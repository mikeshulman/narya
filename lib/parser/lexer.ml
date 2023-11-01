open Fmlib_parse
open Token
open Core
open Reporter

(* NB: The parsing combinator "string" just parses the characters in the string one by one.  This means that if it succeeds to parse the first character in the string, it consumes that character, and if it fails later in the string then parsing dies completely.  If that's not what you want, which it usually isn't, you need to wrap it in "backtrack".  *)

(* The Fmlib parsers allow us to track a "state" through the parsing.  We use this to forbid block comments from appearing on a line before any tokens.  State "Indent" means we have seen only 0x20 spaces so far on this line, "Code" means we have seen valid tokens on this line, and "Blankline" means this line had a block comment before any tokens and hence cannot contain any tokens.  *)
module Indent_state = struct
  type t = Indent | Code | Blankline
end

module Located_token = struct
  type t = Position.range * Token.t
end

(* We define the lexer using a basic character parser from Fmlib.  Note that a "character" here really means a byte, so we have to be careful with Unicode. *)
module Basic = Character.Make (Indent_state) (Located_token) (Unit)
open Basic

(* A line comment starts with a backquote and extends to the end of the line.  The next line, of course, starts with an Indent. *)
let line_comment : unit t =
  let* _ = char '`' in
  let* _ = skip_zero_or_more (charp (fun c -> c <> '\n') "non-newline") in
  let* () = set Indent in
  return ()

(* A block comment starts with {` and ends with `}, and can be nested.  If it contains a newline, or it started in the Indent, then the line it ends on must be a blank one. *)
let block_comment : unit t =
  let rec rest nesting state =
    let* c = charp (fun _ -> true) "any character" in
    match (state, c) with
    | `None, '{' | `LBrace, '{' -> rest nesting `LBrace
    | `None, '`' | `Backquote, '`' -> rest nesting `Backquote
    | `Backquote, '}' -> if nesting <= 0 then return () else rest (nesting - 1) `None
    | `LBrace, '`' -> rest (nesting + 1) `None
    | _, '\n' | _, '\r' ->
        let* () = set Blankline in
        rest nesting `None
    | _ -> rest nesting `None in
  let* _ = backtrack (string "{`") "\"{`\"" in
  let* () = rest 0 `None in
  let* s = get in
  if s = Indent then set Blankline else return ()

let space : unit t =
  let* _ = char ' ' in
  return ()

let tab : unit t =
  let* _ = char '\t' in
  unexpected "tab character"

(* A new line starts in the Indent. *)
let newline : unit t =
  let* _ = char '\n' </> char '\r' in
  let* () = set Indent in
  return ()

(* Whitespace consists of spaces, newlines, and comments.  In particular, tab characters are forbidden. *)
let whitespace : int t =
  let* _ =
    zero_or_more (space </> tab </> newline </> line_comment </> block_comment) |> no_expectations
  in
  return 0

(* A quoted string starts and ends with double-quotes, and allows backslash-quoted double-quotes and backslashes inside. *)
let quoted_string : Token.t t =
  let* _ = char '"' in
  let buf = Buffer.create 10 in
  let rec rest state =
    let* c = charp (fun _ -> true) "any character" in
    match (state, c) with
    | `None, '"' -> return (Token.String (Buffer.contents buf))
    | `None, '\\' -> rest `Quoted
    | `None, _ | `Quoted, _ ->
        Buffer.add_char buf c;
        rest `None in
  rest `None

(* Any of these characters is always its own token.  Note that we can't treat these as "characters" for the character parser because some of them are multibyte code points. *)
let onechar_op : Token.t t =
  (let* _ = char '(' in
   return LParen)
  </> (let* _ = char ')' in
       return RParen)
  </> (let* _ = char '[' in
       return LBracket)
  </> (let* _ = char ']' in
       return RBracket)
  </> (let* _ = char '{' in
       return LBrace)
  </> (let* _ = char '}' in
       return RBrace)
  </> (let* _ = backtrack (string "\u{21A6}") "\"\u{21A6}\"" in
       return Mapsto)
  </> (let* _ = backtrack (string "\u{2192}") "\"\u{2192}\"" in
       return Arrow)
  </> (let* _ = backtrack (string "\u{2254}") "\"\u{2254}\"" in
       return Coloneq)
  <?> "one-character operator"

(* Any sequence consisting entirely of these characters is its own token. *)
let ascii_symbols = "~!@#$%^&*/?=+\\|,<>:;-"
let is_ascii_symbol c = String.exists (fun x -> x = c) ascii_symbols

let ascii_op : Token.t t =
  let* op = word is_ascii_symbol is_ascii_symbol "ASCII symbol" in
  match op with
  | "->" -> return Arrow
  | "|->" -> return Mapsto
  | ":=" -> return Coloneq
  | ":" -> return Colon
  | _ -> return (Op op)

(* A numeral is a string composed entirely of digits and periods (and not starting or ending with a period, but that's taken care of later in "canonicalize".  Of course if there is more than one period it's not a *valid* numeral, but we don't allow it as another kind of token either. *)
let digits_dot = "0123456789."
let is_digit_or_dot c = String.exists (fun x -> x = c) digits_dot
let is_numeral s = String.for_all is_digit_or_dot s

(* To detect the characters allowed in a general identifier, we can easily exclude the special ascii symbols, along with parentheses, braces, and whitespace (including tabs). *)
let special_ascii = "()[]{} \t\n\r" ^ ascii_symbols

(* But to exclude the special unicode characters, since they are multibyte we require lookahead.  We note that each of our three special Unicode characters begins with the same byte. *)
let arrow = "\u{2192}"
let lead_char = arrow.[0]
let arrow_rest = String.sub arrow 1 (String.length arrow - 1)
let mapsto = "\u{21A6}"
let () = assert (mapsto.[0] = lead_char)
let mapsto_rest = String.sub mapsto 1 (String.length mapsto - 1)
let coloneq = "\u{2254}"
let () = assert (coloneq.[0] = lead_char)
let coloneq_rest = String.sub coloneq 1 (String.length coloneq - 1)

let other_char : char t =
  (* We need a backtrack here, so that we don't consume the first byte of the special Unicode characters if their appearance is what ends our identifier. *)
  backtrack
    (let* c =
       charp (fun x -> not (String.exists (fun y -> y = x) special_ascii)) "alphanumeric or unicode"
     in
     if c = lead_char then
       let* () = not_followed_by (string arrow_rest) "not a \"\u{2192}\"" in
       let* () = not_followed_by (string mapsto_rest) "not a \"\u{21A6}\"" in
       let* () = not_followed_by (string coloneq_rest) "not a \"\u{2254}\"" in
       return c
     else return c)
    "other character"

(* Once we have an identifier string, we inspect it and divide into cases to make a Token.t.  We take a range so that we can immediately report invalid field, constructor, and numeral names with a position. *)
let canonicalize (rng : Position.range) : string -> Token.t t = function
  | "let" -> return Let
  | "in" -> return In
  | "def" -> return Def
  | "record" -> return Record
  | "data" -> return Data
  | "codata" -> return Codata
  | "section" -> return Section
  | "." -> return Dot
  | "_" -> return Underscore
  | s -> (
      let len = String.length s in
      match (s.[0], s.[len - 1]) with
      | '.', '.' -> fatal ~loc:(Range.convert rng) Parse_error
      | '.', _ ->
          let name = String.sub s 1 (len - 1) in
          (* We allow as a "field name" anything starting with a period and not containing any other periods. *)
          if Token.variableable name then return (Field name)
          else fatal ~loc:(Range.convert rng) (Invalid_field name)
      | _, '.' ->
          let name = String.sub s 0 (len - 1) in
          (* We allow as a "constructor name" anything ending with a period and not containing any other periods. *)
          if Token.variableable name then return (Constr name)
          else fatal ~loc:(Range.convert rng) (Invalid_constr name)
      | '_', _ | _, '_' -> return (Internal s)
      | _ ->
          if is_numeral s then
            match int_of_string_opt s with
            | Some n -> return (Numeral n)
            | None -> fatal ~loc:(Range.convert rng) (Invalid_numeral s)
            (* Anything else, not starting or ending with a period, and that doesn't consist entirely of digits and periods, is potentially a valid name.  The periods will be interpreted later as namespacing of constants (hence are disallowed in a local variable). *)
          else return (Name s))

(* Now to make a token, we consume as many such characters as possible, adding them one-by-one to a Buffer and then canonicalizing the resulting string. *)
let other : Token.t t =
  let* rng, buf =
    located
      (one_or_more_fold_left
         (fun c ->
           let buf = Buffer.create 16 in
           Buffer.add_char buf c;
           return buf)
         (fun buf c ->
           Buffer.add_char buf c;
           return buf)
         other_char) in
  canonicalize rng (Buffer.contents buf)

(* Finally, a token cannot appear on a blank-only line, and is either a quoted string, a single-character operator, an operator of special ASCII symbols, or something else.  We remove whitespace first (which updates the state!). *)
let token : Located_token.t t =
  lexer whitespace Eof
    (let* s = get in
     match s with
     | Blankline -> unexpected "token on line starting with a block comment"
     | Code | Indent ->
         let* tok = quoted_string </> onechar_op </> ascii_op </> other in
         let* () = set Code in
         return tok)

module Parser = struct
  include Basic.Parser

  (* This is how we make the lexer to plug into the parser. *)
  let init : t = make_partial Indent token
  let restart (lex : t) : t = restart_partial token lex

  (* But occasionally we may also just want to parse a specific string into a single token. *)
  let single (str : string) : Token.t option =
    let p =
      run_on_string str (make Code (located (quoted_string </> onechar_op </> ascii_op </> other)))
    in
    if has_succeeded p then Some (snd (final p)) else None
end
