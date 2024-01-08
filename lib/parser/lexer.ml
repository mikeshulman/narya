open Bwd
open Fmlib_parse
open Token
open Core
open Reporter

(* NB: The parsing combinator "string" just parses the characters in the string one by one.  This means that if it succeeds to parse the first character in the string, it consumes that character, and if it fails later in the string then parsing dies completely.  If that's not what you want, which it usually isn't, you need to wrap it in "backtrack".  *)

module Token_whitespace = struct
  type t = Token.t * Whitespace.t list
end

module Located_token = struct
  type t = Position.range * Token_whitespace.t
end

(* We define the lexer using a basic character parser from Fmlib.  Note that a "character" here really means a byte, so we have to be careful with Unicode. *)
module Basic = Character.Make (Unit) (Located_token) (Unit)
open Basic

(* A line comment starts with a backquote and extends to the end of the line.  *)
let line_comment : Whitespace.t t =
  let* c = word (fun c -> c = '`') (fun c -> c <> '\n') "line comment" in
  let* _ = char '\n' in
  return (`Line (String.sub c 1 (String.length c - 1)))

(* A block comment starts with {` and ends with `}, and can be nested.  *)
let block_comment : Whitespace.t t =
  let state_of = function
    | '{' -> `LBrace
    | '`' -> `Backquote
    | _ -> `None in
  let rec rest buf nesting prev =
    let* c = charp (fun _ -> true) "any character" in
    match (prev, c) with
    | `LBrace, '`' -> rest (buf ^ "`") (nesting + 1) `None
    | `Backquote, '}' ->
        if nesting <= 0 then return (`Block buf) else rest (buf ^ "`}") (nesting - 1) `None
    | `Backquote, '`' -> rest (buf ^ "`") nesting `Backquote
    | `Backquote, _ -> rest (buf ^ "`" ^ String.make 1 c) nesting (state_of c)
    | _, '`' -> rest buf nesting `Backquote
    | _ -> rest (buf ^ String.make 1 c) nesting (state_of c) in
  let* _ = backtrack (string "{`") "\"{`\"" in
  rest "" 0 `None

let newlines : Whitespace.t t =
  let* n =
    one_or_more_fold_left
      (fun c -> return (if c = '\n' then 1 else 0))
      (fun n c -> return (if c = '\n' then n + 1 else n))
      (one_of_chars " \t\n\r" "space, tab, or newline") in
  return (`Newlines n)

(* Whitespace.T consists of spaces, tabs, newlines, and comments. *)
let whitespace : Whitespace.t list t =
  let* ws =
    zero_or_more_fold_left Emp
      (fun ws w -> if w = `Newlines 0 then return ws else return (Snoc (ws, w)))
      (line_comment </> block_comment </> newlines)
    |> no_expectations in
  return (Bwd.to_list ws)

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
  </> (let* _ = backtrack (string "\u{2907}") "\"\u{2907}\"" in
       return DblMapsto)
  </> (let* _ = backtrack (string "\u{2192}") "\"\u{2192}\"" in
       return Arrow)
  </> (let* _ = backtrack (string "\u{2254}") "\"\u{2254}\"" in
       return Coloneq)
  </> (let* _ = backtrack (string "\u{2A74}") "\"\u{2A74}\"" in
       return DblColoneq)
  </> (let* _ = backtrack (string "\u{2A72}") "\"\u{2A72}\"" in
       return Pluseq)
  </> (let* _ = backtrack (string "\u{2026}") "\"\u{2026}\"" in
       return Ellipsis)
  <?> "one-character operator"

(* Any sequence consisting entirely of these characters is its own token. *)
let ascii_symbols = "~!@#$%^&*/?=+\\|,<>:;-"
let is_ascii_symbol c = String.exists (fun x -> x = c) ascii_symbols

let ascii_op : Token.t t =
  let* op = word is_ascii_symbol is_ascii_symbol "ASCII symbol" in
  match op with
  | "->" -> return Arrow
  | "|->" -> return Mapsto
  | "|=>" -> return DblMapsto
  | ":=" -> return Coloneq
  | "::=" -> return DblColoneq
  | "+=" -> return Pluseq
  | ":" -> return Colon
  | "..." -> return Ellipsis
  | _ -> return (Op op)

(* A numeral is a string composed entirely of digits and periods (and not starting or ending with a period, but that's taken care of later in "canonicalize".  Of course if there is more than one period it's not a *valid* numeral, but we don't allow it as another kind of token either. *)
let digits_dot = "0123456789."
let is_digit_or_dot c = String.exists (fun x -> x = c) digits_dot
let is_numeral s = String.for_all is_digit_or_dot s

(* To detect the characters allowed in a general identifier, we can easily exclude the special ascii symbols, along with parentheses, braces, and Whitespace.t (including tabs). *)
let special_ascii = "()[]{} \t\n\r" ^ ascii_symbols

(* But to exclude the special unicode characters, since they are multibyte we require lookahead.  We note that each of our special Unicode characters → ↦ ≔ ⩴ ⤇ ⩲ … begins with the same byte 0xE2.*)
let lead_char = "\u{2192}".[0]

let not_special chr =
  assert (chr.[0] = lead_char);
  let rest = String.sub chr 1 (String.length chr - 1) in
  not_followed_by (string rest) ("not a \"" ^ chr ^ "\"")

let not_arrow = not_special "\u{2192}"
let not_mapsto = not_special "\u{21A6}"
let not_dblmapsto = not_special "\u{2907}"
let not_coloneq = not_special "\u{2254}"
let not_dblcoloneq = not_special "\u{2A74}"
let not_pluseq = not_special "\u{2A72}"
let not_ellipsis = not_special "\u{2026}"

let other_char : char t =
  (* We need a backtrack here, so that we don't consume the first byte of the special Unicode characters if their appearance is what ends our identifier. *)
  backtrack
    (let* c =
       charp (fun x -> not (String.exists (fun y -> y = x) special_ascii)) "alphanumeric or unicode"
     in
     if c = lead_char then
       let* () = not_arrow in
       let* () = not_mapsto in
       let* () = not_dblmapsto in
       let* () = not_coloneq in
       let* () = not_dblcoloneq in
       let* () = not_pluseq in
       let* () = not_ellipsis in
       return c
     else return c)
    "other character"

(* Once we have an identifier string, we inspect it and divide into cases to make a Token.t.  We take a range so that we can immediately report invalid field, constructor, and numeral names with a position. *)
let canonicalize (rng : Position.range) : string -> Token.t t = function
  | "let" -> return Let
  | "in" -> return In
  | "axiom" -> return Axiom
  | "def" -> return Def
  | "echo" -> return Echo
  | "record" -> return Record
  | "data" -> return Data
  | "codata" -> return Codata
  | "section" -> return Section
  | "." -> return Dot
  | "..." -> return Ellipsis
  | "_" -> return Underscore
  | s -> (
      match String.split_on_char '.' s with
      | [] -> fatal (Anomaly "canonicalizing empty string")
      | [ ""; "" ] -> return Dot (* Shouldn't happen, we already tested for dot *)
      | [ ""; field ] -> return (Field field)
      | [ constr; "" ] -> return (Constr constr)
      | parts when List.for_all ok_ident parts -> return (Ident parts)
      | "" :: parts when List.nth parts (List.length parts - 1) = "" ->
          fatal ~loc:(Range.convert rng) Parse_error
      | "" :: _ -> fatal ~loc:(Range.convert rng) (Invalid_field s)
      | parts when List.nth parts (List.length parts - 1) = "" ->
          fatal ~loc:(Range.convert rng) (Invalid_constr s)
      | _ -> fatal ~loc:(Range.convert rng) Parse_error)

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

(* Finally, a token cannot appear on a blank-only line, and is either a quoted string, a single-character operator, an operator of special ASCII symbols, or something else.  Unlike the built-in 'lexer' function, we include Whitespace.t *after* the token, so that we can save comments occurring after any code. *)
let token : Located_token.t t =
  located
    ((let* tok = quoted_string </> onechar_op </> ascii_op </> other in
      let* ws = whitespace in
      return (tok, ws))
    </> expect_end (Eof, []))

(* This means we need a separate combinator to parse any initial Whitespace.t.  We re-use the EOF token as a "BOF" token for this. *)
let wstoken : Located_token.t t =
  let* ws = whitespace in
  located (return (Eof, ws))

module Parser = struct
  include Basic.Parser

  (* This is how we make the lexer to plug into the parser. *)
  let start : t = make_partial Position.start () wstoken
  let restart (lex : t) : t = make_partial (position lex) () token |> transfer_lookahead lex
end
