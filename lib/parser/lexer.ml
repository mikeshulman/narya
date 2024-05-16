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

(* We define the lexer using a basic utf-8 character parser from Fmlib. *)
module Basic = Ucharacter.Make_utf8 (Bool) (Located_token) (Unit)
open Basic

let backquote = Uchar.of_char '`'
let newline = Uchar.of_char '\n'
let lbrace = Uchar.of_char '{'
let rbrace = Uchar.of_char '}'

(* A line comment starts with a backquote and extends to the end of the line.  *)
let line_comment : Whitespace.t t =
  let* c = uword (fun c -> c = backquote) (fun c -> c <> newline) "line comment" in
  let* () = set true in
  return (`Line (String.sub c 1 (String.length c - 1)))

(* A block comment starts with {` and ends with `}, and can be nested.  *)
let block_comment : Whitespace.t t =
  let state_of c = if c = lbrace then `LBrace else if c = backquote then `Backquote else `None in
  let rec rest buf nesting prev =
    let* c = ucharp (fun _ -> true) "any character" in
    match prev with
    | `LBrace when c = backquote -> rest (buf ^ "`") (nesting + 1) `None
    | `Backquote when c = rbrace ->
        if nesting <= 0 then return (`Block buf) else rest (buf ^ "`}") (nesting - 1) `None
    | `Backquote when c = backquote -> rest (buf ^ "`") nesting `Backquote
    | `Backquote -> rest (buf ^ "`" ^ Utf8.Encoder.to_internal c) nesting (state_of c)
    | _ when c = backquote -> rest buf nesting `Backquote
    | _ -> rest (buf ^ Utf8.Encoder.to_internal c) nesting (state_of c) in
  let* _ = backtrack (string "{`") "\"{`\"" in
  let* () = set false in
  rest "" 0 `None

let newlines : Whitespace.t t =
  let* n =
    one_or_more_fold_left
      (fun c -> return (if c = '\n' then 1 else 0))
      (fun n c -> return (if c = '\n' then n + 1 else n))
      (one_of_chars " \t\n\r" "space, tab, or newline") in
  let* line = get in
  let* () = set false in
  return (`Newlines (if line then n - 1 else n))

(* Whitespace.T consists of spaces, tabs, newlines, and comments. *)
let whitespace : Whitespace.t list t =
  let* () = set false in
  let* ws =
    zero_or_more_fold_left Emp
      (fun ws w -> if w = `Newlines 0 then return ws else return (Snoc (ws, w)))
      (line_comment </> block_comment </> newlines)
    |> no_expectations in
  return (Bwd.to_list ws)

(* A quoted string starts and ends with double-quotes, and allows backslash-quoted double-quotes and backslashes inside. *)
let quoted_string : Token.t t =
  let* _ = char '"' in
  let rec rest state str =
    let* c = ucharp (fun _ -> true) "any character" in
    match (state, Utf8.Encoder.to_internal c) with
    | `None, "\"" | `Backquote, "\"" -> return (String str)
    | `None, "\\" | `Backquote, "\\" -> rest `Quoted str
    | _, "`" -> rest `Backquote (str ^ "`")
    | `Backquote, "}" ->
        emit Comment_end_in_string;
        rest `None (str ^ "}")
    | _, c -> rest `None (str ^ c) in
  rest `None ""

(* Any of these characters is always its own token. *)
let onechar_ops =
  [|
    (0x28, LParen);
    (0x29, RParen);
    (0x5B, LBracket);
    (0x5D, RBracket);
    (0x7B, LBrace);
    (0x7D, RBrace);
    (0x3F, Query);
    (0x21A6, Mapsto);
    (0x2907, DblMapsto);
    (0x2192, Arrow);
    (0x2254, Coloneq);
    (0x2A74, DblColoneq);
    (0x2A72, Pluseq);
    (0x2026, Ellipsis);
  |]

let onechar_uchars = Array.map (fun c -> Uchar.of_int (fst c)) onechar_ops
let onechar_tokens = Array.map snd onechar_ops

let onechar_op : Token.t t =
  let* c = ucharp (fun c -> Array.mem c onechar_uchars) "one-character operator" in
  let i = Option.get (Array.find_index (fun x -> x = c) onechar_uchars) in
  return onechar_tokens.(i)

(* Any sequence consisting entirely of these characters is its own token. *)
let ascii_symbols =
  [|
    '~'; '!'; '@'; '#'; '$'; '%'; '&'; '*'; '/'; '='; '+'; '\\'; '|'; ','; '<'; '>'; ':'; ';'; '-';
  |]

let ascii_symbol_uchars = Array.map Uchar.of_char ascii_symbols
let is_ascii_symbol c = Array.mem c ascii_symbols

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

(* A Unicode superscript is a string of Unicode superscript numbers and letters between superscript parentheses.  We don't ever want to fail lexing, so any string starting with a superscript left parenthesis that *doesn't* look like this, or a superscript right parenthesis occurring before a superscript left parenthesis, is lexed as an "invalid superscript". *)
let utf8_superscript =
  (let* _ = uchar Token.super_lparen_uchar in
   (let* s =
      uword
        (fun c -> Array.mem c Token.super_uchars)
        (fun c -> Array.mem c Token.super_uchars)
        "utf-8 superscript" in
    (let* _ = uchar Token.super_rparen_uchar in
     return (Superscript (Token.of_super s)))
    </> return (Invalid_superscript (Token.of_super s)))
   </> (let* _ = uchar Token.super_rparen_uchar in
        return (Invalid_superscript ""))
   </> return (Invalid_superscript ""))
  </> let* _ = uchar Token.super_rparen_uchar in
      return (Invalid_superscript "")

(* An ASCII superscript is a caret followed (without any space) by a string of numbers and letters between parentheses.  We don't ever want to fail lexing, so any string starting with a caret that doesn't look like this is lexed as an "invalid superscript". *)
let caret_superscript =
  let* _ = char '^' in
  (let* _ = char '(' in
   (let* s =
      word
        (fun x -> Array.mem x Token.unsupers)
        (fun x -> Array.mem x Token.unsupers)
        "caret superscript" in
    (let* _ = char ')' in
     return (Superscript s))
    </> return (Invalid_superscript s))
   </> return (Invalid_superscript ""))
  </> return (Invalid_superscript "")

let superscript = utf8_superscript </> caret_superscript

(* For other identifiers, we consume (utf-8) characters until we reach whitespace or a special symbol.  Here's the set of specials. *)
let specials =
  Array.concat
    [
      ascii_symbol_uchars;
      onechar_uchars;
      (* Carets are not allowed to mean anything except a superscript. *)
      Array.map Uchar.of_char [| '^'; ' '; '\t'; '\n'; '\r' |];
      (* We only include the superscript parentheses: other superscript characters without parentheses are allowed in identifiers. *)
      [| Token.super_lparen_uchar; Token.super_rparen_uchar |];
    ]

let other_char : string t =
  let* c = ucharp (fun x -> not (Array.mem x specials)) "alphanumeric or unicode" in
  return (Utf8.Encoder.to_internal c)

(* Once we have an identifier string, we inspect it and divide into cases to make a Token.t.  We take a range so that we can immediately report invalid field, constructor, and numeral names with a position. *)
let canonicalize (rng : Position.range) : string -> Token.t t = function
  | "let" -> return Let
  | "in" -> return In
  | "axiom" -> return Axiom
  | "def" -> return Def
  | "and" -> return And
  | "echo" -> return Echo
  | "match" -> return Match
  | "sig" -> return Sig
  | "data" -> return Data
  | "codata" -> return Codata
  | "notation" -> return Notation
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

(* An identifier is a list of one or more other characters, canonicalized. *)
let other : Token.t t =
  let* rng, str =
    located (one_or_more_fold_left return (fun str c -> return (str ^ c)) other_char) in
  canonicalize rng str

(* Finally, a token is either a quoted string, a single-character operator, an operator of special ASCII symbols, or something else.  Unlike the built-in 'lexer' function, we include whitespace *after* the token, so that we can save comments occurring after any code. *)
let token : Located_token.t t =
  (let* loc, tok = located (quoted_string </> onechar_op </> ascii_op </> superscript </> other) in
   let* ws = whitespace in
   return (loc, (tok, ws)))
  </> located (expect_end (Eof, []))

(* This means we need a separate combinator to parse any initial whitespace.   *)
let bof : Located_token.t t =
  let* ws = whitespace in
  located (return (Bof, ws))

module Parser = struct
  include Basic.Parser

  (* This is how we make the lexer to plug into the parser. *)
  let start : t = make_partial Position.start false bof
  let restart (lex : t) : t = make_partial (position lex) false token |> transfer_lookahead lex
end

module Single_token = struct
  module Basic = Token_parser.Make (Unit) (Token_whitespace) (Token_whitespace) (Unit)
  open Basic

  let token : Token_whitespace.t t = step "token" (fun state _ tok -> Some (tok, state))

  module Parser = struct
    include Basic.Parser

    let start : t =
      make ()
        ((* bof *)
         let* _ = token in
         token)
  end
end

module Lex_and_parse_single =
  Parse_with_lexer.Make_utf8 (Unit) (Token_whitespace) (Token_whitespace) (Unit) (Parser)
    (Single_token.Parser)

let single str =
  let open Lex_and_parse_single in
  let p = run_on_string str (make Parser.start Single_token.Parser.start) in
  if has_succeeded p then
    let tok, ws = final p in
    if ws = [] then Some tok else None
  else None
