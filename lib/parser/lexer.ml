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

(* As the lexer "state" we remember whether we just saw a line comment. *)
module LexerState = struct
  type t = [ `Linecomment | `None ]
end

(* We define the lexer using a basic utf-8 character parser from Fmlib. *)
module Basic = Ucharacter.Make_utf8 (LexerState) (Located_token) (Unit)
open Basic

let backquote = Uchar.of_char '`'
let newline = Uchar.of_char '\n'
let lbrace = Uchar.of_char '{'
let rbrace = Uchar.of_char '}'

(* A line comment starts with a backquote and extends to the end of the line.  *)
let line_comment : Whitespace.t t =
  let* c = uword (fun c -> c = backquote) (fun c -> c <> newline) "line comment" in
  let* () = set `Linecomment in
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
  let* () = set `None in
  rest "" 0 `None

(* This combinator parses not just newlines but also spaces and tabs, but it only counts the number of newlines.  Thus it returns (`Newlines 0) if it parses only spaces and tabs (possibly including the newline at the end of a preceding line comment). *)
let newlines : Whitespace.t t =
  let* n =
    one_or_more_fold_left
      (fun c -> return (if c = '\n' then 1 else 0))
      (fun n c -> return (if c = '\n' then n + 1 else n))
      (one_of_chars " \t\n\r" "space, tab, or newline") in
  let* line = get in
  let* () = set `None in
  (* If we just saw a line comment, then we don't include the newline that *ended* the line comment as a "newline". *)
  return (`Newlines (if line = `Linecomment then n - 1 else n))

(* Whitespace.t consists of spaces, tabs, newlines, and comments.  We only record newlines when there are a positive number of them. *)
let whitespace : Whitespace.t list t =
  let* () = set `None in
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

module Specials = struct
  (* Any of these characters is always its own token. *)
  let default_onechar_ops =
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

  (* Any sequence consisting entirely of these characters is its own token. *)
  let default_ascii_symbols =
    [|
      '~'; '!'; '@'; '#'; '$'; '%'; '&'; '*'; '/'; '='; '+'; '\\'; '|'; ','; '<'; '>'; ':'; ';'; '-';
    |]

  module Data = struct
    type t = {
      onechar_ops : (int * Token.t) Array.t;
      ascii_symbols : char Array.t;
      digit_vars : bool;
    }
  end

  module R = Algaeff.Reader.Make (Data)

  let () = R.register_printer (function `Read -> Some "unhandled Lexer.Specials read effect")

  let run ?(onechar_ops = Array.of_list []) ?(ascii_symbols = Array.of_list []) ?(digit_vars = true)
      f =
    let onechar_ops = Array.append default_onechar_ops onechar_ops in
    let ascii_symbols = Array.append default_ascii_symbols ascii_symbols in
    R.run ~env:{ onechar_ops; ascii_symbols; digit_vars } f

  let onechar_ops () = (R.read ()).onechar_ops
  let ascii_symbols () = (R.read ()).ascii_symbols
  let digit_vars () = (R.read ()).digit_vars
end

let onechar_uchars () = Array.map (fun c -> Uchar.of_int (fst c)) (Specials.onechar_ops ())
let onechar_tokens () = Array.map snd (Specials.onechar_ops ())

let onechar_op : Token.t t =
  let* c = ucharp (fun c -> Array.mem c (onechar_uchars ())) "one-character operator" in
  let i = Option.get (Array.find_index (fun x -> x = c) (onechar_uchars ())) in
  return (onechar_tokens ()).(i)

let ascii_symbol_uchars () = Array.map Uchar.of_char (Specials.ascii_symbols ())
let is_ascii_symbol c = Array.mem c (Specials.ascii_symbols ())

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
let specials () =
  Array.concat
    [
      ascii_symbol_uchars ();
      onechar_uchars ();
      (* Carets are not allowed to mean anything except a superscript.  We also have to stop when we meet a line comment started by a backquote.  We don't have to worry about block comments, since their opening brace is a onechar op and hence also stops an identifier. *)
      Array.map Uchar.of_char [| '^'; ' '; '\t'; '\n'; '\r'; '`' |];
      (* We only include the superscript parentheses: other superscript characters without parentheses are allowed in identifiers. *)
      [| Token.super_lparen_uchar; Token.super_rparen_uchar |];
    ]

let other_char : string t =
  let* c = ucharp (fun x -> not (Array.mem x (specials ()))) "alphanumeric or unicode" in
  return (Utf8.Encoder.to_internal c)

let is_numeral =
  List.for_all (fun s -> String.for_all (fun c -> String.exists (fun x -> x = c) "0123456789") s)

(* Once we have an identifier string, we inspect it and divide into cases to make a Token.t.  We take a range so that we can immediately report invalid field, constructor, and numeral names with a position. *)
let canonicalize (rng : Position.range) : string -> Token.t t = function
  | "let" -> return Let
  | "rec" -> return Rec
  | "in" -> return In
  | "axiom" -> return Axiom
  | "def" -> return Def
  | "and" -> return And
  | "echo" -> return Echo
  | "synth" -> return Synth
  | "quit" -> return Quit
  | "match" -> return Match
  | "return" -> return Return
  | "sig" -> return Sig
  | "data" -> return Data
  | "codata" -> return Codata
  | "notation" -> return Notation
  | "import" -> return Import
  | "export" -> return Export
  | "solve" -> return Solve
  | "show" -> return Show
  | "display" -> return Display
  | "option" -> return Option
  | "undo" -> return Undo
  | "section" -> return Section
  | "end" -> return End
  | "." -> return Dot
  | "..." -> return Ellipsis
  | "_" -> return Underscore
  | s -> (
      let parts = String.split_on_char '.' s in
      let bwdparts = Bwd.of_list parts in
      (* Only allow names starting with digits if the flag says so *)
      if
        (not (Specials.digit_vars ()))
        && (not (is_numeral parts))
        && List.exists
             (fun s -> String.length s > 0 && String.exists (fun x -> x = s.[0]) "0123456789")
             parts
      then fatal Parse_error
      else
        match (parts, bwdparts) with
        | [], _ -> fatal (Anomaly "canonicalizing empty string")
        (* Can't both start and end with a . *)
        | "" :: _, Snoc (_, "") -> fatal ~loc:(Range.convert rng) Parse_error
        (* Starting with a . makes a field.  If there is only a primary name, it's a lower field. *)
        | [ ""; field ], _ -> return (Field (field, []))
        (* Otherwise, if the primary field name is followed by a "..", then the remaining sections are the parts. *)
        | "" :: field :: "" :: pbij, _ -> return (Field (field, pbij))
        (* Otherwise, there is only one remaining section allowed, and it is split into characters to make the remaining sections. *)
        | [ ""; field; pbij ], _ ->
            return (Field (field, String.fold_right (fun c s -> String.make 1 c :: s) pbij []))
        | "" :: _ :: _ :: _ :: _, _ -> fatal ~loc:(Range.convert rng) Parse_error
        (* Ending with a . (and containing no internal .s) makes a constr *)
        | _, Snoc (Snoc (Emp, constr), "") -> return (Constr constr)
        | _, Snoc (_, "") ->
            fatal ~loc:(Range.convert rng) (Unimplemented ("higher constructors: " ^ s))
        (* Otherwise, all the parts must be identifiers. *)
        | parts, _ when List.for_all ok_ident parts -> return (Ident parts)
        | _, _ -> fatal ~loc:(Range.convert rng) Parse_error)

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
  let start : t = make_partial Position.start `None bof
  let restart (lex : t) : t = make_partial (position lex) `None token |> transfer_lookahead lex
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
