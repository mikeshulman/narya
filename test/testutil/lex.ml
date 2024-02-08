open Fmlib_parse
open Parser

(* To test the lexer, we hook it up with a trivial parser that just produces a list of tokens. *)

module Token_list = struct
  type t = Lexer.Token_whitespace.t list
end

module Parse_tokens = struct
  module Basic = Token_parser.Make (Unit) (Lexer.Token_whitespace) (Token_list) (Unit)
  open Basic

  let token : Lexer.Token_whitespace.t t = step "token" (fun state _ tok -> Some (tok, state))

  module Parser = struct
    include Basic.Parser

    let start : t = make () (zero_or_more token)
  end
end

module Lex_and_parse =
  Parse_with_lexer.Make_utf8 (Unit) (Lexer.Token_whitespace) (Token_list) (Unit) (Lexer.Parser)
    (Parse_tokens.Parser)

open Lex_and_parse

let start : Lex_and_parse.t = make Lexer.Parser.start Parse_tokens.Parser.start
let trylex str = run_on_string str start

let lex str =
  let p = trylex str in
  if has_succeeded p then List.tl (final p) else raise (Failure ("Lexing failed of " ^ str))

let nolex str =
  let p = trylex str in
  if has_failed_syntax p then failed_expectations p
  else raise (Failure ("Lexing succeeded of " ^ str))

let lexbof str =
  let p = trylex str in
  if has_succeeded p then final p else raise (Failure ("Lexing failed of " ^ str))
