open Testutil
open Lex

let () = assert (lex "a b c" = [ (Ident [ "a" ], []); (Ident [ "b" ], []); (Ident [ "c" ], []) ])
let () = assert (lex "A->C" = [ (Ident [ "A" ], []); (Arrow, []); (Ident [ "C" ], []) ])
let () = assert (lex "A→C" = [ (Ident [ "A" ], []); (Arrow, []); (Ident [ "C" ], []) ])

let () =
  assert (
    lex "(A\u{21A6}C0) .d"
    = [
        (LParen, []);
        (Ident [ "A" ], []);
        (Mapsto, []);
        (Ident [ "C0" ], []);
        (RParen, []);
        (Field ("d", []), []);
      ])

let () =
  assert (
    lex "th(ns24$#*430-}aqo0[eouOEU){OE)(@@!()#"
    = [
        (Ident [ "th" ], []);
        (LParen, []);
        (Ident [ "ns24" ], []);
        (Op "$#*", []);
        (Ident [ "430" ], []);
        (Op "-", []);
        (RBrace, []);
        (Ident [ "aqo0" ], []);
        (LBracket, []);
        (Ident [ "eouOEU" ], []);
        (RParen, []);
        (LBrace, []);
        (Ident [ "OE" ], []);
        (RParen, []);
        (LParen, []);
        (Op "@@!", []);
        (LParen, []);
        (RParen, []);
        (Op "#", []);
      ])

let () =
  assert (
    lex "this is ` a line comment\n  starting another \"line\""
    = [
        (Ident [ "this" ], []);
        (Ident [ "is" ], [ `Line " a line comment" ]);
        (Ident [ "starting" ], []);
        (Ident [ "another" ], []);
        (String "line", []);
      ])

let () =
  assert (
    lex
      "this is {` a block \n comment spanning \n multiple lines `} ` with a line comment\n and_more-code"
    = [
        (Ident [ "this" ], []);
        ( Ident [ "is" ],
          [ `Block " a block \n comment spanning \n multiple lines "; `Line " with a line comment" ]
        );
        (Ident [ "and_more" ], []);
        (Op "-", []);
        (Ident [ "code" ], []);
      ])

let () =
  assert (
    lex "block comments {` can contain ` line comments \n and {` nest `} arbitrarily `} \n see?"
    = [
        (Ident [ "block" ], []);
        ( Ident [ "comments" ],
          [ `Block " can contain ` line comments \n and {` nest `} arbitrarily "; `Newlines 1 ] );
        (Ident [ "see" ], []);
        (Query, []);
      ])

let () =
  assert (
    lex "block comments {` nest `{` even after `} backquotes `} see?"
    = [
        (Ident [ "block" ], []);
        (Ident [ "comments" ], [ `Block " nest `{` even after `} backquotes " ]);
        (Ident [ "see" ], []);
        (Query, []);
      ])

let () =
  assert (
    lex "block comments {`} can start with a lbrace `} see?"
    = [
        (Ident [ "block" ], []);
        (Ident [ "comments" ], [ `Block "} can start with a lbrace " ]);
        (Ident [ "see" ], []);
        (Query, []);
      ])

let () =
  assert (
    lex "block ` comments {` don't start in \n line comments"
    = [
        (Ident [ "block" ], [ `Line " comments {` don't start in " ]);
        (Ident [ "line" ], []);
        (Ident [ "comments" ], []);
      ])

let () =
  assert (
    lex "block \"comments {` don't start in\" strings"
    = [
        (Ident [ "block" ], []); (String "comments {` don't start in", []); (Ident [ "strings" ], []);
      ])

let () =
  assert (
    lex "block {` comment `{{` nested ``} done `} over"
    = [ (Ident [ "block" ], [ `Block " comment `{{` nested ``} done " ]); (Ident [ "over" ], []) ])

let () = assert (lex "  initial space" = [ (Ident [ "initial" ], []); (Ident [ "space" ], []) ])

let () =
  assert (
    lex "Block comments {` can end the file `}"
    = [ (Ident [ "Block" ], []); (Ident [ "comments" ], [ `Block " can end the file " ]) ])

let () = assert (nolex "Unterminated {` block comment" = [ ("any character", None) ])

let () =
  assert (
    lex "let x := a in b : coo"
    = [
        (Let, []);
        (Ident [ "x" ], []);
        (Coloneq, []);
        (Ident [ "a" ], []);
        (In, []);
        (Ident [ "b" ], []);
        (Colon, []);
        (Ident [ "coo" ], []);
      ])

let () = assert (lex "" = [])
let () = assert (lexbof "" = [ (Bof, []) ])
let () = assert (lexbof " " = [ (Bof, []) ])
let () = assert (lexbof "\n" = [ (Bof, [ `Newlines 1 ]) ])
let () = assert (lexbof "` line comment\n" = [ (Bof, [ `Line " line comment" ]) ])
let () = assert (lexbof "` line comment" = [ (Bof, [ `Line " line comment" ]) ])
let () = assert (lex "x^(1-2)" = [ (Ident [ "x" ], []); (Superscript "1-2", []) ])

let () =
  assert (
    lex "(x^(1-2))" = [ (LParen, []); (Ident [ "x" ], []); (Superscript "1-2", []); (RParen, []) ])

let () = assert (lex "x⁽¹⁻²⁾" = [ (Ident [ "x" ], []); (Superscript "1-2", []) ])

let () =
  assert (lex "x⁽¹⁾⁽²⁾" = [ (Ident [ "x" ], []); (Superscript "1", []); (Superscript "2", []) ])
