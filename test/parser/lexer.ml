open Testutil
open Lex

let () = assert (lex "a b c" = [ Ident [ "a" ]; Ident [ "b" ]; Ident [ "c" ] ])
let () = assert (lex "A->C" = [ Ident [ "A" ]; Arrow; Ident [ "C" ] ])
let () = assert (lex "A→C" = [ Ident [ "A" ]; Arrow; Ident [ "C" ] ])

let () =
  assert (
    lex "(A\u{21A6}C0) .d" = [ LParen; Ident [ "A" ]; Mapsto; Ident [ "C0" ]; RParen; Field "d" ])

let () =
  assert (
    lex "th(ns24$#*430-}aqo0[eouOEU){OE)(@@!()#"
    = [
        Ident [ "th" ];
        LParen;
        Ident [ "ns24" ];
        Op "$#*";
        Ident [ "430" ];
        Op "-";
        RBrace;
        Ident [ "aqo0" ];
        LBracket;
        Ident [ "eouOEU" ];
        RParen;
        LBrace;
        Ident [ "OE" ];
        RParen;
        LParen;
        Op "@@!";
        LParen;
        RParen;
        Op "#";
      ])

let () =
  assert (
    lex "this is ` a line comment\n  starting another \"line\""
    = [ Ident [ "this" ]; Ident [ "is" ]; Ident [ "starting" ]; Ident [ "another" ]; String "line" ])

let () =
  assert (
    lex
      "this is {` a block \n comment spanning \n multiple lines `} ` with a line comment\n and_more-code"
    = [ Ident [ "this" ]; Ident [ "is" ]; Ident [ "and_more" ]; Op "-"; Ident [ "code" ] ])

let () =
  assert (
    lex "block comments {` can contain ` line comments \n and {` nest `} arbitrarily `} \n see?"
    = [ Ident [ "block" ]; Ident [ "comments" ]; Ident [ "see" ]; Op "?" ])

let () =
  assert (
    lex "block comments {` nest `{` even after `} backquotes `} see?"
    = [ Ident [ "block" ]; Ident [ "comments" ]; Ident [ "see" ]; Op "?" ])

let () =
  assert (
    lex "block comments {`} can start with a lbrace `} see?"
    = [ Ident [ "block" ]; Ident [ "comments" ]; Ident [ "see" ]; Op "?" ])

let () =
  assert (
    lex "block ` comments {` don't start in \n line comments"
    = [ Ident [ "block" ]; Ident [ "line" ]; Ident [ "comments" ] ])

let () =
  assert (
    lex "block \"comments {` don't start in\" strings"
    = [ Ident [ "block" ]; String "comments {` don't start in"; Ident [ "strings" ] ])

let () = assert (lex "  initial space" = [ Ident [ "initial" ]; Ident [ "space" ] ])

let () =
  assert (lex "Block comments {` can end the file `}" = [ Ident [ "Block" ]; Ident [ "comments" ] ])

let () = assert (nolex "Unterminated {` block comment" = [ ("any character", None) ])

let () =
  assert (
    lex "let x := a in b : coo"
    = [ Let; Ident [ "x" ]; Coloneq; Ident [ "a" ]; In; Ident [ "b" ]; Colon; Ident [ "coo" ] ])
