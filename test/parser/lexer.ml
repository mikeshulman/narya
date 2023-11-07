open Testutil
open Lex

let () = assert (lex "a b c" = [ Name "a"; Name "b"; Name "c" ])
let () = assert (lex "A->C" = [ Name "A"; Arrow; Name "C" ])
let () = assert (lex "A→C" = [ Name "A"; Arrow; Name "C" ])

let () =
  assert (lex "(A\u{21A6}C0) .d" = [ LParen; Name "A"; Mapsto; Name "C0"; RParen; Field "d" ])

let () =
  assert (
    lex "th(ns24$#*430-}aqo0[eouOEU){OE)(@@!()#"
    = [
        Name "th";
        LParen;
        Name "ns24";
        Op "$#*";
        Numeral (Q.of_float 430.);
        Op "-";
        RBrace;
        Name "aqo0";
        LBracket;
        Name "eouOEU";
        RParen;
        LBrace;
        Name "OE";
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
    = [ Name "this"; Name "is"; Name "starting"; Name "another"; String "line" ])

let () =
  assert (
    lex
      "this is {` a block \n comment spanning \n multiple lines `} ` with a line comment\n and_more-code"
    = [ Name "this"; Name "is"; Name "and_more"; Op "-"; Name "code" ])

let () = assert (nolex "No \t tabs allowed" = [ ("tab character", None) ])

let () =
  assert (
    lex "block comments {` can contain ` line comments \n and {` nest `} arbitrarily `} \n see?"
    = [ Name "block"; Name "comments"; Name "see"; Op "?" ])

let () =
  assert (
    lex "block ` comments {` don't start in \n line comments"
    = [ Name "block"; Name "line"; Name "comments" ])

let () =
  assert (
    lex "block \"comments {` don't start in\" strings"
    = [ Name "block"; String "comments {` don't start in"; Name "strings" ])

let () =
  assert (
    nolex "{` no block comments `} starting lines"
    = [ ("token on line starting with a block comment", None); ("end of input", None) ])

let () = assert (lex "  initial space" = [ Name "initial"; Name "space" ])

let () =
  assert (
    nolex "No {` block comments \n starting lines `} with code"
    = [ ("token on line starting with a block comment", None); ("end of input", None) ])

let () = assert (lex "Block comments {` can end the file `}" = [ Name "Block"; Name "comments" ])
let () = assert (nolex "Unterminated {` block comment" = [ ("any character", None) ])

let () =
  assert (
    lex "let x := a in b : coo"
    = [ Let; Name "x"; Coloneq; Name "a"; In; Name "b"; Colon; Name "coo" ])
