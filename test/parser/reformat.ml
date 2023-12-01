open Testutil.Print

let test_reformat () =
  (* Application spines, with field projections *)
  set_margin 20;
  reformat "blah blah blah blah blah blah blah blah blah blah blah";
  reformat "constr. arg arg arg arg arg arg";
  reformat "x .fld .fld2 arg .fld3 arg arg arg arg";

  (* Parentheses *)
  reformat "blah (blah blah) (blah (blah blah)) (blah blah blah blah)";
  reformat "blah (blah blah blah blah blah blah blah) blah ((blah blah) blah (blah) blah)";

  (* Abstraction *)
  reformat "x |-> M";
  reformat "x |-> blah blah blah blah blah blah blah blah blah ";
  reformat "x x x x x x x x x x x x x x x x x |-> M";
  reformat "x x x x x x x x x x x x x x x x x |-> blah blah blah blah blah blah blah blah blah ";

  (* Type ascription *)
  reformat "M:A";
  reformat "M : blah blah blah blah blah blah blah blah";
  reformat "blah blah blah blah blah blah blah blah : A";
  reformat "blah blah blah : blah blah blah";
  reformat "blah blah blah blah blah blah blah blah : blah blah blah";
  reformat "blah blah blah : blah blah blah blah blah blah blah";
  reformat "blah blah blah blah blah : blah blah blah blah blah";
  reformat "blah blah blah blah blah blah blah blah : blah blah blah blah blah blah blah blah";

  (* Function-types, including pi-types *)
  reformat "(x:A) -> B";
  set_margin 30;
  reformat "(x:A)(x:A)(x:A)(x:A)(x:A)(x:A)(x:A)(x:A)(x:A)(x:A) -> C";
  reformat "(x:A)(x:A)(x:A)(x:A)(x:A)(x:A)(x:A)(x:A)(x:A) -> C";
  reformat "(x:A) -> blah blah blah blah blah blah blah blah blah blah blah";
  set_margin 70;
  reformat "(x:A)->(x:A)->(x:A)->(x:A)->(x:A)-> C";
  reformat "(x:A)->(x:A)->(x:A)->(x:A)->(x:A)->(x:A)->(x:A)->(x:A) -> C";
  reformat "(x:A)->(x:A)->(x:A)->(x:A)->(x:A)->(x:A)->(x:A)->(x:A)->(x:A)->(x:A)->(x:A) -> C";
  set_margin 30;
  reformat "A -> B";
  reformat "A -> A -> A -> A -> A -> A -> B";
  reformat "A -> A -> A -> A -> A -> A -> A -> B";
  reformat "A -> A -> A -> A -> A -> A -> A -> A -> B";
  reformat "A -> A -> A -> A -> A -> A -> A -> A -> A -> B";
  reformat "A -> A -> A -> A -> A -> A -> A -> A -> A -> A -> B";
  reformat "A -> A -> A -> A -> A -> (x:A) -> A -> B";
  reformat "A -> A -> A -> A -> A -> A -> A -> A -> B";
  reformat "A -> A -> A -> A -> A -> A -> A -> A -> A -> A -> B";
  reformat "(x:A)->A->(x:A)->A->(x:A)-> C";
  reformat "(x:A)(x:A)(x:A)-> A ->(x:A)(_:A)(x:A)(x:A)->(x:A) -> C";
  reformat "A -> A -> A -> blah blah blah blah blah blah blah blah -> A -> A -> B";
  reformat "A -> A -> A -> (x : blah blah blah blah blah blah blah blah) -> A -> A -> B";
  reformat
    "(x:A)(x:A)(x:blah blah blah blah blah blah blah blah)(x:A)(x:A)(x:A)(x:A)(x:A)(x:A) -> C";
  ()

let test_compactness () =
  (* Let-binding *)
  set_margin 20;
  reformat "let x := y in z";
  reformat "let x := y in blah blah blah blah blah blah blah";
  reformat "let x := y in let z := w in u";
  set_margin 30;
  reformat "let x := y in let z := w in u";
  set_margin 20;
  reformat "let x := blah blah blah blah blah in blah blah blah blah blah blah";
  reformat "let x := blah blah blah blah blah in x";
  reformat "let x : w := y in let z : a := w in u";
  reformat
    "let x : boo boo boo boo boo boo boo boo boo := blah blah blah blah blah in blah blah blah blah blah blah";
  reformat "let x : boo boo boo boo boo boo boo boo boo := blah blah blah blah blah in x";
  reformat "let x : boo boo boo boo boo boo boo boo boo := y in blah blah blah blah blah blah";
  reformat "let x : boo boo boo boo boo boo boo boo boo := y in x";
  reformat "let x : a := blah blah blah blah blah in blah blah blah blah blah blah";
  reformat "let x : a := blah blah blah blah blah in x";

  (* Structs *)
  set_margin 30;
  reformat "{fst := M; snd := N}";
  reformat "f {fst := M; snd := N}";
  reformat "{fst := blah blah blah blah blah blah; snd := blah blah blah blah blah blah blah blah}";
  reformat "{fst := blah blah blah blah blah blah; snd := blah}";
  reformat
    "f {fst := blah blah blah blah blah blah; snd := blah blah blah blah blah blah blah blah}";
  reformat "f {fst := blah blah blah blah blah blah; snd := blah}";
  reformat
    "{.fst |-> blah blah blah blah blah blah; .snd |-> blah blah blah blah blah blah blah blah}";
  reformat
    "f {.fst |-> blah blah blah blah blah blah; .snd |-> blah blah blah blah blah blah blah blah}";
  set_margin 40;
  reformat "{fst := M; snd := {foo := N; bar := P}}";
  reformat "f {fst := M; snd := {foo := N; bar := P}}";
  set_margin 80;
  reformat "{.fst |-> {.foo |-> bar ; .baz |-> qux }; .snd |-> { .poo |-> { .bah |-> bum } } }";

  (* Matches *)
  set_margin 30;
  reformat "[x| con. a b |-> blah blah | str. u v |-> bluh bluh ]";
  reformat
    "[x| con. a b |-> blah blah blah blah blah blah blah blah blah blah  | str. u v |-> bluh bluh ]";
  reformat
    "[x| con. a a a a a a a a a a a a a a a a a a a a a a a  |-> blah blah | str. u v |-> bluh bluh ]";
  reformat
    "[x| con. a a a a a a a a a a a a a a a a a a a a a a a  |-> blah blah blah blah blah blah blah blah blah blah blah | str. u v |-> bluh bluh ]";
  reformat "[ con. a b |-> blah blah | str. u v |-> bluh bluh ]";
  reformat
    "[x| con. a b |-> [ y | foo. |-> ba ba baa ba baa baba ba ba baaba babba ba | bar. u v w z w |-> z ] | str. u v |-> bluh bluh ]";
  reformat
    "[x| con. a b |-> { foo := ba ba baa ba baa baba ba ba baaba babba ba ; bar := z } | str. u v |-> { .flab |-> boo boo; .flub |-> zoo zo zoo zo zzo zo } ]";
  reformat
    "[ con. a b |-> [ foo. x |-> ba ba ba | bar. y z |-> y ] | str. u v |-> [ baz. |-> bluh bluh ] ]";
  reformat "([x| poo. |-> bah])";
  reformat "([x| poo. |-> (bah boo)])";
  reformat "([x| poo. |-> bah (boo boo)])";
  ()

let () =
  run @@ fun () ->
  Parser.Print.pp_as_case Compact @@ fun () ->
  test_reformat ();
  Printf.printf "--------------------\nNoncompactly\n--------------------\n\n";
  Parser.Print.noncompactly test_compactness;
  Printf.printf "\n--------------------\nCompactly\n--------------------\n\n";
  Parser.Print.compactly test_compactness
