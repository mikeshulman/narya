open Testutil.Print

(* TODO: Some of the pretty-printing routines yield blank spaces at the end of lines, though they otherwise look nice.  It would be nice if we could tweak them to not do that, or failing that do some postprocessing to remove the extra spaces. *)

let test_reformat () =
  Testutil.Repl.run @@ fun () ->
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

  (* Binary operators *)
  Testutil.Repl.(
    def "ℕ" "Type" "data [ zero. | suc. (_ : ℕ) ]";
    def "plus" "ℕ → ℕ → ℕ"
      "m n ↦ match n [
       | zero. ↦ m
       | suc. n ↦ suc. (plus m n)
     ]";
    cmd ~quiet:true "notation 0 plus : m \"+\" n … ≔ plus m n";
    def "times" "ℕ → ℕ → ℕ"
      "m n ↦ match n [
       | zero. ↦ zero.
       | suc. n ↦ plus (times m n) m
     ]";
    cmd ~quiet:true "notation 1 times : m \"*\" n … ≔ times m n");
  reformat "x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x";
  reformat "x + x * x + x * x * x + x * x * x * x + x + x * x * x * x * x * x * x";

  (* Lists *)
  Testutil.Repl.def "List" "Type → Type" "A ↦ data [ nil. | cons. (x:A) (xs:List A) ]";
  Testutil.Repl.def "Bwd" "Type → Type" "A ↦ data [ emp. | snoc. (xs:Bwd A) (x:A) ]";
  reformat "[> 1, 2, 3 >]";
  reformat "[> 1 >]";
  reformat "[> >]";
  reformat "[< 1, 2, 3 <]";
  reformat "[< 1 <]";
  reformat "[< <]";
  reformat "[> blah, blah, blah, blah, blah, blah, blah, blah, blah, blah, blah >]";
  reformat "[< blah, blah, blah, blah, blah, blah, blah, blah, blah, blah, blah <]";
  Testutil.Repl.cmd ~quiet:true "notation 5 cons : x \":>\" y … ≔ cons. x y";
  Testutil.Repl.cmd ~quiet:true "notation 5 snoc : … x \"<:\" y ≔ snoc. x y";
  reformat "1 :> 2 :> 3 :> xs";
  reformat "xs <: 1 <: 2 <: 3";
  reformat "x :> x :> x :> x :> x :> x :> x :> x :> x :> x :> x :> x :> x :> x :> xs";
  reformat "xs <: x <: x <: x <: x <: x <: x <: x <: x <: x <: x <: x <: x <: x <: x";
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

  (* Tuples *)
  set_margin 30;
  reformat "(fst := M, snd := N)";
  reformat "f (fst := M, snd := N)";
  reformat "(fst := blah blah blah blah blah blah, snd := blah blah blah blah blah blah blah blah)";
  reformat "(fst := blah blah blah blah blah blah, snd := blah)";
  reformat
    "f (fst := blah blah blah blah blah blah, snd := blah blah blah blah blah blah blah blah)";
  reformat "f (fst := blah blah blah blah blah blah, snd := blah)";
  set_margin 40;
  reformat "(fst := M, snd := (foo := N, bar := P))";
  reformat "(fst := M, snd := (foo := N, bar := P),)";
  reformat "f (fst := M, snd := (foo := N, bar := P))";

  (* Comatches *)
  set_margin 30;
  reformat
    "[.fst |-> blah blah blah blah blah blah | .snd |-> blah blah blah blah blah blah blah blah]";
  set_margin 80;
  reformat "[.fst |-> [.foo |-> bar  | .baz |-> qux ] | .snd |-> [ .poo |-> [ .bah |-> bum ] ] ]";

  (* Matches *)
  reformat "[fst. |-> [foo. |-> bar  | baz. |-> qux ] | snd. |-> [ poo. |-> [ bah. |-> bum ] ] ]";
  set_margin 30;
  reformat "match x [ con. a b |-> blah blah | str. u v |-> bluh bluh ]";
  reformat
    "match x [| con. a b |-> blah blah blah blah blah blah blah blah blah blah  | str. u v |-> bluh bluh ]";
  reformat
    "match x [| con. a a a a a a a a a a a a a a a a a a a a a a a  |-> blah blah | str. u v |-> bluh bluh ]";
  reformat
    "match x [| con. a a a a a a a a a a a a a a a a a a a a a a a  |-> blah blah blah blah blah blah blah blah blah blah blah | str. u v |-> bluh bluh ]";
  reformat "[ con. a b |-> blah blah | str. u v |-> bluh bluh ]";
  reformat
    "match x [| con. a b |-> match y [ foo. |-> ba ba baa ba baa baba ba ba baaba babba ba | bar. u v w z w |-> z ] | str. u v |-> bluh bluh ]";
  reformat
    "match x [| con. a b |-> [ .foo |-> ba ba baa ba baa baba ba ba baaba babba ba | .bar |-> z ] | str. u v |-> [ .flab |-> boo boo | .flub |-> zoo zo zoo zo zzo zo ] ]";
  reformat
    "[ con. a b |-> [ foo. x |-> ba ba ba | bar. y z |-> y ] | str. u v |-> [ baz. |-> bluh bluh ] ]";
  reformat "(match x [| poo. |-> bah])";
  reformat "match x, y [ true., false. ↦ 0 | true., true. ↦ 1 ]";
  reformat
    "match x [ zero. ↦ 0 | suc. zero. ↦ 1 | suc. (suc. zero.) ↦ 2 | suc. (suc. (suc. n)) ↦ n ]";

  (* Canonical types *)
  reformat "codata [ x .head : blah blah blah blah blah blah blah blah | x .tail : Stream A ]";
  reformat
    "codata [ x .head : blah blah blah blah blah blah blah blah -> blah | x .tail : Stream A ]";
  reformat "sig ( fst : blah blah blah blah blah blah blah blah, tail : Stream A )";
  reformat "data [ one. : blah blah blah blah blah blah blah blah blah -> blah | two. : me ]";
  ()

let () =
  run @@ fun () ->
  Parser.Printconfig.run ~env:{ style = `Compact; state = `Case; chars = `Unicode } test_reformat;
  Printf.printf "--------------------\nNoncompactly\n--------------------\n\n";
  Parser.Printconfig.run
    ~env:{ style = `Noncompact; state = `Case; chars = `Unicode }
    test_compactness;
  Printf.printf "\n--------------------\nCompactly\n--------------------\n\n";
  Parser.Printconfig.run ~env:{ style = `Compact; state = `Case; chars = `Unicode } test_compactness
