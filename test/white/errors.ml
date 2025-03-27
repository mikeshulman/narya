open Dim
open Testutil.Mcp

let () =
  Parser.Unparse.install ();
  run @@ fun () ->
  let uu, _ = synth "Type" in
  let aa = assume "A" uu in
  let atoa = check "A→A" uu in
  let f = assume "f" atoa in
  let a = assume "a" aa in
  let () = uncheck ~print:() "a" uu ~short:"E0401" in
  let () = unsynth ~print:() "refl f a" ~code:Not_enough_arguments_to_function in
  let () = unsynth ~print:() "refl f a a" ~code:Not_enough_arguments_to_function in
  let _ = synth "refl f a a (refl a)" in
  let _ = unsynth "refl f a a (refl a) a" ~short:"E0701" in
  let () = unsynth ~print:() "Id A a" ~code:Not_enough_arguments_to_instantiation in
  let idff = check "Id (A→A) f f" uu in
  let () = uncheck ~print:() "x ↦ x" idff ~code:(Not_enough_lambdas 2) in
  let () = uncheck ~print:() "x y ↦ x" idff ~code:(Not_enough_lambdas 1) in
  let _ = check "x0 x1 x2 ↦ refl f x0 x1 x2" idff in
  let () = uncheck ~print:() "x0 x1 x2 x3 ↦ refl f x0 x1 x2" idff ~short:"E0700" in
  let () = unsynth ~print:() "refl (x ↦ x)" ~code:(Nonsynthesizing "argument of degeneracy") in
  let () = unsynth ~print:() "refl" ~code:(Missing_argument_of_degeneracy "refl") in
  let () = unsynth ~print:() "sym f" ~short:"E0601" in
  let a0 = assume "a0" aa in
  let a1 = assume "a1" aa in
  let idaa, _ = synth "Id A a0 a1" in
  let a2 = assume "a2" idaa in
  let () = unsynth ~print:() "sym a2" ~short:"E0601" in
  let () = unsynth ~print:() "g" ~code:(Unbound_variable ("g", [])) in
  let ida, _ = synth "Id A" in
  let () = uncheck ~print:() "a" ida ~short:"E0401" in
  let idida, _ = synth "Id (Id A) a a (refl a) a a (refl a)" in
  let () = uncheck ~print:() "a" idida ~short:"E0401" in
  let () = assert (Option.is_none (Core.Equal.equal_val 0 aa ida)) in

  (* Parse errors. *)
  let () = unsynth ~print:() "x y {` unterminated block comment" ~code:Parse_error in
  let () = unsynth ~print:() "f (x" ~code:Parse_error in
  let () = unsynth ~print:() ".fst x" ~code:Parse_error in
  let () = unsynth ~print:() "x |-> x .fs.t y" ~code:(Invalid_field ".fs.t") in
  let () =
    unsynth ~print:() "f (con.str. x)" ~code:(Unimplemented "higher constructors: con.str.") in
  let () = unsynth ~print:() "x |-> f 0.1.2 x" ~code:(Invalid_numeral "0.1.2") in
  let () = unsynth ~print:() "let x.y ≔ z in w" ~code:(Invalid_variable [ "x"; "y" ]) in
  let () = unsynth ~print:() "x.y ↦ z" ~code:(Invalid_variable [ "x"; "y" ]) in
  let () = unsynth ~print:() "a x.y b ↦ z" ~code:(Invalid_variable [ "x"; "y" ]) in
  let () = unsynth ~print:() "↦ x" ~code:Parse_error in
  let () = unsynth ~print:() "(f x) y ↦ z" ~code:Parse_error in
  let () = unsynth ~print:() "_" ~code:(Unimplemented "unification arguments") in
  let () = unsynth ~print:() "a ↦ ( fst ≔ a, fst ≔ a )" ~code:(Duplicate_field_in_tuple "fst") in
  let () = unsynth ~print:() "( (x) ≔ a )" ~code:Invalid_field_in_tuple in
  let () = unsynth ~print:() "[ _ ↦ a ]" ~code:(Nonsynthesizing "top-level unsynth") in
  let () = unsynth ~print:() "[ (x) ↦ a ]" ~code:(Nonsynthesizing "top-level unsynth") in
  let () = unsynth ~print:() "[ | | .head |-> 0 | .tail |-> f ]" ~code:Parse_error in

  (* Records and datatypes *)
  Testutil.Repl.(
    def "Σ" "(A : Type) → (A → Type) → Type" "A B ↦ sig ( fst : A, snd : B fst)";
    def "ℕ" "Type" "data [ zero. | suc. (_ : ℕ) ]";
    def "Nat" "Type" "ℕ");
  let atou = check "A→Type" uu in
  let bb = assume "B" atou in
  let sigab = check "Σ A B" uu in
  let () =
    uncheck ~print:() "( fst ≔ a )" sigab
      ~code:(Missing_field_in_tuple (Core.Field.intern "snd" D.zero, None)) in
  let () = uncheck ~print:() "( fst ≔ a )" aa ~short:"E0900" in
  let nat = check "ℕ" uu in
  let () = uncheck ~print:() "( fst ≔ a )" nat ~short:"E0900" in
  let s = assume "s" sigab in
  let () = unsynth ~print:() "s .third" ~short:"E0800" in
  let () = uncheck ~print:() "zero." sigab ~short:"E1000" in
  let () = uncheck ~print:() "two." nat ~short:"E1000" in
  let () =
    uncheck ~print:() "zero. a" nat
      ~code:(Wrong_number_of_arguments_to_constructor (Core.Constr.intern "zero", 1)) in
  let () =
    uncheck ~print:() "suc." nat
      ~code:(Wrong_number_of_arguments_to_constructor (Core.Constr.intern "suc", -1)) in
  let () =
    uncheck ~print:() "4.2" nat ~code:(Unsupported_numeral (Q.make (Z.of_int 21) (Z.of_int 5)))
  in

  (* To test degeneracies on records we have to set up a bunch of stuff, since the simplest case this happens is with Id Gel and squares in the universe. *)
  Testutil.Repl.gel_install ();
  let aa0 = assume "A0" uu in
  let bb0 = assume "B0" uu in
  let corrab0, _ = synth "A0 → B0 → Type" in
  let rr0 = assume "R0" corrab0 in
  let aa1 = assume "A1" uu in
  let bb1 = assume "B1" uu in
  let corrab1, _ = synth "A1 → B1 → Type" in
  let rr1 = assume "R1" corrab1 in
  let iduua, _ = synth "Id Type A0 A1" in
  let aa2 = assume "A2" iduua in
  let iduub, _ = synth "Id Type B0 B1" in
  let bb2 = assume "B2" iduub in

  let iduur, _ = synth "refl ((X ↦ Y ↦ (X→Y→Type)) : Type→Type→Type) A0 A1 A2 B0 B1 B2 R0 R1" in

  let r2 = assume "R2" iduur in
  let gelr2, _ = synth "refl Gel A0 A1 A2 B0 B1 B2 R0 R1 R2" in
  let a0 = assume "a0" aa0 in
  let a1 = assume "a1" aa1 in
  let a2 = assume "a2" (fst (synth "A2 a0 a1")) in
  let b0 = assume "b0" bb0 in
  let b1 = assume "b1" bb1 in
  let b2 = assume "b2" (fst (synth "B2 b0 b1")) in
  let r0 = assume "r0" (fst (synth "R0 a0 b0")) in
  let r1 = assume "r1" (fst (synth "R1 a1 b1")) in
  let r2 = assume "r2" (fst (synth "R2 a0 a1 a2 b0 b1 b2 r0 r1")) in

  let r2ty, _ =
    synth "refl Gel A0 A1 A2 B0 B1 B2 R0 R1 R2 a0 a1 a2 b0 b1 b2 (ungel ≔ r0) (ungel ≔ r1)" in

  let r2' = check "(ungel ≔ r2)" r2ty in

  let symr2ty, _ =
    synth "sym (refl Gel A0 A1 A2 B0 B1 B2 R0 R1 R2) a0 b0 (ungel ≔ r0) a1 b1 (ungel ≔ r1) a2 b2"
  in

  let () = uncheck ~print:() "(ungel ≔ r2)" symr2ty ~short:"E0901" in

  let gg = assume "gg" r2ty in
  let _ = synth "gg .ungel" in
  let gg' = assume "gg'" symr2ty in
  let _ =
    unsynth ~print:() "gg' .ungel"
      ~code:(No_such_field (`Degenerated_record Eta, `Strings ("ungel", []))) in

  (* Cube variables *)
  let () = uncheck ~print:() "x ↦ x.0" atoa ~short:"E0506" in
  ()
