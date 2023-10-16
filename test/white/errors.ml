open Testutil
open Mcp

let () =
  run @@ fun () ->
  let uu, _ = synth "Type" in
  let aa = assume "A" uu in
  let atoa = check "A→A" uu in
  let f = assume "f" atoa in
  let a = assume "a" aa in
  let () = uncheck "a" uu ~code:Unequal_synthesized_type in
  let () = unsynth "refl f a" ~code:Not_enough_arguments_to_function in
  let () = unsynth "refl f a a" ~code:Not_enough_arguments_to_function in
  let _ = synth "refl f a a (refl a)" in
  let _ = unsynth "refl f a a (refl a) a" ~code:Applying_nonfunction_nontype in
  let () = unsynth "Id A a" ~code:Not_enough_arguments_to_instantiation in
  let idff = check "Id (A→A) f f" uu in
  let () = uncheck "x ↦ x" idff ~code:(Not_enough_lambdas 2) in
  let () = uncheck "x y ↦ x" idff ~code:(Not_enough_lambdas 1) in
  let _ = check "x0 x1 x2 ↦ refl f x0 x1 x2" idff in
  let () = uncheck "x0 x1 x2 x3 ↦ refl f x0 x1 x2" idff ~code:Checking_mismatch in
  let () = unsynth "refl (x ↦ x)" ~code:(Nonsynthesizing "refl") in
  let () = unsynth "refl" ~code:Missing_argument_of_degeneracy in
  let () = unsynth "sym f" ~code:(Low_dimensional_argument_of_degeneracy ("sym", 2)) in
  let () = unsynth "g" ~code:(Unbound_variable "g") in
  let ida, _ = synth "Id A" in
  let () = uncheck "a" ida ~code:(Type_not_fully_instantiated "typechecking") in
  let idida, _ = synth "Id (Id A) a a (refl a) a a (refl a)" in
  let () = uncheck "a" idida ~code:(Type_not_fully_instantiated "typechecking") in
  let () = assert (Option.is_none (Core.Equal.equal_val 0 aa ida)) in

  (* Parse errors *)
  let () = unsynth "let x := a in b : c" ~short:"E0000" in
  let () = unsynth "x y |-> z : w" ~short:"E0000" in
  (* let _ = synth "x y {` unterminated block comment" in *)
  let () = unsynth "x y {` unterminated block comment" ~short:"E0000" in
  (* let _ = synth ".fst x" in *)
  let () = unsynth ".fst x" ~short:"E0000" in

  (* Records and datatypes *)
  let () = Types.Sigma.install () in
  let () = Types.Nat.install () in
  let atou = check "A→Type" uu in
  let bb = assume "B" atou in
  let sigab = check "(x:A)× B x" uu in
  let () = uncheck "{ fst ≔ a }" sigab ~code:(Missing_field_in_struct (Core.Field.intern "snd")) in
  let () = uncheck "{ fst ≔ a }" aa ~code:Checking_mismatch in
  let nat = check "N" uu in
  let () = uncheck "{ fst ≔ a }" nat ~code:(Checking_struct_against_nonrecord Types.Nat.nn) in
  let () = uncheck "{ _ ≔ a }" sigab ~code:Unnamed_field_in_struct in
  let s = assume "s" sigab in
  let () =
    unsynth "s .third" ~code:(No_such_field (Some Types.Sigma.sigma, Core.Field.intern "third"))
  in
  let () =
    uncheck "0." sigab
      ~code:(Checking_constructor_against_nondatatype (Types.Nat.zero', Types.Sigma.sigma)) in
  let () = uncheck "2." nat ~code:(No_such_constructor (Types.Nat.nn, Core.Constr.intern "2")) in
  let () =
    uncheck "0. a" nat ~code:(Wrong_number_of_arguments_to_constructor (Types.Nat.zero', 1)) in
  let () = uncheck "1." nat ~code:(Wrong_number_of_arguments_to_constructor (Types.Nat.suc', -1)) in
  let () = uncheck "4.2" nat ~code:(Unsupported_numeral 4.2) in

  (* To test degeneracies on records we have to set up a bunch of stuff, since the simplest case this happens is with Id Gel and squares in the universe. *)
  let () = Types.Gel.install () in
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
    synth "refl Gel A0 A1 A2 B0 B1 B2 R0 R1 R2 a0 a1 a2 b0 b1 b2 { ungel ≔ r0} { ungel ≔ r1 }" in

  let r2' = check "{ ungel ≔ r2 }" r2ty in

  let symr2ty, _ =
    synth "sym (refl Gel A0 A1 A2 B0 B1 B2 R0 R1 R2) a0 b0 { ungel ≔ r0} a1 b1 { ungel ≔ r1 } a2 b2"
  in

  let () =
    uncheck "{ ungel ≔ r2 }" symr2ty ~code:(Checking_struct_at_degenerated_record Types.Gel.gel)
  in
  ()
