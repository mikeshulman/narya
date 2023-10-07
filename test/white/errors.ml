open Testutil
open Mcp

let uu, _ = synth "Type"
let aa = assume "A" uu
let atoa = check "A→A" uu
let f = assume "f" atoa
let a = assume "a" aa
let () = uncheck "a" uu ~code:Unequal_synthesized_type
let () = unsynth "refl f a" ~code:Not_enough_arguments_to_function
let () = unsynth "refl f a a" ~code:Not_enough_arguments_to_function
let _ = synth "refl f a a (refl a)"
let _ = unsynth "refl f a a (refl a) a" ~code:Applying_nonfunction_nontype
let () = unsynth "Id A a" ~code:Not_enough_arguments_to_instantiation
let idff = check "Id (A→A) f f" uu
let () = uncheck "x ↦ x" idff ~code:Not_enough_lambdas
let () = uncheck "x y ↦ x" idff ~code:Not_enough_lambdas
let _ = check "x0 x1 x2 ↦ refl f x0 x1 x2" idff
let () = uncheck "x0 x1 x2 x3 ↦ refl f x0 x1 x2" idff ~code:Checking_mismatch
let () = unsynth "refl (x ↦ x)" ~code:(Nonsynthesizing_argument_of_degeneracy "refl")
let () = unsynth "refl" ~code:Missing_argument_of_degeneracy
let () = unsynth "sym f" ~code:(Low_dimensional_argument_of_degeneracy ("sym", 2))
let () = unsynth "g" ~code:(Unbound_variable (Core.Constant.intern "g"))
let ida, _ = synth "Id A"
let () = uncheck "a" ida ~code:Type_not_fully_instantiated
let idida, _ = synth "Id (Id A) a a (refl a) a a (refl a)"
let () = uncheck "a" idida ~code:Type_not_fully_instantiated
let () = assert (Option.is_none (Core.Equal.equal_val 0 aa ida))

(* Records and datatypes *)
let () = Types.Sigma.install ()
let () = Types.Nat.install ()
let atou = check "A→Type" uu
let bb = assume "B" atou
let sigab = check "(x:A)× B x" uu
let () = uncheck "{ fst ≔ a }" sigab ~code:(Missing_field_in_struct Types.Sigma.snd)
let () = uncheck "{ fst ≔ a }" aa ~code:Checking_mismatch
let nat = check "N" uu
let () = uncheck "{ fst ≔ a }" nat ~code:(Checking_struct_against_nonrecord Types.Nat.nn)
let s = assume "s" sigab

let () =
  unsynth "s .third" ~code:(No_such_field (Some Types.Sigma.sigma, Core.Field.intern "third"))

let () =
  uncheck "0." sigab
    ~code:(Checking_constructor_against_nondatatype (Types.Nat.zero', Types.Sigma.sigma))

let () = uncheck "2." nat ~code:(No_such_constructor (Types.Nat.nn, Core.Constr.intern "2"))
let () = uncheck "0. a" nat ~code:Wrong_number_of_arguments_to_constructor
let () = uncheck "1." nat ~code:Wrong_number_of_arguments_to_constructor

(* To test degeneracies on records we have to set up a bunch of stuff, since the simplest case this happens is with Id Gel and squares in the universe. *)
let () = Types.Gel.install ()
let aa0 = assume "A0" uu
let bb0 = assume "B0" uu
let corrab0, _ = synth "A0 → B0 → Type"
let rr0 = assume "R0" corrab0
let aa1 = assume "A1" uu
let bb1 = assume "B1" uu
let corrab1, _ = synth "A1 → B1 → Type"
let rr1 = assume "R1" corrab1
let iduua, _ = synth "Id Type A0 A1"
let aa2 = assume "A2" iduua
let iduub, _ = synth "Id Type B0 B1"
let bb2 = assume "B2" iduub

let iduur, _ = synth "refl ((X ↦ Y ↦ (X→Y→Type)) : Type→Type→Type) A0 A1 A2 B0 B1 B2 R0 R1"

let r2 = assume "R2" iduur
let gelr2, _ = synth "refl Gel A0 A1 A2 B0 B1 B2 R0 R1 R2"
let a0 = assume "a0" aa0
let a1 = assume "a1" aa1
let a2 = assume "a2" (fst (synth "A2 a0 a1"))
let b0 = assume "b0" bb0
let b1 = assume "b1" bb1
let b2 = assume "b2" (fst (synth "B2 b0 b1"))
let r0 = assume "r0" (fst (synth "R0 a0 b0"))
let r1 = assume "r1" (fst (synth "R1 a1 b1"))
let r2 = assume "r2" (fst (synth "R2 a0 a1 a2 b0 b1 b2 r0 r1"))

let r2ty, _ =
  synth "refl Gel A0 A1 A2 B0 B1 B2 R0 R1 R2 a0 a1 a2 b0 b1 b2 { ungel ≔ r0} { ungel ≔ r1 }"

let r2' = check "{ ungel ≔ r2 }" r2ty

let symr2ty, _ =
  synth "sym (refl Gel A0 A1 A2 B0 B1 B2 R0 R1 R2) a0 b0 { ungel ≔ r0} a1 b1 { ungel ≔ r1 } a2 b2"

let () =
  uncheck "{ ungel ≔ r2 }" symr2ty ~code:(Checking_struct_at_degenerated_record Types.Gel.gel)
