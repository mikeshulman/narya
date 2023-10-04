open Testutil
open Mcp
open Core.Check.CheckErr

let uu, _ = synth "Type"
let aa = assume "A" uu
let atoa = check "A→A" uu
let f = assume "f" atoa
let a = assume "a" aa

let () =
  match check "a" uu with
  | exception Checking_failure Unequal_synthesized_type -> ()
  | _ -> raise (Failure "Unexpected success")

let () =
  match synth "refl f a" with
  | exception Synthesis_failure Not_enough_arguments_to_function -> ()
  | _ -> raise (Failure "Unexpected success")

let () =
  match synth "refl f a a" with
  | exception Synthesis_failure Not_enough_arguments_to_function -> ()
  | _ -> raise (Failure "Unexpected success")

let _ = synth "refl f a a (refl a)"

let _ =
  match synth "refl f a a (refl a) a" with
  | exception Synthesis_failure Applying_nonfunction_nontype -> ()
  | _ -> raise (Failure "Unexpected success")

let () =
  match synth "Id A a" with
  | exception Synthesis_failure Not_enough_arguments_to_instantiation -> ()
  | _ -> raise (Failure "Unexpected success")

let idff = check "Id (A→A) f f" uu

let () =
  match check "x ↦ x" idff with
  | exception Checking_failure Not_enough_lambdas -> ()
  | _ -> raise (Failure "Unexpected success")

let () =
  match check "x y ↦ x" idff with
  | exception Checking_failure Not_enough_lambdas -> ()
  | _ -> raise (Failure "Unexpected success")

let _ = check "x0 x1 x2 ↦ refl f x0 x1 x2" idff

let () =
  match check "x0 x1 x2 x3 ↦ refl f x0 x1 x2" idff with
  | exception Checking_failure Checking_mismatch -> ()
  | _ -> raise (Failure "Unexpected success")

let () =
  match synth "refl (x ↦ x)" with
  | exception Synthesis_failure Nonsynthesizing_argument_of_refl -> ()
  | _ -> raise (Failure "Unexpected success")

let () =
  match synth "refl" with
  | exception Synthesis_failure Missing_arguments_of_symbol -> ()
  | _ -> raise (Failure "Unexpected success")

let () =
  match synth "sym f" with
  | exception Synthesis_failure Low_dimensional_argument_of_sym -> ()
  | _ -> raise (Failure "Unexpected success")

let () =
  match synth "g" with
  | exception Synthesis_failure (No_such_constant _) -> ()
  | _ -> raise (Failure "Unexpected success")

let ida, _ = synth "Id A"

let () =
  match check "a" ida with
  | exception Checking_failure Type_not_fully_instantiated -> ()
  | _ -> raise (Failure "Unexpected success")

let idida, _ = synth "Id (Id A) a a (refl a) a a (refl a)"

let () =
  match check "a" idida with
  | exception Checking_failure Type_not_fully_instantiated -> ()
  | _ -> raise (Failure "Unexpected success")

let () = assert (Option.is_none (Core.Equal.equal_val 0 aa ida))

(* Records and datatypes *)
let () = Types.Sigma.install ()
let () = Types.Nat.install ()
let atou = check "A→Type" uu
let bb = assume "B" atou
let sigab = check "(x:A)× B x" uu

let () =
  match check "{ fst ≔ a }" sigab with
  | exception Checking_failure Missing_field_in_struct -> ()
  | _ -> raise (Failure "Unexpected success")

let () =
  match check "{ fst ≔ a }" aa with
  | exception Checking_failure Checking_mismatch -> ()
  | _ -> raise (Failure "Unexpected success")

let nat = check "N" uu

let () =
  match check "{ fst ≔ a }" nat with
  | exception Checking_failure Checking_struct_against_nonrecord -> ()
  | _ -> raise (Failure "Unexpected success")

let s = assume "s" sigab

let () =
  match synth "s .third" with
  | exception Synthesis_failure (No_such_field _) -> ()
  | _ -> raise (Failure "Unexpected success")

let () =
  match check "0." sigab with
  | exception Checking_failure Checking_constructor_against_nondatatype -> ()
  | _ -> raise (Failure "Unexpected success")

let () =
  match check "2." nat with
  | exception Checking_failure (No_such_constructor _) -> ()
  | _ -> raise (Failure "Unexpected success")

let () =
  match check "0. a" nat with
  | exception Checking_failure Wrong_number_of_arguments_to_constructor -> ()
  | _ -> raise (Failure "Unexpected success")

let () =
  match check "1." nat with
  | exception Checking_failure Wrong_number_of_arguments_to_constructor -> ()
  | _ -> raise (Failure "Unexpected success")

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
  match check "{ ungel ≔ r2 }" symr2ty with
  | exception Checking_failure Record_has_degeneracy -> ()
  | _ -> raise (Failure "Unexpected success")
