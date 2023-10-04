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
