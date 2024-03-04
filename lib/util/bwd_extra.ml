(* Extra functions acting on backwards lists *)

open Bwd

(* Split off the first element of a Bwd.t, if it is nonempty. *)
let rec split_first = function
  | Emp -> None
  | Snoc (Emp, x) -> Some (x, Emp)
  | Snoc (xs, x) -> (
      match split_first xs with
      | Some (y, ys) -> Some (y, Snoc (ys, x))
      | None -> None)
