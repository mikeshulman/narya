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

(* Convert from a list while mapping at the same time *)
let of_list_map f ys =
  let rec go xs ys =
    match ys with
    | [] -> xs
    | y :: ys -> go (Snoc (xs, f y)) ys in
  go Emp ys

(* Convert to a list while mapping at the same time *)
let to_list_map f xs =
  let rec go xs ys =
    match xs with
    | Emp -> ys
    | Snoc (xs, x) -> go xs (f x :: ys) in
  go xs []
