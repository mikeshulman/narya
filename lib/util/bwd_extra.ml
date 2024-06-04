(* Extra functions acting on backwards lists *)

open Bwd

(* Find the leftmost element of a bwd *)
let rec head = function
  | Emp -> raise Not_found
  | Snoc (Emp, x) -> x
  | Snoc (xs, _) -> head xs

(* Split off the first element of a Bwd.t, if it is nonempty. *)
let rec split_first = function
  | Emp -> None
  | Snoc (Emp, x) -> Some (x, Emp)
  | Snoc (xs, x) -> (
      match split_first xs with
      | Some (y, ys) -> Some (y, Snoc (ys, x))
      | None -> None)

(* Append one Bwd to another *)
let rec append xs ys =
  match ys with
  | Emp -> xs
  | Snoc (ys, y) -> Snoc (append xs ys, y)

(* Convert from a list while mapping at the same time *)
let of_list_map f ys =
  let rec go xs ys =
    match ys with
    | [] -> xs
    | y :: ys -> go (Snoc (xs, f y)) ys in
  go Emp ys

(* Convert to a list while mapping at the same time *)
let rec prepend_map f xs ys =
  match xs with
  | Emp -> ys
  | Snoc (xs, x) -> prepend_map f xs (f x :: ys)

let to_list_map f xs = prepend_map f xs []
