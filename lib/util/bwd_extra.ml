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

(* Insert an element at a specified index (i.e. counting from the right). *)
let rec insert : type a. int -> a -> a Bwd.t -> a Bwd.t =
 fun i x xs ->
  if i < 0 then raise (Invalid_argument "Bwd_extra.insert")
  else if i = 0 then Snoc (xs, x)
  else
    match xs with
    | Emp -> raise (Invalid_argument "Bwd_extra.insert")
    | Snoc (xs, y) -> Snoc (insert (i - 1) x xs, y)

(* Like List.init, but applied to indices counting from the right. *)
let init : type a. int -> (int -> a) -> a Bwd.t =
 fun n f ->
  let rec go i = if i >= n then Emp else Snoc (go (i + 1), f i) in
  go 0

(* Remove n elements from the end of a Bwd.t *)
let rec remove xs n =
  if n <= 0 then xs
  else
    match xs with
    | Emp -> raise (Failure "Bwd_extra.remove")
    | Snoc (xs, _) -> remove xs (n - 1)

(* Last element of a Bwd *)
let last = function
  | Emp -> raise (Failure "Bwd_extra.last")
  | Snoc (_, x) -> x

(* Replace the last element of a Bwd with something else *)
let replace_last xs x =
  match xs with
  | Emp -> raise (Failure "Bwd_extra.replace_last")
  | Snoc (xs, _) -> Snoc (xs, x)

(* Modify the last element of a Bwd *)
let modify_last xs f =
  match xs with
  | Emp -> raise (Failure "Bwd_extra.replace_last")
  | Snoc (xs, x) -> Snoc (xs, f x)

let rec intersperse sep xs =
  match xs with
  | Emp -> Emp
  | Snoc (Emp, x) -> Snoc (Emp, x)
  | Snoc (Snoc (xs, x1), x2) -> Snoc (Snoc (Snoc (intersperse sep xs, x1), sep), x2)
