(* Extra functions acting on lists. *)

(* Find the last element of a nonempty list *)
let rec last = function
  | [] -> raise (Invalid_argument "List_extra.last")
  | [ x ] -> x
  | _ :: xs -> last xs

(* Split off the last element of a list, if it is nonempty. *)
let rec split_last = function
  | [] -> None
  | [ x ] -> Some ([], x)
  | x :: xs -> (
      match split_last xs with
      | Some (ys, y) -> Some (x :: ys, y)
      | None -> None)

(* Insert an element at a specified position (counting from the left). *)
let rec insert : type a. int -> a -> a list -> a list =
 fun i x xs ->
  if i < 0 then raise (Invalid_argument "List_extra.insert")
  else if i = 0 then x :: xs
  else
    match xs with
    | [] -> raise (Invalid_argument "List_extra.insert")
    | y :: xs -> y :: insert (i - 1) x xs
