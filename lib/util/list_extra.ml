(* Split off the last element of a list, if it is nonempty. *)
let rec split_last = function
  | [] -> None
  | [ x ] -> Some ([], x)
  | x :: xs -> (
      match split_last xs with
      | Some (ys, y) -> Some (x :: ys, y)
      | None -> None)
