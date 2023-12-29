open Bwd

(* Split off the first element of a Bwd.t, if it is nonempty. *)
let rec split_first = function
  | Emp -> None
  | Snoc (Emp, x) -> Some (x, Emp)
  | Snoc (xs, x) -> (
      match split_first xs with
      | Some (y, ys) -> Some (y, Snoc (ys, x))
      | None -> None)

(* Split a Bwd.t into its first k elements and the rest, if it has at least k. *)
let bwd_take : type a. int -> a Bwd.t -> (a Bwd.t * a Bwd.t) option =
 fun k args ->
  let rec take_atmost k args =
    match args with
    | Emp -> if k > 0 then `Need_more k else `Found (Emp, Emp)
    | Snoc (xs, x) -> (
        match take_atmost k xs with
        | `Need_more n -> if n = 1 then `Found (args, Emp) else `Need_more (n - 1)
        | `Found (first, rest) -> `Found (first, Snoc (rest, x))) in
  match take_atmost k args with
  | `Need_more _ -> None
  | `Found (first, rest) -> Some (first, rest)
