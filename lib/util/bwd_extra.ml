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

(* Now take as many elements as are in the supplied list, pairing them with the corresponding element. *)
let bwd_take_labeled : type a k. k list -> a Bwd.t -> ((k, a) Abwd.t * a Bwd.t) option =
 fun labels args ->
  let rec take_atmost labels args =
    match args with
    | Emp -> (
        match labels with
        | [] -> `Found (Emp, Emp)
        | k :: labels -> `Need_more (Emp, k, labels))
    | Snoc (xs, x) -> (
        match take_atmost labels xs with
        | `Need_more (first, k, []) -> `Found (Snoc (first, (k, x)), Emp)
        | `Need_more (first, k, l :: labels) -> `Need_more (Snoc (first, (k, x)), l, labels)
        | `Found (first, rest) -> `Found (first, Snoc (rest, x))) in
  match take_atmost labels args with
  | `Need_more _ -> None
  | `Found (first, rest) -> Some (first, rest)
