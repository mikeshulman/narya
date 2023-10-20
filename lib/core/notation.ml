(* A mixfix notation is an abstract object with a global existence.  They are represented internally by integers, to make them easily comparable and look-up-able. *)
type t = int

let counter = ref 0

let make () =
  let n = !counter in
  counter := !counter + 1;
  n

let compare : t -> t -> int = fun x y -> compare x y
