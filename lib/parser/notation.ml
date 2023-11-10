(* A mixfix notation is an abstract object with a global existence.  They are represented internally by integers, to make them easily comparable and look-up-able. *)
type t = int * (unit -> unit)

let counter = ref 0

let make () =
  let n = !counter in
  counter := !counter + 1;
  (n, fun _ -> ())

let compare : t -> t -> int = fun x y -> compare x y
