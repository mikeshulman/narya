type t = int

let counter = ref (-1)

let make () : t =
  counter := !counter + 1;
  !counter

let compare (x : t) (y : t) = compare x y
