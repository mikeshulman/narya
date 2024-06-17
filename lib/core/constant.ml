module Constant = struct
  type t = int

  let compare (x : t) (y : t) = compare x y
end

type t = Constant.t

let counter = ref (-1)

let make () : t =
  counter := !counter + 1;
  !counter

module Map = struct
  include Map.Make (Constant)
end
