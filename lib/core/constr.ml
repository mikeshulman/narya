module Constr = struct
  type t = string

  let compare (x : t) (y : t) = compare x y
end

type t = Constr.t

let intern (str : string) : t = str

module Map = Map.Make (Constr)

let to_string (c : t) : string = c
