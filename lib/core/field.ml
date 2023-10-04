module Field = struct
  type t = string

  let compare (x : t) (y : t) = compare x y
end

type t = Field.t

let intern (str : string) : t = str

module Map = Map.Make (Field)

let to_string (x : t) : string = x
