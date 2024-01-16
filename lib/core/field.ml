module Field = struct
  type t = string

  let compare (x : t) (y : t) = compare x y
end

type t = Field.t

let intern (str : string) : t = str

module Set = Set.Make (Field)

let to_string (x : t) : string = x

type or_index = [ `Name of t | `Index of int ]

let to_string_ori (x : or_index) : string =
  match x with
  | `Name str -> str
  | `Index n -> string_of_int n

let intern_ori (str : string) : or_index =
  try
    let n = int_of_string str in
    `Index n
  with Failure _ -> `Name str
