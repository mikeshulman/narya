open Util

(* We parametrize over an abstract module specifying how many endpoints our cubes have. *)

type len = N.two
type t = len N.index

let len : len N.t = N.two
let indices : (t, len) Bwv.t = Snoc (Snoc (Emp, Pop Top), Top)

let to_string : t option -> string = function
  | Some Top -> "1"
  | Some (Pop x) ->
      let Top = x in
      "0"
  | None -> "2"

let of_char : char -> (t option, unit) result = function
  | '0' -> Ok (Some (Pop Top))
  | '1' -> Ok (Some Top)
  | '2' -> Ok None
  | _ -> Error ()

let refl_char = 'r'
