(* Configuration options that affect the following code, and are scoped in sections, but don't change the underlying type theory. *)

type implicitness = [ `Implicit | `Explicit ]
type values = [ `Implicit | `Explicit ]

let to_string : values -> string = function
  | `Implicit -> "implicit"
  | `Explicit -> "explicit"

type t = { function_boundaries : implicitness; type_boundaries : implicitness }

let default : t = { function_boundaries = `Explicit; type_boundaries = `Explicit }
