type t = [ `Block of string | `Line of string | `Newlines of int ]
type alist = (Token.t * t list) list
