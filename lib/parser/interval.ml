open Util

(* An "upper tightness interval" is of the form (p,+∞] or [p,+∞] for some tightness p.  Ordinarily we would call these "open" and "closed" intervals, but due to the potential confusion with "closed" and "open" notations we call them instead "strict" and "nonstrict". *)

type ('a, 's) tt = 's No.strictness * 'a No.t
type t = Interval : ('s, 'a) tt -> t

let empty : (No.plus_omega, No.strict) tt = (Strict, No.plus_omega)
let entire : (No.minus_omega, No.nonstrict) tt = (Nonstrict, No.minus_omega)

let to_string = function
  | Interval (Nonstrict, x) -> Printf.sprintf "[%s,inf]" (No.to_string x)
  | Interval (Strict, x) -> Printf.sprintf "(%s,inf]" (No.to_string x)

let endpoint : type e s. (e, s) tt -> No.wrapped = function
  | No.Nonstrict, x -> Wrap x
  | Strict, x -> Wrap x

let contains : type a s b. (a, s) tt -> b No.t -> (a, s, b) No.lt option =
 fun (s, p) x -> No.compare s p x

let compare : t -> t -> int = fun x y -> compare x y
