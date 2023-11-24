open Util
open Notation

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

let contains : type a. t -> a No.t -> bool =
 fun (Interval (s, p)) x ->
  match No.compare s p x with
  | Some _ -> true
  | None -> false

(* A notation has associated upper tightness intervals on both the left and the right, which specify what tightnesses of other notations can appear in an open subterm on that side.  Thus, both of these intervals start at the tightness of the notation, with their open- or closed-ness determined by its associativity. *)
let left : ('s opn, 'tight, 'right) notation -> t =
 fun n ->
  let (Open s) = left n in
  Interval (s, tightness n)

let right : ('left, 'tight, 's opn) notation -> t =
 fun n ->
  let (Open s) = right n in
  Interval (s, tightness n)

let compare : t -> t -> int = fun x y -> compare x y
