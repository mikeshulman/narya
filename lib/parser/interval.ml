open Util
open Notation

(* An "upper tightness interval" is of the form (p,+∞] or [p,+∞] for some tightness p.  Ordinarily we would call these "open" and "closed" intervals, but due to the potential confusion with "closed" and "open" notations we call them instead "strict" and "nonstrict". *)

type t = Interval : 's No.strictness * 'a No.t -> t

let empty = Interval (Strict, No.plus_omega)
let entire = Interval (Nonstrict, No.minus_omega)

let to_string = function
  | Interval (Nonstrict, x) -> Printf.sprintf "[%s,inf]" (No.to_string x)
  | Interval (Strict, x) -> Printf.sprintf "(%s,inf]" (No.to_string x)

let endpoint : t -> No.wrapped = function
  | Interval (No.Nonstrict, x) -> Wrap x
  | Interval (Strict, x) -> Wrap x

let contains : type a. t -> a No.t -> bool =
 fun (Interval (s, p)) x ->
  match No.compare s p x with
  | Some _ -> true
  | None -> false

(* A notation has associated upper tightness intervals on both the left and the right, which specify what tightnesses of other notations can appear in an open subterm on that side.  Thus, both of these intervals start at the tightness of the notation, with their open- or closed-ness determined by its associativity. *)
let left : 'tight notation -> t =
 fun n ->
  match left n with
  | Open s -> Interval (s, tightness n)
  | Closed -> raise (Invalid_argument "closed notations can't be left-associative")

let right : 'tight notation -> t =
 fun n ->
  match right n with
  | Open s -> Interval (s, tightness n)
  | Closed -> raise (Invalid_argument "closed notations can't be right-associative")

let compare : t -> t -> int = fun x y -> compare x y
