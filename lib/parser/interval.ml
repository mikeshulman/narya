open Notation

(* An "upper tightness interval" is of the form (p,+∞] or [p,+∞] for some tightness p.  Ordinarily we would call these "open" and "closed" intervals, but due to the potential confusion with "closed" and "open" notations we call them instead "strict" and "nonstrict". *)

type t = Strict of float | Nonstrict of float

let empty = Strict Float.infinity
let entire = Nonstrict Float.neg_infinity

let to_string = function
  | Nonstrict x -> Printf.sprintf "[%f,inf]" x
  | Strict x -> Printf.sprintf "(%f,inf]" x

let endpoint : t -> float = function
  | Nonstrict x -> x
  | Strict x -> x

let right_assoc (tight : float) (assoc : associativity) : t =
  match assoc with
  | Right -> Nonstrict tight
  | Left | Non -> Strict tight

let contains : t -> float -> bool =
 fun i x ->
  match i with
  | Nonstrict p -> p <= x
  | Strict p -> p < x

(* A notation has associated upper tightness intervals on both the left and the right, which specify what tightnesses of other notations can appear in an open subterm on that side.  Thus, both of these intervals start at the tightness of the notation, with their open- or closed-ness determined by its associativity. *)
let left : notation -> t =
 fun d ->
  match assoc d with
  | Left -> Nonstrict (tightness d)
  | Right | Non -> Strict (tightness d)

let right : notation -> t =
 fun d ->
  match assoc d with
  | Right -> Nonstrict (tightness d)
  | Left | Non -> Strict (tightness d)

let compare : t -> t -> int = fun x y -> compare x y
