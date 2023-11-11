open Notation

(* An "upper tightness interval" is of the form [p,+∞] or (p,+∞] for some tightness p. *)

(* This meaning of "open" and "closed" refers to "open intervals" and "closed intervals", which is unfortunately unrelated to the notions of "left-open" and "right-open" notations. *)
type t = Closed of float | Open of float

let entire = Closed Float.neg_infinity

let to_string = function
  | Closed x -> Printf.sprintf "[%f,inf]" x
  | Open x -> Printf.sprintf "(%f,inf]" x

let endpoint : t -> float = function
  | Closed x -> x
  | Open x -> x

let right_assoc (tight : float) (assoc : associativity) : t =
  match assoc with
  | Right -> Closed tight
  | Left | Non -> Open tight

let contains : t -> float -> bool =
 fun i x ->
  match i with
  | Closed p -> p <= x
  | Open p -> p < x

(* A notation has associated upper tightness intervals on both the left and the right, which specify what tightnesses of other notations can appear in an open subterm on that side.  Thus, both of these intervals start at the tightness of the notation, with their open- or closed-ness determined by its associativity. *)
let left : notation -> t =
 fun d ->
  match assoc d with
  | Left -> Closed (tightness d)
  | Right | Non -> Open (tightness d)

let right : notation -> t =
 fun d ->
  match assoc d with
  | Right -> Closed (tightness d)
  | Left | Non -> Open (tightness d)

let compare : t -> t -> int = fun x y -> compare x y
