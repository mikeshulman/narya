open Util
open Notation

(* An "upper tightness interval" is of the form (p,+∞] or [p,+∞] for some tightness p.  Ordinarily we would call these "open" and "closed" intervals, but due to the potential confusion with "closed" and "open" notations we call them instead "strict" and "nonstrict". *)

type t = Strict : 'a No.t -> t | Nonstrict : 'a No.t -> t

let empty = Strict No.plus_omega
let entire = Nonstrict No.minus_omega

let to_string = function
  | Nonstrict x -> Printf.sprintf "[%s,inf]" (No.to_string x)
  | Strict x -> Printf.sprintf "(%s,inf]" (No.to_string x)

let endpoint : t -> No.wrapped = function
  | Nonstrict x -> Wrap x
  | Strict x -> Wrap x

let right_assoc : type a. a No.t -> associativity -> t =
 fun tight assoc ->
  match assoc with
  | Right -> Nonstrict tight
  | Left | Non -> Strict tight

let contains : type a. t -> a No.t -> bool =
 fun i x ->
  match i with
  | Nonstrict p -> (
      match No.compare Nonstrict p x with
      | Some _ -> true
      | None -> false)
  | Strict p -> (
      match No.compare Strict p x with
      | Some _ -> true
      | None -> false)

(* A notation has associated upper tightness intervals on both the left and the right, which specify what tightnesses of other notations can appear in an open subterm on that side.  Thus, both of these intervals start at the tightness of the notation, with their open- or closed-ness determined by its associativity. *)
let left : notation -> t =
 fun d ->
  match assoc d with
  | Left ->
      let (Wrap t) = tightness d in
      Nonstrict t
  | Right | Non ->
      let (Wrap t) = tightness d in
      Strict t

let right : notation -> t =
 fun d ->
  match assoc d with
  | Right ->
      let (Wrap t) = tightness d in
      Nonstrict t
  | Left | Non ->
      let (Wrap t) = tightness d in
      Strict t

let compare : t -> t -> int = fun x y -> compare x y
