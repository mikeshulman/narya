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

let union : t -> t -> t =
 fun (Interval (s1, t1) as i1) (Interval (s2, t2) as i2) ->
  match No.compare Strict t1 t2 with
  | Some _ -> i1
  | None -> (
      match No.compare Strict t2 t1 with
      | Some _ -> i2
      | None -> (
          match (s1, s2) with
          | Strict, Strict -> Interval (Strict, t1)
          | _ -> Interval (Nonstrict, t1)))

type (_, _, _, _) subset =
  | Subset_strict : ('t2, No.strict, 't1) No.lt -> ('t1, 's1, 't2, 's2) subset
  | Subset_eq : ('t, 's, 't, 's) subset
  | Subset_nonstrict_strict : ('t, No.strict, 't, No.nonstrict) subset

let subset_contains :
    type t1 s1 t2 s2 a. (t1, s1, t2, s2) subset -> (t1, s1, a) No.lt -> (t2, s2, a) No.lt =
 fun sub lt1 ->
  match sub with
  | Subset_strict lt2 -> No.lt_trans Strict_any lt2 lt1
  | Subset_eq -> lt1
  | Subset_nonstrict_strict -> No.lt_to_le lt1

let compare : t -> t -> int = fun x y -> compare x y
