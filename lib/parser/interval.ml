open Util

(* An "upper tightness interval" is of the form (p,+ω] or [p,+ω] for some tightness p.  Ordinarily we would call these "open" and "closed" intervals, but due to the potential confusion with "closed" and "open" notations we call them instead "strict" and "nonstrict". *)

type ('a, 's) tt = { strictness : 's No.strictness; endpoint : 'a No.t }
type t = Interval : ('s, 'a) tt -> t

let empty : (No.plus_omega, No.strict) tt = { strictness = Strict; endpoint = No.plus_omega }

let entire : (No.minus_omega, No.nonstrict) tt =
  { strictness = Nonstrict; endpoint = No.minus_omega }

let plus_omega_only : (No.plus_omega, No.nonstrict) tt =
  { strictness = Nonstrict; endpoint = No.plus_omega }

let to_string = function
  | Interval { strictness = Nonstrict; endpoint } ->
      Printf.sprintf "[%s,inf]" (No.to_string endpoint)
  | Interval { strictness = Strict; endpoint } -> Printf.sprintf "(%s,inf]" (No.to_string endpoint)

let contains : type a s b. (a, s) tt -> b No.t -> (a, s, b) No.lt option =
 fun { strictness; endpoint } x -> No.compare strictness endpoint x

let union : t -> t -> t =
 fun (Interval t1 as i1) (Interval t2 as i2) ->
  match No.compare Strict t1.endpoint t2.endpoint with
  | Some _ -> i1
  | None -> (
      match No.compare Strict t2.endpoint t1.endpoint with
      | Some _ -> i2
      | None -> (
          match (t1.strictness, t2.strictness) with
          | Strict, Strict -> Interval { t1 with strictness = Strict }
          | _ -> Interval { t1 with strictness = Nonstrict }))

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
