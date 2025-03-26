open Signatures

type zero
type 'a plus
type 'a minus
type minus_omega
type plus_omega
type _ t
type one = zero plus
type two = one plus
type three = two plus
type four = three plus
type five = four plus
type six = five plus
type seven = six plus
type eight = seven plus
type minus_one = zero minus
type minus_two = minus_one minus

val zero : zero t
val one : one t
val two : two t
val three : three t
val four : four t
val five : five t
val six : six t
val seven : seven t
val eight : eight t
val minus_one : minus_one t
val minus_two : minus_two t
val minus_omega : minus_omega t
val plus_omega : plus_omega t

type strict
type nonstrict
type _ strictness = Strict : strict strictness | Nonstrict : nonstrict strictness
type (_, _, _) lt

val le_refl : 'a t -> ('a, nonstrict, 'a) lt
val plusomega_nlt : (plus_omega, strict, 'a) lt -> 'b
val lt_to_le : ('a, strict, 'b) lt -> ('a, 's, 'b) lt
val le_plusomega : 'a t -> ('a, nonstrict, plus_omega) lt
val minusomega_le : 'a t -> (minus_omega, nonstrict, 'a) lt
val minusomega_lt_plusomega : (minus_omega, strict, plus_omega) lt
val zero_lt_plusomega : (zero, 's, plus_omega) lt
val minusomega_lt_zero : (minus_omega, 's, zero) lt

type (_, _, _) strict_trans =
  | Strict_any : (strict, 'a, 'b) strict_trans
  | Any_strict : ('a, strict, 'b) strict_trans
  | Nonstrict_nonstrict : (nonstrict, nonstrict, nonstrict) strict_trans

type (_, _) has_strict_trans =
  | Strict_trans : ('s1, 's2, 's3) strict_trans -> ('s1, 's2) has_strict_trans

val strict_trans : 's1 strictness -> 's2 strictness -> ('s1, 's2) has_strict_trans
val equal : 'a t -> 'b t -> ('a, 'b) Eq.compare
val equalb : 'a t -> 'b t -> bool

val lt_trans :
  ('s1, 's2, 's3) strict_trans -> ('a, 's1, 'b) lt -> ('b, 's2, 'c) lt -> ('a, 's3, 'c) lt

val lt_trans1 : ('a, 's1, 'b) lt -> ('b, 's2, 'c) lt -> ('a, 's1, 'c) lt
val compare : 's strictness -> 'a t -> 'b t -> ('a, 's, 'b) lt option
val to_rat : 'a t -> Q.t
val to_string : 'a t -> string

type wrapped = Wrap : 'a t -> wrapped

val of_rat : Q.t -> wrapped option

module Map : sig
  module Make : functor (F : Fam2) -> sig
    module Key : sig
      type nonrec 'a t = 'a t
    end

    include MAP with module Key := Key and module F := F

    type ('x, 'b) map_compare = {
      map_lt : 'a 's. ('a, strict, 'b) lt -> ('x, 'a) F.t -> ('x, 'a) F.t;
      map_gt : 'a 's. ('b, strict, 'a) lt -> ('x, 'a) F.t -> ('x, 'a) F.t;
      map_eq : ('x, 'b) F.t -> ('x, 'b) F.t;
    }

    val map_compare : ('x, 'b) map_compare -> 'b Key.t -> 'x t -> 'x t

    type ('x, 'a) upper =
      | Upper : ('a, strict, 'c) lt * ('x, 'c) F.t -> ('x, 'a) upper
      | No_upper : ('x, 'a) upper

    type ('x, 'a) lower =
      | Lower : ('b, strict, 'a) lt * ('x, 'b) F.t -> ('x, 'a) lower
      | No_lower : ('x, 'a) lower

    val add_cut : 'b Key.t -> (('x, 'b) lower -> ('x, 'b) upper -> ('x, 'b) F.t) -> 'x t -> 'x t
  end
end

type ('a, 's) iinterval = { strictness : 's strictness; endpoint : 'a t }
type interval = Interval : ('s, 'a) iinterval -> interval

module Interval : sig
  val empty : (plus_omega, strict) iinterval
  val entire : (minus_omega, nonstrict) iinterval
  val plus_omega_only : (plus_omega, nonstrict) iinterval
  val to_string : interval -> string
  val contains : ('a, 's) iinterval -> 'b t -> ('a, 's, 'b) lt option
  val union : interval -> interval -> interval

  type (_, _, _, _) subset =
    | Subset_strict : ('t2, strict, 't1) lt -> ('t1, 's1, 't2, 's2) subset
    | Subset_eq : ('t, 's, 't, 's) subset
    | Subset_nonstrict_strict : ('t, strict, 't, nonstrict) subset

  val subset_contains : ('t1, 's1, 't2, 's2) subset -> ('t1, 's1, 'a) lt -> ('t2, 's2, 'a) lt
end
