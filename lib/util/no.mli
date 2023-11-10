type zero
type 'a plus
type 'a minus
type minus_omega
type plus_omega
type _ t

val zero : zero t
val one : zero plus t
val minus_one : zero minus t
val two : zero plus plus t
val minus_two : zero minus minus t
val minus_omega : minus_omega t
val plus_omega : plus_omega t

type strict
type nonstrict
type _ strictness = Strict : strict strictness | Nonstrict : nonstrict strictness
type (_, _, _) lt

val le_refl : 'a t -> ('a, nonstrict, 'a) lt

type (_, _, _) strict_trans =
  | Strict_any : (strict, 'a, 'a) strict_trans
  | Any_strict : ('a, strict, 'a) strict_trans
  | Nonstrict_nonstrict : (nonstrict, nonstrict, nonstrict) strict_trans

val lt_trans :
  ('s1, 's2, 's3) strict_trans -> ('a, 's1, 'b) lt -> ('b, 's2, 'c) lt -> ('a, 's3, 'c) lt

val equal : 'a t -> 'b t -> ('a, 'b) Monoid.compare
val equalb : 'a t -> 'b t -> bool
val compare : 's strictness -> 'a t -> 'b t -> ('a, 's, 'b) lt option
val to_rat : 'a t -> Q.t
val to_string : 'a t -> string

type wrapped = Wrap : 'a t -> wrapped

val of_rat : Q.t -> wrapped option

module type Fam = sig
  type 'a t
end

module MapMake : functor (F : Fam) -> sig
  type 'a no = 'a t
  type t

  val empty : t
  val find : t -> 'a no -> 'a F.t option
  val add : 'a no -> 'a F.t -> t -> t
  val remove : t -> 'a no -> t
end
