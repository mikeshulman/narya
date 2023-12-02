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
val lt_to_le : ('a, strict, 'b) lt -> ('a, 's, 'b) lt

type (_, _, _) strict_trans =
  | Strict_any : (strict, 'a, 'a) strict_trans
  | Any_strict : ('a, strict, 'a) strict_trans
  | Nonstrict_nonstrict : (nonstrict, nonstrict, nonstrict) strict_trans

val equal : 'a t -> 'b t -> ('a, 'b) Monoid.compare
val equalb : 'a t -> 'b t -> bool

val lt_trans :
  ('s1, 's2, 's3) strict_trans -> ('a, 's1, 'b) lt -> ('b, 's2, 'c) lt -> ('a, 's3, 'c) lt

val lt_trans1 : ('a, 's1, 'b) lt -> ('b, 's2, 'c) lt -> ('a, 's1, 'c) lt
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
  val remove : 'a no -> t -> t

  type 'b map_le = { map : 'a 's. ('a, 's, 'b) lt -> 's strictness -> 'a F.t -> 'a F.t }

  val map_le : 'b map_le -> 'b no -> t -> t

  type 'a upper = Upper : ('a, strict, 'c) lt * 'c F.t -> 'a upper | No_upper : 'a upper
  type 'a lower = Lower : ('b, strict, 'a) lt * 'b F.t -> 'a lower | No_lower : 'a lower

  val add_cut : 'b no -> ('b lower -> 'b upper -> 'b F.t) -> t -> t
end
