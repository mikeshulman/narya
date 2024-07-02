(* Module signatures for type-level (additive) monoids. *)

module type Monoid = sig
  (* The elements of the monoid are the types that satisfy this predicate. *)
  type 'a t

  val compare : 'a t -> 'b t -> ('a, 'b) Eq.compare

  (* Addition defined as a relation *)
  type ('a, 'b, 'c) plus

  (* To compute a sum, we wrap up the output in a GADT. *)
  type (_, _) has_plus = Plus : ('a, 'b, 'c) plus -> ('a, 'b) has_plus

  (* The conditions on which of these have to be assumed and which are deduced follows what happens for type-level natural numbers.  If we had other examples, we might have to be more flexible. *)
  val plus : 'b t -> ('a, 'b) has_plus
  val plus_right : ('a, 'b, 'c) plus -> 'b t
  val plus_left : ('m, 'n, 'mn) plus -> 'mn t -> 'm t
  val plus_out : 'a t -> ('a, 'b, 'c) plus -> 'c t

  (* Sums are unique *)
  val plus_uniq : ('a, 'b, 'c) plus -> ('a, 'b, 'd) plus -> ('c, 'd) Eq.t

  (* The unit element of the monoid is called zero *)
  type zero

  val zero : zero t
  val zero_plus : 'a t -> (zero, 'a, 'a) plus
  val plus_zero : 'a t -> ('a, zero, 'a) plus

  (* Addition is associative *)
  val plus_assocl :
    ('a, 'b, 'ab) plus -> ('b, 'c, 'bc) plus -> ('a, 'bc, 'abc) plus -> ('ab, 'c, 'abc) plus

  val plus_assocr :
    ('a, 'b, 'ab) plus -> ('b, 'c, 'bc) plus -> ('ab, 'c, 'abc) plus -> ('a, 'bc, 'abc) plus
end

(* Monoids with positivity (i.e. nonzero-ness) predicate *)

module type MonoidPos = sig
  include Monoid

  (* A subtype of elements of the monoid called "positive" *)
  type _ pos

  val pos : 'a pos -> 'a t

  (* Zero is not positive.  We assert this by explosion. *)
  val zero_nonpos : zero pos -> 'c

  (* Adding a positive element to anything remains positive. *)
  val plus_pos : 'a t -> 'b pos -> ('a, 'b, 'ab) plus -> 'ab pos
  val pos_plus : 'a pos -> ('a, 'b, 'ab) plus -> 'ab pos

  (* Everything is either zero or positive. *)
  type _ compare_zero = Zero : zero compare_zero | Pos : 'n pos -> 'n compare_zero

  val compare_zero : 'a t -> 'a compare_zero
end
