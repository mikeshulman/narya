module type Fam = sig
  type 'g t
end

module type Fam2 = sig
  type ('b, 'g) t
end

module type Fam3 = sig
  type ('a, 'b, 'c) t
end

module type Fam4 = sig
  type ('a, 'b, 'c, 'd) t
end

(* We deal with several kinds of intrinsically well-typed maps, whose output type depends on their input value (which is a type).  They all share this common signature. *)

module type MAP = sig
  module Key : Fam
  module F : Fam2

  type 'b t

  val empty : 'b t
  val find_opt : 'g Key.t -> 'b t -> ('b, 'g) F.t option
  val add : 'g Key.t -> ('b, 'g) F.t -> 'b t -> 'b t
  val update : 'g Key.t -> (('b, 'g) F.t option -> ('b, 'g) F.t option) -> 'b t -> 'b t
  val remove : 'g Key.t -> 'b t -> 'b t
end

module type MAP_MAKER = sig
  module Key : Fam
  module Make : functor (F : Fam2) -> MAP with module Key := Key and module F := F
end
