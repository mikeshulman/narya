open Util

(* At both the checked and the value level we have actually three different types to define: ordinary terms, case trees, and let/match case trees to appear in let-bindings.  However, there is some overlap in the types of constructors and operations that these support.  Thus, to avoid duplication of code, we actually define all together as one GADT type family, indexed by a three-element type to distinguish them.  We name the two main groups after the two kinds of energy:

   - Ordinary terms are "kinetic", because ordinary computation applies directly to them.
   - Case trees are "potential", because they don't compute until enough arguments are applied to reach a leaf of the case tree.  That leaf can be either a kinetic term or information about a canonical type (which is not a computation, just a specification of behavior).
   - Let/match case trees are "chemical", a special kind of potential energy that's freed by breaking things apart (i.e. decomposing an element of a datatype into constructors, as with a match).
*)

type kinetic = private Dummy_kinetic
type potential = private Dummy_potential
type chemical = private Dummy_chemical

type _ energy =
  | Kinetic : kinetic energy
  | Potential : potential energy
  | Chemical : chemical energy

module Energy = struct
  type 'a t = 'a energy

  let compare : type a b. a t -> b t -> (a, b) Eq.compare =
   fun s1 s2 ->
    match (s1, s2) with
    | Kinetic, Kinetic -> Eq
    | Potential, Potential -> Eq
    | Chemical, Chemical -> Eq
    | _ -> Neq
end

(* Structs can have or lack eta-conversion, but the only kinetic or chemical ones are the ones with eta (records). *)
type _ eta = Eta : 's eta | Noeta : potential eta

(* The term bound by a kinetic let must be kinetic, while that bound by a potential or chemical let must be chemical. *)
type (_, _) lettable =
  | Kinetic : (kinetic, kinetic) lettable
  | Chemical : (chemical, chemical) lettable
  | Potential : (chemical, potential) lettable

(* Subclassifiers *)
type _ nonkinetic = Chemical : chemical nonkinetic | Potential : potential nonkinetic
type _ nonchemical = Kinetic : kinetic nonchemical | Potential : potential nonchemical
