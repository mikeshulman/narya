(* This module should not be opened, but used qualified. *)

open Util
open Signatures
open Dimbwd
open Energy

(* Metavariables, such as holes and unification variables.  Local generative definitions are also reperesented as metavariables. *)

type sort = [ `Hole | `Def of string * string option ]

(* A metavariable has an autonumber identity, like a constant.  It also stores its sort, and is parametrized by its checked context length and its energy (kinetic or potential). *)
type ('b, 's) t = {
  compunit : Compunit.t;
  number : int;
  sort : sort;
  len : 'b Dbwd.t;
  energy : 's energy;
}

let counters = Compunit.IntArray.make_basic ()

let make : type b s. Compunit.t -> sort -> b Dbwd.t -> s energy -> (b, s) t =
 fun compunit sort len energy ->
  let number = Compunit.IntArray.inc counters compunit in
  { compunit; number; sort; len; energy }

let name : type b s. (b, s) t -> string =
 fun x ->
  match x.sort with
  | `Hole -> Printf.sprintf "?%d" x.number
  | `Def (sort, None) -> Printf.sprintf "_%s.%d" sort x.number
  | `Def (sort, Some name) -> Printf.sprintf "_%s.%d.%s" sort x.number name

let compare : type b1 s1 b2 s2. (b1, s1) t -> (b2, s2) t -> (b1 * s1, b2 * s2) Eq.compare =
 fun x y ->
  match
    ( x.number = y.number,
      x.sort = y.sort,
      Dbwd.compare x.len y.len,
      Energy.compare x.energy y.energy )
  with
  | true, true, Eq, Eq -> Eq
  | _ -> Neq

(* Since metavariables are parametrized by context length and energy, an intrinsically well-typed map must incorporate those as well. *)

module IntMap = Map.Make (Int)

type _ key = MetaKey : ('b, 's) t -> ('b * 's) key

module Key = struct
  type 'b t = 'b key
end

module Map = struct
  module Key = Key

  module Make (F : Fam2) = struct
    module EIMap = struct
      type ('b, 'g) t = {
        kinetic : ('b, 'g * kinetic) F.t IntMap.t;
        potential : ('b, 'g * potential) F.t IntMap.t;
      }

      let empty : ('b, 'g) t = { kinetic = IntMap.empty; potential = IntMap.empty }
    end

    module Map = DbwdMap.Make (EIMap)

    type 'b t = 'b Map.t Compunit.Map.t

    open Monad.Ops (Monad.Maybe)

    let empty : type b. b t = Compunit.Map.empty

    let find_opt : type b g. g Key.t -> b t -> (b, g) F.t option =
     fun key map ->
      let go : type b s g. s energy -> int -> (b, g) EIMap.t -> (b, g * s) F.t option =
       fun s i eimap ->
        match s with
        | Kinetic -> IntMap.find_opt i eimap.kinetic
        | Potential -> IntMap.find_opt i eimap.potential in
      let (MetaKey m) = key in
      let* map = Compunit.Map.find_opt m.compunit map in
      let* map = Map.find_opt m.len map in
      go m.energy m.number map

    let update : type b g. g Key.t -> ((b, g) F.t option -> (b, g) F.t option) -> b t -> b t =
     fun key f map ->
      let go :
          type b s g.
          s energy ->
          int ->
          ((b, g * s) F.t option -> (b, g * s) F.t option) ->
          (b, g) EIMap.t ->
          (b, g) EIMap.t =
       fun s i f eimap ->
        match s with
        | Kinetic -> { eimap with kinetic = IntMap.update i f eimap.kinetic }
        | Potential -> { eimap with potential = IntMap.update i f eimap.potential } in
      let (MetaKey m) = key in
      Compunit.Map.update m.compunit
        (function
          | Some map ->
              Some
                (Map.update m.len
                   (function
                     | Some map -> Some (go m.energy m.number f map)
                     | None -> Some (go m.energy m.number f EIMap.empty))
                   map)
          | None ->
              Some
                (Map.update m.len
                   (function
                     | Some map -> Some (go m.energy m.number f map)
                     | None -> Some (go m.energy m.number f EIMap.empty))
                   Map.empty))
        map

    let add : type b g. g Key.t -> (b, g) F.t -> b t -> b t =
     fun key value map -> update key (fun _ -> Some value) map

    let remove : type b g. g Key.t -> b t -> b t = fun key map -> update key (fun _ -> None) map
  end
end
