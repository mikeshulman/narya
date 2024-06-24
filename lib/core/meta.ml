(* This module should not be opened, but used qualified. *)

open Util
open Signatures
open Dimbwd
open Energy

(* Metavariables, such as holes and unification variables.  Local generative definitions are also reperesented as metavariables.  A metavariable is identified by its class, an autonumber that's specific to the class, and the compilation unit it belongs to.  Since the autonumbers are specific to the class, we store them as arguments of the class, even though every metavariable has one. *)

module Identity = struct
  type t = [ `Hole of int | `Def of int * string * string option ]

  let compare : t -> t -> int = compare
end

(* A metavariable is also parametrized by its checked context length and its energy (kinetic or potential), although these are not part of its identity. *)
type ('b, 's) t = {
  compunit : Compunit.t;
  identity : Identity.t;
  len : 'b Dbwd.t;
  energy : 's energy;
}

(* Make metavariables of each class. *)

let def_counters = Compunit.IntArray.make_basic ()

let make_def : type b s. string -> string option -> b Dbwd.t -> s energy -> (b, s) t =
 fun sort name len energy ->
  let compunit = Compunit.Current.read () in
  let number = Compunit.IntArray.inc def_counters compunit in
  let identity = `Def (number, sort, name) in
  { compunit; identity; len; energy }

let hole_counters = Compunit.IntArray.make_basic ()

let make_hole : type b s. b Dbwd.t -> s energy -> (b, s) t =
 fun len energy ->
  let compunit = Compunit.Current.read () in
  let number = Compunit.IntArray.inc hole_counters compunit in
  let identity = `Hole number in
  { compunit; identity; len; energy }

(* Re-make (link) a metavariable when loading a compiled version from disk. *)
let remake : type b s. (Compunit.t -> Compunit.t) -> (b, s) t -> (b, s) t =
 fun f m -> { m with compunit = f m.compunit }

(* Printable names.  Doesn't include the compilation unit and is not re-parseable. *)
let name : type b s. (b, s) t -> string =
 fun x ->
  match x.identity with
  | `Hole number -> Printf.sprintf "?%d" number
  | `Def (number, sort, None) -> Printf.sprintf "_%s.%d" sort number
  | `Def (number, sort, Some name) -> Printf.sprintf "_%s.%d.%s" sort number name

(* Compare two metavariables for equality, returning equality of their lengths and energies. *)
let compare : type b1 s1 b2 s2. (b1, s1) t -> (b2, s2) t -> (b1 * s1, b2 * s2) Eq.compare =
 fun x y ->
  match
    ( x.compunit = y.compunit,
      x.identity = y.identity,
      Dbwd.compare x.len y.len,
      Energy.compare x.energy y.energy )
  with
  | true, true, Eq, Eq -> Eq
  | _ -> Neq

(* Hole numbers are exposed to the user for identifying them in solve commands, so we need to look them up and return a metavariable without already knowing its context length or energy. *)
type wrapped = Wrap : ('b, 's) t -> wrapped

let hole_number : type b s. (b, s) t -> int =
 fun { identity; _ } ->
  match identity with
  | `Hole number -> number
  | _ -> raise (Failure "not a hole")

(* Since metavariables are parametrized by context length and energy, an intrinsically well-typed map must incorporate those as well. *)

module IdMap = Map.Make (Identity)

type _ key = MetaKey : ('b, 's) t -> ('b * 's) key

module Key = struct
  type 'b t = 'b key
end

module Map = struct
  module Key = Key

  module Make (F : Fam2) = struct
    module EIMap = struct
      type ('b, 'g) t = {
        kinetic : ('b, 'g * kinetic) F.t IdMap.t;
        potential : ('b, 'g * potential) F.t IdMap.t;
      }

      let empty : ('b, 'g) t = { kinetic = IdMap.empty; potential = IdMap.empty }
    end

    module Map = DbwdMap.Make (EIMap)

    type 'b t = 'b Map.t Compunit.Map.t

    open Monad.Ops (Monad.Maybe)

    let empty : type b. b t = Compunit.Map.empty

    let find_opt : type b g. g Key.t -> b t -> (b, g) F.t option =
     fun key map ->
      let go : type b s g. s energy -> Identity.t -> (b, g) EIMap.t -> (b, g * s) F.t option =
       fun s i eimap ->
        match s with
        | Kinetic -> IdMap.find_opt i eimap.kinetic
        | Potential -> IdMap.find_opt i eimap.potential in
      let (MetaKey m) = key in
      let* map = Compunit.Map.find_opt m.compunit map in
      let* map = Map.find_opt m.len map in
      go m.energy m.identity map

    let update : type b g. g Key.t -> ((b, g) F.t option -> (b, g) F.t option) -> b t -> b t =
     fun key f map ->
      let go :
          type b s g.
          s energy ->
          Identity.t ->
          ((b, g * s) F.t option -> (b, g * s) F.t option) ->
          (b, g) EIMap.t ->
          (b, g) EIMap.t =
       fun s i f eimap ->
        match s with
        | Kinetic -> { eimap with kinetic = IdMap.update i f eimap.kinetic }
        | Potential -> { eimap with potential = IdMap.update i f eimap.potential } in
      let (MetaKey m) = key in
      Compunit.Map.update m.compunit
        (function
          | Some map ->
              Some
                (Map.update m.len
                   (function
                     | Some map -> Some (go m.energy m.identity f map)
                     | None -> Some (go m.energy m.identity f EIMap.empty))
                   map)
          | None ->
              Some
                (Map.update m.len
                   (function
                     | Some map -> Some (go m.energy m.identity f map)
                     | None -> Some (go m.energy m.identity f EIMap.empty))
                   Map.empty))
        map

    let add : type b g. g Key.t -> (b, g) F.t -> b t -> b t =
     fun key value map -> update key (fun _ -> Some value) map

    let remove : type b g. g Key.t -> b t -> b t = fun key map -> update key (fun _ -> None) map

    type 'a mapper = { map : 'g. ('a, 'g) F.t -> ('a, 'g) F.t }

    let map : type a. a mapper -> a t -> a t =
     fun f m ->
      Compunit.Map.map
        (fun x ->
          Map.map
            {
              map =
                (fun { kinetic; potential } ->
                  { kinetic = IdMap.map f.map kinetic; potential = IdMap.map f.map potential });
            }
            x)
        m

    let to_channel_unit :
        type b. Out_channel.t -> Compunit.t -> b t -> Marshal.extern_flags list -> unit =
     fun chan i map flags -> Marshal.to_channel chan (Compunit.Map.find_opt i map) flags

    let from_channel_unit : type b. In_channel.t -> b mapper -> Compunit.t -> b t -> b t =
     fun chan f i m ->
      match (Marshal.from_channel chan : b Map.t option) with
      | Some n ->
          Compunit.Map.add i
            (Map.map
               {
                 map =
                   (fun { kinetic; potential } ->
                     { kinetic = IdMap.map f.map kinetic; potential = IdMap.map f.map potential });
               }
               n)
            m
      | None -> m
  end
end
