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
type ('a, 'b, 's) t = {
  compunit : Compunit.t;
  identity : Identity.t;
  raw : 'a N.t;
  len : 'b Dbwd.t;
  energy : 's energy;
}

(* Make metavariables of each class. *)

let def_counters = Compunit.IntArray.make_basic ()

let make_def : type a b s. string -> string option -> a N.t -> b Dbwd.t -> s energy -> (a, b, s) t =
 fun sort name raw len energy ->
  let compunit = Compunit.Current.read () in
  let number = Compunit.IntArray.inc def_counters compunit in
  let identity = `Def (number, sort, name) in
  { compunit; identity; raw; len; energy }

let hole_counters = Compunit.IntArray.make_basic ()

let make_hole : type a b s. a N.t -> b Dbwd.t -> s energy -> (a, b, s) t =
 fun raw len energy ->
  let compunit = Compunit.Current.read () in
  let number = Compunit.IntArray.inc hole_counters compunit in
  let identity = `Hole number in
  { compunit; identity; raw; len; energy }

(* Re-make (link) a metavariable when loading a compiled version from disk. *)
let remake : type a b s. (Compunit.t -> Compunit.t) -> (a, b, s) t -> (a, b, s) t =
 fun f m -> { m with compunit = f m.compunit }

(* Printable names.  Doesn't include the compilation unit and is not re-parseable. *)
let name : type a b s. (a, b, s) t -> string =
 fun x ->
  match x.identity with
  | `Hole number -> Printf.sprintf "?%d" number
  | `Def (number, sort, None) -> Printf.sprintf "_%s.%d" sort number
  | `Def (number, sort, Some name) -> Printf.sprintf "_%s.%d.%s" sort number name

(* Compare two metavariables for equality, returning equality of their lengths and energies. *)
let compare : type a1 b1 s1 a2 b2 s2.
    (a1, b1, s1) t -> (a2, b2, s2) t -> (a1 * b1 * s1, a2 * b2 * s2) Eq.compare =
 fun x y ->
  match
    ( x.compunit = y.compunit,
      x.identity = y.identity,
      N.compare x.raw y.raw,
      Dbwd.compare x.len y.len,
      Energy.compare x.energy y.energy )
  with
  | true, true, Eq, Eq, Eq -> Eq
  | _ -> Neq

type wrapped = Wrap : ('a, 'b, 's) t -> wrapped

module Wrapped = struct
  type t = wrapped

  let compare : t -> t -> int = fun (Wrap x) (Wrap y) -> Identity.compare x.identity y.identity
end

module WrapSet = Set.Make (Wrapped)

(* Note that this doesn't give the compunit, whereas hole numbers are only unique within a compunit.  But holes are probably only used in the top level compunit, and in general we can assume this is only used for just-created holes hence in the "current" compunit. *)
let hole_number : type a b s. (a, b, s) t -> int =
 fun { identity; _ } ->
  match identity with
  | `Hole number -> number
  | _ -> raise (Failure "not a hole")

(* Since metavariables are parametrized by context length and energy, an intrinsically well-typed map must incorporate those as well.  Since this is triply parametrized, it is not technically an instance of our "intrinsically well-typed maps" from Signatures. *)

module IdMap = Map.Make (Identity)

module Map = struct
  type ('a, 'b, 's) key = ('a, 'b, 's) t

  module Make (F : Fam4) = struct
    type _ entry = Entry : ('a, 'b, 's) key * ('x, 'a, 'b, 's) F.t -> 'x entry
    type 'x t = 'x entry IdMap.t Compunit.Map.t

    let empty : type x. x t = Compunit.Map.empty

    let find_opt : type x a b s. (a, b, s) key -> x t -> (x, a, b, s) F.t option =
     fun key m ->
      match Compunit.Map.find_opt key.compunit m with
      | Some m -> (
          match IdMap.find_opt key.identity m with
          | None -> None
          | Some (Entry (key', value)) -> (
              match compare key key' with
              | Eq -> Some value
              | Neq -> raise (Failure "Meta.Map.find_opt")))
      | None -> None

    let find_hole_opt : type x. Compunit.t -> int -> x t -> x entry option =
     fun c i m ->
      match Compunit.Map.find_opt c m with
      | Some m -> IdMap.find_opt (`Hole i) m
      | None -> None

    let update : type x a b s.
        (a, b, s) key -> ((x, a, b, s) F.t option -> (x, a, b, s) F.t option) -> x t -> x t =
     fun key f m ->
      Compunit.Map.update key.compunit
        (fun m ->
          let m = Option.value ~default:IdMap.empty m in
          Some
            (IdMap.update key.identity
               (function
                 | None -> (
                     match f None with
                     | None -> None
                     | Some fx -> Some (Entry (key, fx)))
                 | Some (Entry (key', value)) -> (
                     match compare key key' with
                     | Eq -> (
                         match f (Some value) with
                         | None -> None
                         | Some fx -> Some (Entry (key, fx)))
                     | Neq -> raise (Failure "Meta.Map.update")))
               m))
        m

    let add : type x a b s. (a, b, s) key -> (x, a, b, s) F.t -> x t -> x t =
     fun key value m -> update key (fun _ -> Some value) m

    let remove : type x a b s. (a, b, s) key -> x t -> x t =
     fun key m -> update key (fun _ -> None) m

    type 'x mapper = {
      map : 'a 'b 's. ('a, 'b, 's) key -> ('x, 'a, 'b, 's) F.t -> ('x, 'a, 'b, 's) F.t;
    }

    let map : type x. x mapper -> x t -> x t =
     fun f m ->
      Compunit.Map.map
        (fun m -> IdMap.map (fun (Entry (key, value)) -> Entry (key, f.map key value)) m)
        m

    type 'x iterator = { it : 'a 'b 's. ('a, 'b, 's) key -> ('x, 'a, 'b, 's) F.t -> unit }

    let iter : type x. x iterator -> x t -> unit =
     fun f m ->
      Compunit.Map.iter (fun _ m -> IdMap.iter (fun _ (Entry (key, value)) -> f.it key value) m) m

    type ('x, 'acc) folder = {
      fold : 'a 'b 's. ('a, 'b, 's) key -> ('x, 'a, 'b, 's) F.t -> 'acc -> 'acc;
    }

    let fold : type x acc. (x, acc) folder -> x t -> acc -> acc =
     fun f m acc ->
      Compunit.Map.fold
        (fun _ m acc -> IdMap.fold (fun _ (Entry (key, value)) acc -> f.fold key value acc) m acc)
        m acc

    type 'x filterer = { filter : 'a 'b 's. ('a, 'b, 's) key -> ('x, 'a, 'b, 's) F.t -> bool }

    let filter : type x. x filterer -> x t -> x t =
     fun f m ->
      Compunit.Map.map
        (fun m -> IdMap.filter (fun _ (Entry (key, value)) -> f.filter key value) m)
        m

    let to_channel_unit : type x.
        Out_channel.t -> Compunit.t -> x t -> Marshal.extern_flags list -> unit =
     fun chan i m flags -> Marshal.to_channel chan (Compunit.Map.find_opt i m) flags

    type 'x unit_entry = 'x entry IdMap.t option

    let find_unit i m = Compunit.Map.find_opt i m

    let add_unit i x m =
      match x with
      | Some x -> Compunit.Map.add i x m
      | None -> m

    let from_channel_unit : type x.
        In_channel.t -> x mapper -> Compunit.t -> x t -> x t * x unit_entry =
     fun chan f compunit m ->
      match (Marshal.from_channel chan : x entry IdMap.t option) with
      | Some n ->
          let fn = IdMap.map (fun (Entry (key, value)) -> Entry (key, f.map key value)) n in
          (Compunit.Map.add compunit fn m, Some fn)
      | None -> (m, None)
  end
end
