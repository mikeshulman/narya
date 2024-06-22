(* This module should not be opened, but be used qualified. *)

(* A compilation unit is identified by an autonumber. *)
module Compunit = struct
  type t = int

  let compare : t -> t -> int = compare
end

type t = Compunit.t

let counter = ref 0
let by_file : (string, t) Hashtbl.t = Hashtbl.create 20

(* The zeroth compilation unit includes predefined constants as well as those from command-line exec strings, stdin, and interactive mode. *)
let basic : t = 0

let make file : t =
  counter := !counter + 1;
  Hashtbl.add by_file file !counter;
  !counter

let get file = Hashtbl.find by_file file

(* Constants and metavariables are identified by their compilation unit together with another autonumber.  We can store those autonumber counters in dynamic arrays, since compilation units are integers and can be used as array indices.  To avoid exposing the definition of Compunit.t as int outside this module, we expose a dynamic array module that does just what we need. *)
module IntArray = struct
  type t = int Dynarray.t

  let make_basic () = Dynarray.make 1 (-1)
  let get a i = Dynarray.get a i

  let inc a i =
    (if i >= Dynarray.length a then
       let k = i - Dynarray.length a + 1 in
       Dynarray.append_seq a (Seq.init k (fun _ -> -1)));
    Dynarray.set a i (Dynarray.get a i + 1);
    Dynarray.get a i
end

module Map = Map.Make (Compunit)

(* The current compilation unit, used for creating new constants and metavariables, is exposed through a reader effect. *)
module Current = Algaeff.Reader.Make (Compunit)
