open Core
open User
module Trie = Yuujinchou.Trie

(* Parameter module for Yuujinchou *)
module P = struct
  type data = [ `Constant of Constant.t | `Notation of PrintKey.t * permuted_notation ]

  (* Currently we have no nontrivial tags, hooks, or contexts. *)
  type tag = unit
  type hook = unit
  type context = unit
end

(* Modifier module for Yuujinchou *)
module M = struct
  include Yuujinchou.Modifier.Make (P)

  (* We wrap the 'union' operations of Yuujinchou.Trie so that they merge by performing the modifier shadow effect, just as Scope does. *)
  let union ~prefix ?context_export t1 t2 = Trie.union ~prefix (Perform.shadow context_export) t1 t2

  let union_subtree ~prefix ?context_export t1 pt2 =
    Trie.union_subtree ~prefix (Perform.shadow context_export) t1 pt2

  let union_singleton ~prefix ?context_export t1 (path, const) =
    Trie.union_singleton ~prefix (Perform.shadow context_export) t1 (path, (const, ()))

  let union_root ~prefix ?context_export t r =
    Trie.union_root ~prefix (Perform.shadow context_export) t r
end

(* The Yuujinchou Scope instance, that manages a pair of import/export scopes with effects. *)
include Yuujinchou.Scope.Make (P)

(* Look up a name to get a constant. *)
let lookup name =
  match resolve name with
  | Some (`Constant c, ()) -> Some c
  | Some (`Notation _, ()) -> None
  | None -> None

(* Backwards lookup of a constant to find its name. *)
let find_data trie x =
  Seq.find_map (fun (path, (data, _)) -> if data = x then Some path else None) (Trie.to_seq trie)

let name_of c =
  match find_data (get_visible ()) (`Constant c) with
  | Some name -> name
  (* TODO: Better to munge the original name. *)
  | None -> [ "_UNNAMED_CONSTANT" ]

(* Create a new Constant.t and define a name to equal it. *)
let define name =
  let c = Constant.make () in
  include_singleton (name, (`Constant c, ()));
  c
