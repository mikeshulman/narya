open Bwd
open Util
open Core
open Reporter
module Trie = Yuujinchou.Trie

(* Parameter module for Yuujinchou *)
module Param = struct
  type data = [ `Constant of Constant.t | `Notation of User.prenotation * User.notation ]

  (* Currently we have no nontrivial tags, hooks, or contexts. *)
  type tag = unit
  type hook = unit
  type context = unit
end

(* Modifier module for Yuujinchou *)
module Mod = struct
  include Yuujinchou.Modifier.Make (Param)

  (* We wrap the 'union' operations of Yuujinchou.Trie so that they merge by performing the modifier shadow effect, just as Scope does.  This is in the development version of Yuujinchou but hasn't been released yet. *)
  let union ?prefix ?context t1 t2 = Trie.union ?prefix (Perform.shadow context) t1 t2

  let union_subtree ?prefix ?context t1 pt2 =
    Trie.union_subtree ?prefix (Perform.shadow context) t1 pt2

  let union_singleton ?prefix ?context t1 (path, data) =
    Trie.union_singleton ?prefix (Perform.shadow context) t1 (path, data)

  let union_root ?prefix ?context t r = Trie.union_root ?prefix (Perform.shadow context) t r
end

let () =
  Mod.register_printer (function
    | `NotFound _ -> Some "unhandled Modifier.not_found effect"
    | `Shadow _ -> Some "unhandled Modifier.shadow effect"
    | `Hook _ -> Some "unhandled Modifier.hook effect")

(* Scope state: a visible namespace, an export namespace, and an export prefix. *)
type trie = (Param.data, Param.tag) Trie.t
type t = { visible : trie; export : trie; prefix : Trie.bwd_path }

module S = State.Make (struct
  type nonrec t = t
end)

let () =
  S.register_printer (function
    | `Get -> Some "unhandled Scope.get effect"
    | `Set _ -> Some "unhandled Scope.set effect")

let export_prefix () = (S.get ()).prefix

(* The following operations are copied from Yuujinchou.Scope, with the mutex removed since I don't think we need it. *)

let resolve p = Trie.find_singleton p (S.get ()).visible

let modify_visible ?context_visible m =
  S.modify @@ fun s ->
  { s with visible = Mod.modify ?context:context_visible ~prefix:Emp m s.visible }

let modify_export ?context_export m =
  S.modify @@ fun s ->
  { s with export = Mod.modify ?context:context_export ~prefix:(export_prefix ()) m s.export }

let export_visible ?context_modifier ?context_export m =
  S.modify @@ fun s ->
  {
    s with
    export =
      Mod.union ?context:context_export ~prefix:(export_prefix ()) s.export
      @@ Mod.modify ?context:context_modifier m s.visible;
  }

let include_singleton ?context_visible ?context_export (path, x) =
  S.modify @@ fun s ->
  {
    s with
    visible = Mod.union_singleton ?context:context_visible s.visible (path, x);
    export =
      Mod.union_singleton ?context:context_export ~prefix:(export_prefix ()) s.export (path, x);
  }

let import_singleton ?context_visible (path, x) =
  S.modify @@ fun s ->
  { s with visible = Mod.union_singleton ?context:context_visible s.visible (path, x) }

let include_subtree ?context_modifier ?context_visible ?context_export
    ?(modifier = Yuujinchou.Language.id) (path, ns) =
  S.modify @@ fun s ->
  let ns = Mod.modify ?context:context_modifier ~prefix:Emp modifier ns in
  {
    s with
    visible = Mod.union_subtree ?context:context_visible s.visible (path, ns);
    export = Mod.union_subtree ?context:context_export ~prefix:(export_prefix ()) s.export (path, ns);
  }

let import_subtree ?context_modifier ?context_visible ?(modifier = Yuujinchou.Language.id) (path, ns)
    =
  S.modify @@ fun s ->
  let ns = Mod.modify ?context:context_modifier ~prefix:Emp modifier ns in
  { s with visible = Mod.union_subtree ?context:context_visible s.visible (path, ns) }

let get_visible () = (S.get ()).visible
let get_export () = (S.get ()).export

(* We remove the Mod.run from Scope.run and let the caller control it separately. *)
let run ?(export_prefix = Emp) ?(init_visible = Trie.empty) f =
  let init = { visible = init_visible; export = Trie.empty; prefix = export_prefix } in
  S.run ~init f

(* Like 'run', but override the handlers for the scope state effects instead of running a state module; hence no init_visible is given.  Unlike most RedPRL try_with functions, this one isn't designed for calling *inside* of an outer "run" to override some things locally, instead it is for *replacing* "run" by passing out the state effects to our History module. *)
let try_with ?get ?set f = S.try_with ?get ?set f

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
let define compunit name =
  let c = Constant.make compunit in
  include_singleton (name, (`Constant c, ()));
  c

(* We currently allow names used for constants to be redefined by other constants.  But once a name is used for a notation, it can't be shadowed by a constant.  (And the name of a notation can't be anything used before, although that is checked elsewhere.) *)
let check_constant_name name =
  match resolve name with
  | Some (`Constant _, ()) -> emit (Name_already_defined (String.concat "." name))
  | Some (_, ()) ->
      fatal ~severity:Asai.Diagnostic.Error (Name_already_defined (String.concat "." name))
  | None -> ()
