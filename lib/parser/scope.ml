open Bwd
open Util
open Core
open Reporter
module Trie = Yuujinchou.Trie

(* Parameter module for Yuujinchou *)
module Param = struct
  type data =
    [ `Constant of Constant.t | `Notation of User.prenotation * User.notation ]
    * Asai.Range.t option

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

module M = Algaeff.Mutex.Make ()

exception Locked = M.Locked

(* Scope state: a visible namespace, an export namespace, an export prefix, and a set of configuration options. *)
type trie = (Param.data, Param.tag) Trie.t
type scope = { visible : trie; export : trie; prefix : Trie.bwd_path; options : Options.t }

(* A Scope.t has an inner scope and also maintains a stack of outer scopes. *)
type t = { outer : scope Bwd.t; inner : scope }

let empty : t =
  {
    outer = Emp;
    inner = { visible = Trie.empty; export = Trie.empty; prefix = Emp; options = Options.default };
  }

module S = State.Make (struct
  type nonrec t = t
end)

let () =
  S.register_printer (function
    | `Get -> Some "unhandled Scope.get effect"
    | `Set _ -> Some "unhandled Scope.set effect")

let export_prefix () = (S.get ()).inner.prefix

(* The following operations are copied from Yuujinchou.Scope, but acting only on the inner scope. *)

let resolve p = M.exclusively @@ fun () -> Trie.find_singleton p (S.get ()).inner.visible

let modify_visible ?context_visible m =
  M.exclusively @@ fun () ->
  S.modify @@ fun s ->
  {
    s with
    inner =
      { s.inner with visible = Mod.modify ?context:context_visible ~prefix:Emp m s.inner.visible };
  }

let modify_options f =
  M.exclusively @@ fun () ->
  S.modify @@ fun s -> { s with inner = { s.inner with options = f s.inner.options } }

let modify_export ?context_export m =
  M.exclusively @@ fun () ->
  S.modify @@ fun s ->
  {
    s with
    inner =
      {
        s.inner with
        export = Mod.modify ?context:context_export ~prefix:(export_prefix ()) m s.inner.export;
      };
  }

let export_visible ?context_modifier ?context_export m =
  M.exclusively @@ fun () ->
  S.modify @@ fun s ->
  {
    s with
    inner =
      {
        s.inner with
        export =
          Mod.union ?context:context_export ~prefix:(export_prefix ()) s.inner.export
          @@ Mod.modify ?context:context_modifier m s.inner.visible;
      };
  }

let include_singleton ?context_visible ?context_export (path, x) =
  M.exclusively @@ fun () ->
  S.modify @@ fun s ->
  {
    s with
    inner =
      {
        s.inner with
        visible = Mod.union_singleton ?context:context_visible s.inner.visible (path, x);
        export =
          Mod.union_singleton ?context:context_export ~prefix:(export_prefix ()) s.inner.export
            (path, x);
      };
  }

let import_singleton ?context_visible (path, x) =
  M.exclusively @@ fun () ->
  S.modify @@ fun s ->
  {
    s with
    inner =
      {
        s.inner with
        visible = Mod.union_singleton ?context:context_visible s.inner.visible (path, x);
      };
  }

let unsafe_include_subtree ?context_modifier ?context_visible ?context_export
    ?(modifier = Yuujinchou.Language.id) (path, ns) =
  S.modify @@ fun s ->
  let ns = Mod.modify ?context:context_modifier ~prefix:Emp modifier ns in
  {
    s with
    inner =
      {
        s.inner with
        visible = Mod.union_subtree ?context:context_visible s.inner.visible (path, ns);
        export =
          Mod.union_subtree ?context:context_export ~prefix:(export_prefix ()) s.inner.export
            (path, ns);
      };
  }

let include_subtree ?context_modifier ?context_visible ?context_export ?modifier (path, ns) =
  M.exclusively @@ fun () ->
  unsafe_include_subtree ?context_modifier ?context_visible ?context_export ?modifier (path, ns)

let import_subtree ?context_modifier ?context_visible ?(modifier = Yuujinchou.Language.id) (path, ns)
    =
  M.exclusively @@ fun () ->
  S.modify @@ fun s ->
  let ns = Mod.modify ?context:context_modifier ~prefix:Emp modifier ns in
  {
    s with
    inner =
      {
        s.inner with
        visible = Mod.union_subtree ?context:context_visible s.inner.visible (path, ns);
      };
  }

let get_visible () = M.exclusively @@ fun () -> (S.get ()).inner.visible
let get_export () = M.exclusively @@ fun () -> (S.get ()).inner.export
let get_options () = M.exclusively @@ fun () -> (S.get ()).inner.options

let () =
  (Implicitboundaries.forward_functions := fun () -> (get_options ()).function_boundaries);
  Implicitboundaries.forward_types := fun () -> (get_options ()).type_boundaries

(* Set the visible namespace, e.g. before going into interactive mode. *)
let set_visible visible =
  M.exclusively @@ fun () -> S.modify (fun s -> { s with inner = { s.inner with visible } })

(* Start a new section, with specified prefix. *)
let start_section prefix =
  M.exclusively @@ fun () ->
  S.modify (fun s ->
      let new_scope : scope =
        {
          visible = s.inner.visible;
          export = Trie.empty;
          prefix = Bwd.of_list prefix;
          options = s.inner.options;
        } in
      { outer = Snoc (s.outer, s.inner); inner = new_scope })

let count_sections () = M.exclusively @@ fun () -> Bwd.length (S.get ()).outer

(* Wrap up a section, integrating its exported names into the previous section's namespace with the prefix attached.  Returns the prefix that was used. *)
let end_section () =
  M.exclusively @@ fun () ->
  let ending_scope = (S.get ()).inner in
  try
    S.modify (fun s ->
        match s.outer with
        | Snoc (outer, inner) -> { outer; inner }
        | Emp -> raise (Failure "no section here to end"));
    unsafe_include_subtree (Bwd.to_list ending_scope.prefix, ending_scope.export);
    Some (Bwd.to_list ending_scope.prefix)
  with Failure _ -> None

(* We remove the Mod.run from Scope.run and let the caller control it separately. *)
let run ?(export_prefix = Emp) ?(init_visible = Trie.empty) ?(options = Options.default) f =
  let init =
    {
      outer = Emp;
      inner = { visible = init_visible; export = Trie.empty; prefix = export_prefix; options };
    } in
  M.run @@ fun () -> S.run ~init f

(* Like 'run', but override the handlers for the scope state effects instead of running a state module; hence no init_visible is given.  Unlike most RedPRL try_with functions, this one isn't designed for calling *inside* of an outer "run" to override some things locally, instead it is for *replacing* "run" by passing out the state effects to our History module.  Hence why it starts a new Mutex as well, and why we call it "run_with" instead of "try_with". *)
let run_with ?get ?set f = M.run @@ fun () -> S.try_with ?get ?set f

(* Look up a name to get a constant. *)
let lookup name =
  match resolve name with
  | Some ((`Constant c, _), ()) -> Some c
  | Some ((`Notation _, _), ()) -> None
  | None -> None

(* Backwards lookup of a constant to find its name. *)
let find_data trie x =
  Seq.find_map
    (fun (path, ((data, _), _)) -> if data = x then Some path else None)
    (Trie.to_seq trie)

let name_of c =
  match find_data (get_visible ()) (`Constant c) with
  | Some name -> name
  (* TODO: Better to munge the original name. *)
  | None -> [ "_UNNAMED_CONSTANT" ]

(* Create a new Constant.t and define a name to equal it. *)
let define compunit ?loc name =
  let c = Constant.make compunit in
  include_singleton (name, ((`Constant c, loc), ()));
  c

(* Ensure that a new name wouldn't shadow anything else *)
let check_name name loc =
  match resolve name with
  | Some ((_, oldloc), ()) ->
      let extra_remarks =
        match oldloc with
        | Some loc -> [ Asai.Diagnostic.loctext ~loc "previous definition" ]
        | None -> [] in
      fatal ?loc ~extra_remarks (Name_already_defined (String.concat "." name))
  | None -> ()
