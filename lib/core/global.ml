(* This module should not be opened, but used qualified. *)

open Bwd
open Util
open Tbwd
open Reporter
open Syntax
open Term
open Status

(* The global environment of constants and definition-local metavariables. *)

(* Each global constant either is an axiom or has a definition (a case tree).  The latter includes canonical types.  An axiom can be either parametric, which means it is always accessible, or nonparametric, which means it is not accessible behind context locks for external parametricity.  (In the future, this should be customizable on a per-direction basis.) *)
type definition = Axiom of [ `Parametric | `Nonparametric ] | Defined of (emp, potential) term

(* All global metavariables have definitions. *)
module Metamap = Meta.Map.Make (struct
  type ('x, 'bs) t = ('x, 'bs) Metadef.t
end)

type metamap = Metadef.def Metamap.t

type data = {
  constants : ((emp, kinetic) term * definition, Code.t) Result.t Constant.Map.t;
  metas : metamap;
  locked : bool;
  (* These two data pertain to the *currently executing command*: they store information about the holes and the global metavariables it has created.  The purpose is that if and when that command completes, we notify the user about the holes and save the metavariables to the correct global state.  In particular, during a "solve" command, the global state is rewound in time, but any newly created global metavariables need to be put into the "present" global state that it was rewound from. *)
  current_holes : (Meta.wrapped * printable) Bwd.t;
  current_metas : metamap;
}

(* The empty global state, as at the beginning of execution. *)
let empty : data =
  {
    constants = Constant.Map.empty;
    metas = Metamap.empty;
    locked = false;
    current_holes = Emp;
    current_metas = Metamap.empty;
  }

module S = State.Make (struct
  type t = data
end)

let () =
  S.register_printer (function
    | `Get -> Some "unhandled Global get effect"
    | `Set _ -> Some "unhandled Global set effect")

(* Look up a constant. *)
let find c =
  let d = S.get () in
  match (Constant.Map.find_opt c d.constants, d.locked) with
  | Some (Ok (_, Axiom `Nonparametric)), true -> fatal (Locked_axiom (PConstant c))
  | Some (Ok (ty, tm)), _ -> (ty, tm)
  | Some (Error e), _ -> fatal e
  | None, _ -> fatal (Undefined_constant (PConstant c))

(* We need to make some calls to Eternity, which isn't defined until lib/parser, so we supply a ref here for Eternity to insert its callbacks. *)
type eternity = {
  find_opt : 'b 's. ('b, 's) Meta.t -> ('b, 's) Metadef.wrapped option;
  add :
    'a 'b 's.
    ('b, 's) Meta.t ->
    (string option, 'a) Bwv.t ->
    ('a, 'b) Termctx.t ->
    ('b, kinetic) term ->
    ('b, 's) status ->
    unit;
}

let eternity : eternity ref =
  ref
    {
      find_opt = (fun _ -> raise (Failure "eternity not set"));
      add = (fun _ _ _ _ _ -> raise (Failure "eternity not set"));
    }

(* When looking up a metavariable, we check both Eternity, the new globals, and the old globals. *)
let find_meta m =
  match !eternity.find_opt m with
  | Some d -> d
  | None -> (
      let data = S.get () in
      match Metamap.find_opt (MetaKey m) data.current_metas with
      | Some d -> Metadef.Wrap d
      | None -> (
          match Metamap.find_opt (MetaKey m) data.metas with
          | Some d -> Metadef.Wrap d
          | None -> fatal (Anomaly "undefined metavariable")))

(* Marshal and unmarshal the constants and metavariables pertaining to a single compilation unit.  We ignore the "current" data because that is only relevant during typechecking commands, whereas this comes at the end of typechecking a whole file. *)

let to_channel_unit chan i flags =
  let d = S.get () in
  Constant.Map.to_channel_unit chan i d.constants flags;
  Metamap.to_channel_unit chan i d.metas flags

let from_channel_unit f chan i =
  let d = S.get () in
  let constants =
    Constant.Map.from_channel_unit chan
      (Result.map (fun (tm, df) -> (Link.term f tm, df)))
      i d.constants in
  let metas = Metamap.from_channel_unit chan { map = (fun _ df -> Link.metadef f df) } i d.metas in
  S.set { d with constants; metas }

(* Look up whether the state is locked. *)
let locked () = (S.get ()).locked

(* Add a new constant. *)
let add c ty df =
  S.modify @@ fun d -> { d with constants = d.constants |> Constant.Map.add c (Ok (ty, df)) }

(* Set the definition of an already-defined constant. *)
let set c df =
  S.modify @@ fun d ->
  {
    d with
    constants =
      d.constants
      |> Constant.Map.update c (function
           | Some (Ok (ty, _)) -> Some (Ok (ty, df))
           | _ -> raise (Failure "Global.set"));
  }

(* Add a new constant, but make it an error to access it. *)
let add_error c e =
  S.modify @@ fun d -> { d with constants = d.constants |> Constant.Map.add c (Error e) }

(* Add a new Global metavariable (e.g. local let-definition) to the new metas associated to the current command. *)
let add_meta m ~termctx ~ty ~tm ~energy =
  S.modify @@ fun d ->
  {
    d with
    current_metas =
      d.current_metas
      |> Metamap.add (MetaKey m) (Metadef { data = Def_meta { tm; energy }; termctx; ty });
  }

(* Set the definition of a Global metavariable, required to already exist. *)
let set_meta m ~tm =
  S.modify @@ fun d ->
  {
    d with
    current_metas =
      d.current_metas
      |> Metamap.update (MetaKey m) (function
           | Some (Metadef ({ data = Def_meta df; _ } as d)) ->
               Some (Metadef { d with data = Def_meta { df with tm } })
           | _ -> raise (Failure "set_meta"));
  }

(* Given a map of meta definitions, save them to the permanent Global state.  This is done after a command finishes with the current_metas from this or some other global state. *)
let save_metas metas =
  Metamap.iter
    { it = (fun m def -> S.modify @@ fun d -> { d with metas = d.metas |> Metamap.add m def }) }
    metas

(* Add a new hole.  This is an eternal metavariable, so we pass off to Eternity, and also save some information about it locally so that we can discard it if the command errors (in interactive mode this doesn't stop the program) and notify the user if the command succeeds. *)
let add_hole m ~vars ~termctx ~ty ~status =
  !eternity.add m vars termctx ty status;
  S.modify (fun d ->
      { d with current_holes = Snoc (d.current_holes, (Wrap m, Termctx.PHole (vars, termctx, ty))) })

(* Temporarily set the value of a constant to execute a callback, and restore it afterwards.  We implement this by saving and restoring the value, rather that by calling another S.run, because we want to make sure to keep the 'current' information created by the callback. *)
let with_definition c df f =
  let d = S.get () in
  match Constant.Map.find_opt c d.constants with
  | Some (Ok (ty, _) as old) ->
      S.set { d with constants = d.constants |> Constant.Map.add c (Ok (ty, df)) };
      let result = f () in
      (* Note that f could change the state in other ways, so we can't just reset the whole state to d.  *)
      S.modify (fun d -> { d with constants = d.constants |> Constant.Map.add c old });
      result
  | _ -> fatal (Anomaly "missing definition in with_definition")

(* Similarly, temporarily set the value of a global metavariable, which could be either permanent or current. *)
let with_meta_definition m tm f =
  let d = S.get () in
  let m = Meta.MetaKey m in
  match Metamap.find_opt m d.metas with
  | Some olddf ->
      S.set { d with metas = d.metas |> Metamap.add m (Metadef.define tm olddf) };
      let result = f () in
      (* Note that f could change the state in other ways, so we can't just reset the whole state to d.  *)
      S.modify (fun d -> { d with metas = d.metas |> Metamap.add m olddf });
      result
  | _ -> (
      match Metamap.find_opt m d.current_metas with
      | Some olddf ->
          S.set
            { d with current_metas = d.current_metas |> Metamap.add m (Metadef.define tm olddf) };
          let result = f () in
          (* Note that f could change the state in other ways, so we can't just reset the whole state to d.  *)
          S.modify (fun d -> { d with metas = d.metas |> Metamap.add m olddf });
          result
      | _ ->
          (* If the metavariable isn't found, that means that when we created it we didn't have a type for it.  That, in turn, means that the user doesn't have a name for it, since the metavariable is only bound to a user name in a "let rec".  So we don't need to do anything. *)
          f ())

(* Temporarily set the locked flag. *)
let with_locked f =
  let d = S.get () in
  let old = d.locked in
  S.set { d with locked = true };
  let result = f () in
  (* Note that f could change the state in other ways, so we can't just reset the whole state to d.  *)
  S.modify (fun d -> { d with locked = old });
  result

(* Get the entire global state, for saving as part of the data for an eternal metavariable (hole) that is being created.  For this purpose, we throw away the current holes and merge the current metas into the permanent ones, since that gives the global state in which solutions to the hole will have to be checked. *)
let get () =
  let d = S.get () in
  (* TODO: We need fold for intrinsically well-typed maps. *)
  let metas = ref d.metas in
  Metamap.iter { it = (fun m def -> metas := !metas |> Metamap.add m def) } d.current_metas;
  { d with current_holes = Emp; current_metas = Metamap.empty; metas = !metas }

(* Start with a specified global state.  This is used e.g. for going back in time and solving holes. *)
let run = S.run
let try_with = S.try_with

(* At the end of a succesful normal command, notify the user of generated holes, save the newly created metavariables, and return the number of holes created to notify the user of. *)
let end_command make_msg =
  let d = S.get () in
  emit (make_msg (Bwd.length d.current_holes));
  Mbwd.miter (fun [ (Meta.Wrap m, p) ] -> emit (Hole (Meta.name m, p))) [ d.current_holes ];
  save_metas d.current_metas;
  S.modify (fun d -> { d with current_holes = Emp; current_metas = Metamap.empty })

(* For a command that needs to run in a different state like Solve, wrap it in this function instead.  This does that, and then after it completes, it saves the newly created metavariables to the *old* global state, not the special one that the command ran in. *)
let run_command_with ~init make_msg f =
  let metas, result =
    run ~init @@ fun () ->
    let result = f () in
    let d = S.get () in
    emit (make_msg (Bwd.length d.current_holes));
    Mbwd.miter (fun [ (Meta.Wrap m, p) ] -> emit (Hole (Meta.name m, p))) [ d.current_holes ];
    (d.current_metas, result) in
  (* Now that we're back in the old context, save the new metas to it. *)
  save_metas metas;
  result
