(* This module should not be opened, but used qualified. *)

open Bwd
open Util
open Tbwd
open Reporter
open Term
open Status
open Printable

(* The global environment of constants and definition-local metavariables. *)

(* Each global constant either is an axiom or has a definition (a case tree).  The latter includes canonical types.  An axiom can be either parametric, which means it is always accessible, or nonparametric, which means it is not accessible behind context locks for external parametricity.  (In the future, this should be customizable on a per-direction basis.) *)
type definition = Axiom of [ `Parametric | `Nonparametric ] | Defined of (emp, potential) term

(* Global metavariables have only a definition (or an error indicating that they can't be correctly accessed, such as if typechecking failed earlier). *)
module Metamap = Meta.Map.Make (struct
  type ('x, 'a, 'b, 's) t = (('a, 'b, 's) Metadef.t, Code.t) Result.t
end)

type metamap = unit Metamap.t

type data = {
  constants : ((emp, kinetic) term * definition, Code.t) Result.t Constant.Map.t;
  metas : metamap;
  (* These two data pertain to the *currently executing command*: they store information about the holes and the global metavariables it has created.  The purpose is that if and when that command completes, we notify the user about the holes and save the metavariables to the correct global state.  In particular, during a "solve" command, the global state is rewound in time, but any newly created global metavariables need to be put into the "present" global state that it was rewound from. *)
  current_holes : (Meta.wrapped * printable * Asai.Range.t) Bwd.t;
  current_metas : metamap;
  (* These are the eternal holes that exist.  We store them so that when commands creating holes are undone, those holes can be discarded. *)
  holes : Meta.WrapSet.t;
}

(* The empty global state, as at the beginning of execution. *)
let empty : data =
  {
    constants = Constant.Map.empty;
    metas = Metamap.empty;
    current_holes = Emp;
    current_metas = Metamap.empty;
    holes = Meta.WrapSet.empty;
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
  match Constant.Map.find_opt c d.constants with
  | Some (Ok (ty, tm)) -> (ty, tm)
  | Some (Error e) -> fatal e
  | None -> fatal (Undefined_constant (PConstant c))

(* We need to make some calls to Eternity, which isn't defined until lib/parser, so we supply a ref here for Eternity to insert its callbacks. *)
type eternity = {
  find_opt : 'a 'b 's. ('a, 'b, 's) Meta.t -> ('a, 'b, 's) Metadef.t option;
  add :
    'a 'b 's.
    ('a, 'b, 's) Meta.t ->
    (string option, 'a) Bwv.t ->
    ('a, 'b) termctx ->
    ('b, kinetic) term ->
    ('b, 's) status ->
    No.interval option ->
    No.interval option ->
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
      match Metamap.find_opt m data.current_metas with
      | Some (Ok d) -> d
      (* If we find an error, we immediately raise it. *)
      | Some (Error e) -> fatal e
      | None -> (
          match Metamap.find_opt m data.metas with
          | Some (Ok d) -> d
          | Some (Error e) -> fatal e
          | None -> fatal (Anomaly ("undefined metavariable: " ^ Meta.name m))))

(* Marshal and unmarshal the constants and metavariables pertaining to a single compilation unit.  We ignore the "current" data because that is only relevant during typechecking commands, whereas this comes at the end of typechecking a whole file. *)

let to_channel_unit chan i flags =
  let d = S.get () in
  Constant.Map.to_channel_unit chan i d.constants flags;
  Metamap.to_channel_unit chan i d.metas flags

let link_definition f df =
  match df with
  | Axiom p -> Axiom p
  | Defined tm -> Defined (Link.term f tm)

type unit_entry =
  ((emp, kinetic) term * definition, Code.t) Result.t Constant.Map.unit_entry
  * unit Metamap.unit_entry

let find_unit i =
  let d = S.get () in
  (Constant.Map.find_unit i d.constants, Metamap.find_unit i d.metas)

let add_unit i (c, m) =
  let d = S.get () in
  let constants = Constant.Map.add_unit i c d.constants in
  let metas = Metamap.add_unit i m d.metas in
  S.set { d with constants; metas }

let from_channel_unit f chan i =
  let d = S.get () in
  let constants, new_constants =
    Constant.Map.from_channel_unit chan
      (Result.map (fun (tm, df) -> (Link.term f tm, link_definition f df)))
      i d.constants in
  let metas, new_metas =
    Metamap.from_channel_unit chan { map = (fun _ df -> Result.map (Link.metadef f) df) } i d.metas
  in
  S.set { d with constants; metas };
  (new_constants, new_metas)

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
  let tm = (tm :> [ `Defined of ('b, 's) term | `Axiom | `Undefined ]) in
  S.modify @@ fun d ->
  {
    d with
    current_metas =
      d.current_metas |> Metamap.add m (Ok { tm; termctx; ty; energy; li = None; ri = None });
  }

(* Set the definition of a Global metavariable, required to already exist but not be defined. *)
let set_meta m ~tm =
  S.modify @@ fun d ->
  {
    d with
    current_metas =
      d.current_metas
      |> Metamap.update m (function
           | Some (Ok d) -> Some (Ok { d with tm = `Defined tm })
           | _ -> raise (Failure "set_meta"));
  }

(* Given a map of meta definitions, save them to the permanent Global state.  This is done after a command finishes with the current_metas from this or some other global state. *)
let save_metas metas =
  Metamap.iter
    { it = (fun m def -> S.modify @@ fun d -> { d with metas = d.metas |> Metamap.add m def }) }
    metas

(* Since holes are not allowed inside all commands, we need to keep track of whether we're in a command that allows holes and check for it. *)
module HolesAllowed = Algaeff.Reader.Make (struct
  type t = (unit, [ `Command of string | `File of string ]) Result.t
end)

let () =
  HolesAllowed.register_printer (function `Read -> Some "unhandled HolesAllowed.read effect")

(* Add a new hole.  This is an eternal metavariable, so we pass off to Eternity, and also save some information about it locally so that we can discard it if the command errors (in interactive mode this doesn't stop the program) and notify the user if the command succeeds, and also discard it if this command is later undone. *)
let add_hole m loc ~vars ~termctx ~ty ~status ~li ~ri =
  match HolesAllowed.read () with
  | Ok () ->
      !eternity.add m vars termctx ty status (Some li) (Some ri);
      S.modify @@ fun d ->
      {
        d with
        current_holes = Snoc (d.current_holes, (Wrap m, PHole (vars, termctx, ty), loc));
        holes = Meta.WrapSet.add (Wrap m) d.holes;
      }
  | Error msg -> fatal (No_holes_allowed msg)

(* Check whether a hole exists in the current time. *)
let hole_exists : type a b s. (a, b, s) Meta.t -> bool =
 fun m -> Meta.WrapSet.mem (Wrap m) (S.get ()).holes

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
  | Some (Error _ as old) ->
      (* If the constant is currently unusable, we just retain that state. *)
      let result = f () in
      S.modify (fun d -> { d with constants = d.constants |> Constant.Map.add c old });
      result
  | _ -> fatal (Anomaly "missing definition in with_definition")

(* Similarly, temporarily set the value of a global metavariable, which could be either permanent or current. *)
let with_meta_definition m tm f =
  let d = S.get () in
  match Metamap.find_opt m d.metas with
  | Some (Ok olddf) ->
      S.set { d with metas = d.metas |> Metamap.add m (Ok (Metadef.define tm olddf)) };
      let result = f () in
      (* Note that f could change the state in other ways, so we can't just reset the whole state to d.  *)
      S.modify (fun d -> { d with metas = d.metas |> Metamap.add m (Ok olddf) });
      result
  | Some (Error _ as old) ->
      (* If the metavariable is currently unusable, we just retain that state. *)
      let result = f () in
      S.modify (fun d -> { d with metas = d.metas |> Metamap.add m old });
      result
  | _ -> (
      match Metamap.find_opt m d.current_metas with
      | Some (Ok olddf) ->
          S.set
            {
              d with
              current_metas = d.current_metas |> Metamap.add m (Ok (Metadef.define tm olddf));
            };
          let result = f () in
          (* Note that f could change the state in other ways, so we can't just reset the whole state to d.  *)
          S.modify (fun d -> { d with metas = d.metas |> Metamap.add m (Ok olddf) });
          result
      | _ ->
          (* If the metavariable isn't found, that means that when we created it we didn't have a type for it.  That, in turn, means that the user doesn't have a name for it, since the metavariable is only bound to a user name in a "let rec".  So we don't need to do anything. *)
          f ())

(* Temporarily set the value of a constant to produce an error, and restore it afterwards. *)
let without_definition c err f =
  let d = S.get () in
  match Constant.Map.find_opt c d.constants with
  | Some old ->
      S.set { d with constants = d.constants |> Constant.Map.add c (Error err) };
      let result = f () in
      (* Note that f could change the state in other ways, so we can't just reset the whole state to d.  *)
      S.modify (fun d -> { d with constants = d.constants |> Constant.Map.add c old });
      result
  | _ -> fatal (Anomaly "missing definition in without_definition")

(* Similarly, temporarily set the value of a global metavariable to produce an error. *)
let without_meta_definition m err f =
  let d = S.get () in
  match Metamap.find_opt m d.metas with
  | Some olddf ->
      S.set { d with metas = d.metas |> Metamap.add m (Error err) };
      let result = f () in
      (* Note that f could change the state in other ways, so we can't just reset the whole state to d.  *)
      S.modify (fun d -> { d with metas = d.metas |> Metamap.add m olddf });
      result
  | _ -> (
      match Metamap.find_opt m d.current_metas with
      | Some olddf ->
          S.set { d with current_metas = d.current_metas |> Metamap.add m (Error err) };
          let result = f () in
          (* Note that f could change the state in other ways, so we can't just reset the whole state to d.  *)
          S.modify (fun d -> { d with metas = d.metas |> Metamap.add m olddf });
          result
      | _ ->
          (* If the metavariable isn't found, that means that when we created it we didn't have a type for it.  That, in turn, means that the user doesn't have a name for it, since the metavariable is only bound to a user name in a "let rec".  So we don't need to do anything. *)
          f ())

(* Get the entire global state, for saving as part of the data for an eternal metavariable (hole) that is being created.  For this purpose, we throw away the current holes and merge the current metas into the permanent ones, since that gives the global state in which solutions to the hole will have to be checked. *)
let get () =
  let d = S.get () in
  let metas =
    Metamap.fold { fold = (fun m def metas -> Metamap.add m def metas) } d.current_metas d.metas
  in
  { d with current_holes = Emp; current_metas = Metamap.empty; metas }

(* Start with a specified global state.  This is used e.g. for going back in time and solving holes. *)
let run = S.run
let try_with = S.try_with

(* Store the hole number, starting position, and ending position of each newly created hole, to report to ProofGeneral. *)
module HoleState = struct
  type t = { holes : (int * int * int) Bwd.t; offset : int }
end

module HolePos = State.Make (HoleState)

let () =
  HolePos.register_printer (function
    | `Get -> Some "unhandled Global.HolePos get effect"
    | `Set _ -> Some "unhandled Global.HolePos set effect")

(* Notify the user about currently created holes and add them to the global list. *)
let do_holes make_msg =
  let d = S.get () in
  emit (make_msg (Bwd.length d.current_holes));
  Mbwd.miter
    (fun [ (Meta.Wrap m, p, (loc : Asai.Range.t)) ] ->
      (* We intentionally do not "locate" this emission, since we want to display only the hole context and type, not its location in the source. *)
      emit (Hole (Meta.name m, p));
      let s, e = Asai.Range.split loc in
      HolePos.modify (fun st ->
          { st with holes = Snoc (st.holes, (Meta.hole_number m, s.offset, e.offset)) }))
    [ d.current_holes ];
  d.current_metas

(* At the end of a succesful normal command, notify the user of generated holes and save the newly created metavariables. *)
let end_command make_msg =
  let metas = do_holes make_msg in
  save_metas metas;
  S.modify (fun d -> { d with current_holes = Emp; current_metas = Metamap.empty })

(* For a command that needs to run in a different state like Solve, wrap it in this function instead.  This does that, and then after it completes, it saves the newly created metavariables to the *old* global state, not the special one that the command ran in. *)
let run_command_with ~init make_msg f =
  let metas, result =
    run ~init @@ fun () ->
    let result = f () in
    let metas = do_holes make_msg in
    (metas, result) in
  (* Now that we're back in the old context, save the new metas to it. *)
  save_metas metas;
  result
