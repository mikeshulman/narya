open Dim
open Core
open Notation
open Postprocess
open Unparse
open Format
open Uuseg_string
open Print
open Reporter

type t =
  | Axiom of {
      wsaxiom : Whitespace.t list;
      name : Scope.Trie.path;
      wsname : Whitespace.t list;
      wscolon : Whitespace.t list;
      ty : observation;
    }
  | Def of {
      wsdef : Whitespace.t list;
      name : Scope.Trie.path;
      wsname : Whitespace.t list;
      wscolon : Whitespace.t list;
      ty : observation;
      wscoloneq : Whitespace.t list;
      tm : observation;
    }
  | Echo of { wsecho : Whitespace.t list; tm : observation }
  | Bof of Whitespace.t list
  | Eof

let execute : t -> unit = function
  | Axiom { name; ty = Term ty; _ } ->
      if Option.is_some (Scope.lookup name) then
        emit (Constant_already_defined (String.concat "." name));
      let const = Scope.define name in
      Core.Command.execute (Axiom (const, process Emp ty));
      emit (Constant_assumed (PConstant const))
  | Def { name; ty = Term ty; tm = Term tm; _ } ->
      if Option.is_some (Scope.lookup name) then
        emit (Constant_already_defined (String.concat "." name));
      let const = Scope.define name in
      Core.Command.execute (Def (const, process Emp ty, process Emp tm));
      emit (Constant_defined (PConstant const))
  | Echo { tm = Term tm; _ } -> (
      let rtm = process Emp tm in
      match rtm.value with
      | Synth stm ->
          let ctm, ety = Check.synth Ctx.empty { value = stm; loc = rtm.loc } in
          let etm = Norm.eval (Emp D.zero) ctm in
          let btm = Readback.readback_at Ctx.empty etm ety in
          let utm = unparse Names.empty btm Interval.entire Interval.entire in
          pp_term `None Format.std_formatter (Term utm);
          Format.pp_print_newline Format.std_formatter ();
          Format.pp_print_newline Format.std_formatter ()
      | _ -> fatal (Nonsynthesizing "argument of echo"))
  | Bof _ -> ()
  | Eof -> fatal (Anomaly "EOF cannot be executed")

(* TODO: Comments that appear after a newline after a command ends should be attached to the *following* command instead. *)
let pp_command : formatter -> t -> Whitespace.t list =
 fun ppf cmd ->
  match cmd with
  | Axiom { wsaxiom; name; wsname; wscolon; ty = Term ty } ->
      pp_open_hvbox ppf 2;
      pp_tok ppf Axiom;
      pp_ws `Nobreak ppf wsaxiom;
      pp_utf_8 ppf (String.concat "." name);
      pp_ws `Break ppf wsname;
      pp_tok ppf Colon;
      pp_ws `Nobreak ppf wscolon;
      let ty, rest = split_ending_whitespace ty in
      pp_term `None ppf (Term ty);
      pp_close_box ppf ();
      rest
  | Def { wsdef; name; wsname; wscolon; ty; wscoloneq; tm = Term tm } ->
      pp_open_hvbox ppf 2;
      pp_tok ppf Def;
      pp_ws `Nobreak ppf wsdef;
      pp_utf_8 ppf (String.concat "." name);
      pp_ws `Break ppf wsname;
      pp_tok ppf Colon;
      pp_ws `Nobreak ppf wscolon;
      pp_term `Break ppf ty;
      pp_tok ppf Coloneq;
      pp_ws `Nobreak ppf wscoloneq;
      let tm, rest = split_ending_whitespace tm in
      pp_term `None ppf (Term tm);
      pp_close_box ppf ();
      rest
  | Echo { wsecho; tm } ->
      pp_open_hvbox ppf 2;
      pp_tok ppf Echo;
      pp_ws `Nobreak ppf wsecho;
      pp_term `None ppf tm;
      pp_close_box ppf ();
      []
  | Bof ws -> ws
  | Eof -> []
