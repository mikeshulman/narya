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
  | Axiom of Scope.Trie.path * observation
  | Def of Scope.Trie.path * observation * observation
  | Echo of observation
  | Eof

let execute : t -> unit = function
  | Axiom (name, Term ty) ->
      let const = Scope.define name in
      if Hashtbl.mem Global.types const then fatal (Constant_already_defined (PConstant const))
      else Core.Command.execute (Axiom (const, process Emp ty));
      emit (Constant_assumed (PConstant const))
  | Def (name, Term ty, Term tm) ->
      let const = Scope.define name in
      if Hashtbl.mem Global.types const then fatal (Constant_already_defined (PConstant const))
      else Core.Command.execute (Def (const, process Emp ty, process Emp tm));
      emit (Constant_defined (PConstant const))
  | Echo (Term tm) -> (
      let rtm = process Emp tm in
      match rtm with
      | Synth rtm ->
          let ctm, ety = Check.synth Ctx.empty rtm in
          let etm = Norm.eval (Emp D.zero) ctm in
          let btm = Readback.readback_at Ctx.empty etm ety in
          let utm = unparse Names.empty btm Interval.entire Interval.entire in
          pp_term Format.std_formatter (Term utm);
          Format.pp_print_newline Format.std_formatter ();
          Format.pp_print_newline Format.std_formatter ()
      | _ -> fatal (Nonsynthesizing "argument of echo"))
  | Eof -> fatal (Anomaly "EOF cannot be executed")

let pp_command : formatter -> t -> unit =
 fun ppf cmd ->
  match cmd with
  (* TODO: Incorporate whitespace/comments *)
  | Axiom (name, ty) ->
      pp_open_hvbox ppf 2;
      pp_tok ppf Axiom;
      pp_print_string ppf " ";
      pp_utf_8 ppf (String.concat "." name);
      pp_print_space ppf ();
      pp_tok ppf Colon;
      pp_print_string ppf " ";
      pp_term ppf ty;
      pp_close_box ppf ()
  | Def (name, ty, tm) ->
      pp_open_hvbox ppf 2;
      pp_tok ppf Def;
      pp_print_string ppf " ";
      pp_utf_8 ppf (String.concat "." name);
      pp_print_space ppf ();
      pp_tok ppf Colon;
      pp_print_string ppf " ";
      pp_term ppf ty;
      pp_print_space ppf ();
      pp_tok ppf Coloneq;
      pp_print_string ppf " ";
      pp_term ppf tm;
      pp_close_box ppf ()
  | Echo tm ->
      pp_open_hvbox ppf 2;
      pp_tok ppf Echo;
      pp_print_string ppf " ";
      pp_term ppf tm;
      pp_close_box ppf ()
  | Eof -> ()
