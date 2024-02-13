open Dim
open Util
open List_extra
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
  | Notation : {
      fixity : ('left, 'tight, 'right) fixity;
      wsnotation : Whitespace.t list;
      wstight : Whitespace.t list; (* Empty for outfix *)
      wsellipsis : Whitespace.t list; (* Empty for non-associative *)
      name : Scope.Trie.path;
      wsname : Whitespace.t list;
      wscolon : Whitespace.t list;
      pattern : State.pattern;
      wscoloneq : Whitespace.t list;
      head : [ `Constr of string | `Constant of Scope.Trie.path ];
      wshead : Whitespace.t list;
      args : (string * Whitespace.t list) list;
    }
      -> t
  | Bof of Whitespace.t list
  | Eof

let execute : t -> unit = function
  | Axiom { name; ty = Term ty; _ } ->
      if Option.is_some (Scope.lookup name) then
        emit (Constant_already_defined (String.concat "." name));
      let const = Scope.define name in
      Reporter.try_with ~fatal:(fun d ->
          Scope.S.modify_visible (Yuujinchou.Language.except name);
          Scope.S.modify_export (Yuujinchou.Language.except name);
          Reporter.fatal_diagnostic d)
      @@ fun () ->
      Core.Command.execute (Axiom (const, process Emp ty));
      emit (Constant_assumed (PConstant const))
  | Def { name; ty = Term ty; tm = Term tm; _ } ->
      if Option.is_some (Scope.lookup name) then
        emit (Constant_already_defined (String.concat "." name));
      let const = Scope.define name in
      Reporter.try_with ~fatal:(fun d ->
          Scope.S.modify_visible (Yuujinchou.Language.except name);
          Scope.S.modify_export (Yuujinchou.Language.except name);
          Reporter.fatal_diagnostic d)
      @@ fun () ->
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
  | Notation { fixity; name; pattern; head; args; _ } ->
      let notation_name = "notation" :: name in
      if Option.is_some (Scope.lookup notation_name) then
        emit (Constant_already_defined (String.concat "." notation_name));
      (* TODO: Should the "name" of a notation actually be a Constant.t, to be looked up in the scope? *)
      let _ = Scope.define notation_name in
      Reporter.try_with ~fatal:(fun d ->
          Scope.S.modify_visible (Yuujinchou.Language.except notation_name);
          Scope.S.modify_export (Yuujinchou.Language.except notation_name);
          Reporter.fatal_diagnostic d)
      @@ fun () ->
      let head =
        match head with
        | `Constr c -> `Constr (Constr.intern c)
        | `Constant c -> (
            match Scope.lookup c with
            | Some c -> `Constant c
            | None -> fatal (Invalid_notation_head (String.concat "." c))) in
      let unbound, _ =
        List.fold_left
          (fun (args, seen) item ->
            match item with
            | `Var (x, _, _) -> (
                if List.mem x seen then fatal (Duplicate_notation_variable x);
                let found, rest = List.partition (fun (y, _) -> x = y) args in
                match found with
                | [ _ ] -> (rest, x :: seen)
                | [] -> fatal (Unused_notation_variable x)
                | _ -> fatal (Notation_variable_used_twice x))
            | `Op _ | `Ellipsis _ -> (args, seen))
          (args, []) pattern in
      if not (List.is_empty unbound) then
        fatal (Unbound_variable_in_notation (List.map fst unbound));
      State.Current.add_user (String.concat "." name) fixity pattern head (List.map fst args);
      emit (Notation_defined (String.concat "." name))
  | Bof _ -> ()
  | Eof -> fatal (Anomaly "EOF cannot be executed")

let tightness_of_fixity : type left tight right. (left, tight, right) fixity -> string option =
  function
  | Infix tight
  | Infixl tight
  | Infixr tight
  | Prefix tight
  | Prefixr tight
  | Postfix tight
  | Postfixl tight -> Some (No.to_string tight)
  | Outfix -> None

let pp_pattern : formatter -> State.pattern -> unit =
 fun ppf pattern ->
  pp_open_hvbox ppf 0;
  List.iter
    (function
      | `Var (x, _, ws) ->
          pp_utf_8 ppf x;
          pp_ws `Break ppf ws
      | `Op (op, _, ws) ->
          pp_print_string ppf "\"";
          pp_tok ppf op;
          pp_print_string ppf "\"";
          pp_ws `Break ppf ws
      | `Ellipsis ws ->
          pp_tok ppf Ellipsis;
          pp_ws `Break ppf ws)
    pattern;
  pp_close_box ppf ()

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
  | Echo { wsecho; tm = Term tm } ->
      pp_open_hvbox ppf 2;
      pp_tok ppf Echo;
      pp_ws `Nobreak ppf wsecho;
      let tm, rest = split_ending_whitespace tm in
      pp_term `None ppf (Term tm);
      pp_close_box ppf ();
      rest
  | Notation
      {
        fixity;
        wsnotation;
        wstight;
        wsellipsis;
        name;
        wsname;
        wscolon;
        pattern;
        wscoloneq;
        head;
        wshead;
        args;
      } ->
      pp_open_hvbox ppf 2;
      pp_tok ppf Notation;
      pp_ws `Nobreak ppf wsnotation;
      (match tightness_of_fixity fixity with
      | Some str -> pp_print_string ppf str
      | None -> ());
      pp_ws `Nobreak ppf wstight;
      pp_utf_8 ppf (String.concat "." name);
      pp_ws `Break ppf wsname;
      pp_tok ppf Colon;
      pp_ws `Nobreak ppf wscolon;
      (match fixity with
      | Infixl _ | Postfixl _ ->
          pp_tok ppf Ellipsis;
          pp_ws `Break ppf wsellipsis
      | _ -> ());
      pp_pattern ppf pattern;
      (match fixity with
      | Infixr _ | Prefixr _ ->
          pp_tok ppf Ellipsis;
          pp_ws `Break ppf wsellipsis
      | _ -> ());
      pp_tok ppf Coloneq;
      pp_ws `Nobreak ppf wscoloneq;
      (match head with
      | `Constr c -> pp_constr ppf c
      | `Constant c -> pp_utf_8 ppf (String.concat "." c));
      let rest =
        match split_last args with
        | None ->
            let wshead, rest = Whitespace.split wshead in
            pp_ws `None ppf wshead;
            rest
        | Some (args, (last, wslast)) ->
            List.iter
              (fun (arg, wsarg) ->
                pp_utf_8 ppf arg;
                pp_ws `Break ppf wsarg)
              args;
            pp_utf_8 ppf last;
            let wslast, rest = Whitespace.split wslast in
            pp_ws `None ppf wslast;
            rest in
      pp_close_box ppf ();
      rest
  | Bof ws -> ws
  | Eof -> []
