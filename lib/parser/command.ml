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
      wsfix : Whitespace.t list;
      wstight : Whitespace.t list;
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
                if List.mem x seen then
                  fatal (Invalid_notation_pattern ("duplicate variable: " ^ x));
                let found, rest = List.partition (fun (y, _) -> x = y) args in
                match found with
                | [ _ ] -> (rest, x :: seen)
                | [] -> fatal (Invalid_notation_pattern ("unused variable: " ^ x))
                | _ -> fatal (Invalid_notation_pattern ("variable used twice: " ^ x)))
            | `Op _ -> (args, seen))
          (args, []) pattern in
      if not (List.is_empty unbound) then
        fatal
          (Invalid_notation_pattern
             ("unbound variable(s): " ^ String.concat ", " (List.map fst unbound)));
      State.Current.add_user (String.concat "." name) fixity pattern head (List.map fst args);
      emit (Notation_defined (String.concat "." name))
  | Bof _ -> ()
  | Eof -> fatal (Anomaly "EOF cannot be executed")

let fixity_toks : type left tight right. (left, tight, right) fixity -> Token.t * string = function
  | Infix tight -> (Infix, No.to_string tight)
  | Infixl tight -> (Infixl, No.to_string tight)
  | Infixr tight -> (Infixr, No.to_string tight)
  | Prefix tight -> (Prefix, No.to_string tight)
  | Prefixr tight -> (Prefixr, No.to_string tight)
  | Postfix tight -> (Postfix, No.to_string tight)
  | Postfixl tight -> (Postfixl, No.to_string tight)
  | Outfix -> (Outfix, "")

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
      { fixity; wsfix; wstight; name; wsname; wscolon; pattern; wscoloneq; head; wshead; args } ->
      pp_open_hvbox ppf 2;
      let fix_tok, tight_tok = fixity_toks fixity in
      pp_tok ppf fix_tok;
      pp_ws `Nobreak ppf wsfix;
      pp_print_string ppf tight_tok;
      pp_ws `Nobreak ppf wstight;
      pp_utf_8 ppf (String.concat "." name);
      pp_ws `Break ppf wsname;
      pp_tok ppf Colon;
      pp_ws `Nobreak ppf wscolon;
      pp_pattern ppf pattern;
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
