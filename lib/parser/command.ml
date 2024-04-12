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

type def = {
  wsdef : Whitespace.t list;
  name : Scope.Trie.path;
  wsname : Whitespace.t list;
  parameters : Parameter.t list;
  wscolon : Whitespace.t list;
  ty : observation option;
  wscoloneq : Whitespace.t list;
  tm : observation;
}

type t =
  | Axiom of {
      wsaxiom : Whitespace.t list;
      name : Scope.Trie.path;
      wsname : Whitespace.t list;
      parameters : Parameter.t list;
      wscolon : Whitespace.t list;
      ty : observation;
    }
  | Def of def list
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
  | Axiom { name; parameters; ty = Term ty; _ } ->
      if Option.is_some (Scope.lookup name) then
        emit (Constant_already_defined (String.concat "." name));
      let const = Scope.define name in
      Reporter.try_with ~fatal:(fun d ->
          Scope.S.modify_visible (Yuujinchou.Language.except name);
          Scope.S.modify_export (Yuujinchou.Language.except name);
          Reporter.fatal_diagnostic d)
      @@ fun () ->
      let (Processed_tel (params, ctx)) = process_tel Varscope.empty parameters in
      Core.Command.execute (Axiom (const, params, process ctx ty));
      emit (Constant_assumed (PConstant const))
  | Def defs ->
      let [ names; cdefs; printables ] =
        Mlist.pmap
          (fun [ d ] ->
            if Option.is_some (Scope.lookup d.name) then
              emit (Constant_already_defined (String.concat "." d.name));
            let c = Scope.define d.name in
            [ d.name; (c, d); PConstant c ])
          [ defs ] (Cons (Cons (Cons Nil))) in
      Reporter.try_with ~fatal:(fun d ->
          List.iter
            (fun c ->
              Scope.S.modify_visible (Yuujinchou.Language.except c);
              Scope.S.modify_export (Yuujinchou.Language.except c))
            names;
          Reporter.fatal_diagnostic d)
      @@ fun () ->
      let defs =
        List.map
          (function
            | const, { parameters; ty; tm = Term tm; _ } -> (
                let (Processed_tel (params, ctx)) = process_tel Varscope.empty parameters in
                match ty with
                | Some (Term ty) ->
                    Core.Command.Def_check (const, params, process ctx ty, process ctx tm)
                | None -> (
                    match process ctx tm with
                    | { value = Synth tm; loc } -> Def_synth (const, params, { value = tm; loc })
                    | _ -> fatal (Nonsynthesizing "body of def without specified type"))))
          cdefs in
      Core.Command.execute (Def defs);
      emit (Constant_defined printables)
  | Echo { tm = Term tm; _ } -> (
      let rtm = process Varscope.empty tm in
      match rtm.value with
      | Synth stm ->
          let ctm, ety = Check.synth Ctx.empty { value = stm; loc = rtm.loc } in
          let etm = Norm.eval_term (Emp D.zero) ctm in
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

let pp_parameter : formatter -> Parameter.t -> unit =
 fun ppf { wslparen; names; wscolon; ty; wsrparen } ->
  pp_tok ppf LParen;
  pp_ws `None ppf wslparen;
  List.iter
    (fun (name, wsname) ->
      pp_var ppf name;
      pp_ws `Break ppf wsname)
    names;
  pp_tok ppf Colon;
  pp_ws `Nobreak ppf wscolon;
  pp_term `None ppf ty;
  pp_tok ppf RParen;
  pp_ws `Break ppf wsrparen

let rec pp_defs : formatter -> Token.t -> Whitespace.t list -> def list -> Whitespace.t list =
 fun ppf tok ws defs ->
  match defs with
  | [] -> ws
  | { wsdef; name; wsname; parameters; wscolon; ty; wscoloneq; tm = Term tm } :: defs ->
      pp_ws `None ppf ws;
      pp_open_hvbox ppf 2;
      pp_tok ppf tok;
      pp_ws `Nobreak ppf wsdef;
      pp_utf_8 ppf (String.concat "." name);
      pp_ws `Break ppf wsname;
      List.iter (pp_parameter ppf) parameters;
      (match ty with
      | Some ty ->
          pp_tok ppf Colon;
          pp_ws `Nobreak ppf wscolon;
          pp_term `Break ppf ty
      | None -> ());
      pp_tok ppf Coloneq;
      pp_ws `Nobreak ppf wscoloneq;
      let tm, rest = split_ending_whitespace tm in
      pp_term `None ppf (Term tm);
      pp_close_box ppf ();
      pp_defs ppf And rest defs

let pp_command : formatter -> t -> Whitespace.t list =
 fun ppf cmd ->
  match cmd with
  | Axiom { wsaxiom; name; wsname; parameters; wscolon; ty = Term ty } ->
      pp_open_hvbox ppf 2;
      pp_tok ppf Axiom;
      pp_ws `Nobreak ppf wsaxiom;
      pp_utf_8 ppf (String.concat "." name);
      pp_ws `Break ppf wsname;
      List.iter (pp_parameter ppf) parameters;
      pp_tok ppf Colon;
      pp_ws `Nobreak ppf wscolon;
      let ty, rest = split_ending_whitespace ty in
      pp_term `None ppf (Term ty);
      pp_close_box ppf ();
      rest
  | Def defs -> pp_defs ppf Def [] defs
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
