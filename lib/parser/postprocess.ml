open Bwd
open Util
open Dim
open Core
open Raw
open Reporter
open Asai.Range
open Notation
open Monad.Ops (Monad.Maybe)
module StringMap = Map.Make (String)

(* We define this here so we can refer to it in parsing implicit applications. *)

type (_, _, _) identity += Braces : (closed, No.plus_omega, closed) identity

let braces : (closed, No.plus_omega, closed) notation = (Braces, Outfix)

(* Require the argument to be either a valid local variable name (to be bound, so faces of cubical variables are not allowed) or an underscore, and return a corresponding 'string option'. *)
let get_var : type lt ls rt rs. (lt, ls, rt, rs) parse located -> string option =
 fun { value; loc } ->
  with_loc loc @@ fun () ->
  match value with
  | Ident ([ x ], _) -> Some x
  | Ident (xs, _) -> fatal (Invalid_variable xs)
  | Placeholder _ -> None
  | _ -> fatal Parse_error

(* At present we only know how to postprocess natural number numerals. *)
let process_numeral loc (n : Q.t) =
  let rec process_nat (n : Z.t) =
    (* TODO: Would be better not to hardcode these. *)
    if n = Z.zero then { value = Raw.Constr ({ value = Constr.intern "zero"; loc }, []); loc }
    else
      {
        value = Raw.Constr ({ value = Constr.intern "suc"; loc }, [ process_nat (Z.sub n Z.one) ]);
        loc;
      } in
  if n.den = Z.one && n.num >= Z.zero then process_nat n.num else fatal (Unsupported_numeral n)

(* Process a bare identifier, resolving it into either a variable, a cube variable with face, a constant, a numeral, or a degeneracy name (the latter being an error since it isn't applied to anything). *)
let process_ident ctx loc parts =
  let open Monad.Ops (Monad.Maybe) in
  (* A numeral is an ident whose pieces are composed entirely of digits.  Of course if there are more than two parts it's not a *valid* numeral, but we don't allow it as another kind of token either. *)
  if List.is_empty parts then fatal (Anomaly "empty ident")
  else if Lexer.is_numeral parts then
    try process_numeral loc (Q.of_string (String.concat "." parts))
    with Invalid_argument _ -> fatal (Invalid_numeral (String.concat "." parts))
  else
    match
      match parts with
      | [ x ] ->
          let* _, n = Bwv.find_opt (fun y -> y = Some x) ctx in
          return (Synth (Var (n, None)))
      | [ x; face ] ->
          let* _, v = Bwv.find_opt (fun y -> y = Some x) ctx in
          let* fa = sface_of_string face in
          return (Synth (Var (v, Some fa)))
      | _ -> None
    with
    | Some tm -> { value = tm; loc }
    | None -> (
        match Scope.lookup parts with
        | Some c -> { value = Synth (Const c); loc }
        | None -> (
            match parts with
            | [ str ] when Option.is_some (deg_of_name str) ->
                fatal (Missing_argument_of_degeneracy str)
            | _ -> fatal (Unbound_variable (String.concat "." parts, []))))

(* If an identifier doesn't resolve, we check whether the user might have meant to project one or more fields from a shorter identifier, and give them a hint that field projections require spaces. *)
let rec detect_spaceless_fields ctx loc (bwd_parts : string Bwd.t) fields found =
  match bwd_parts with
  | Emp | Snoc (Emp, _) -> found
  | Snoc (bwd_parts, fld) ->
      Reporter.try_with
        (fun () ->
          let parts = Bwd.to_list bwd_parts in
          let _ = process_ident ctx loc parts in
          detect_spaceless_fields ctx loc bwd_parts (fld :: fields) ((parts, fld :: fields) :: found))
        ~fatal:(fun _ -> detect_spaceless_fields ctx loc bwd_parts (fld :: fields) found)

(* Now the master postprocessing function.  Note that this function calls the "process" functions registered for individual notations, but those functions will be defined to call *this* function on their constituents, so we have some "open recursion" going on. *)

let rec process : type n lt ls rt rs.
    (string option, n) Bwv.t -> (lt, ls, rt, rs) parse located -> n check located =
 fun ctx res ->
  let loc = res.loc in
  with_loc loc @@ fun () ->
  match res.value with
  | Notn (n, d) -> (find n).processor ctx (args d) loc
  (* "Application" nodes in result trees are used for anything that syntactically *looks* like an application.  In addition to actual applications of functions, this includes applications of constructors and degeneracy operators, and also field projections.  *)
  | App { fn; arg; _ } -> process_spine ctx fn [ (Wrap arg, res.loc) ]
  | Placeholder _ -> fatal (Unimplemented "unification arguments")
  | Ident (parts, _) ->
      Reporter.try_with
        (fun () -> process_ident ctx loc parts)
        ~fatal:(fun ({ severity; message; backtrace; explanation; extra_remarks } as d) ->
          match message with
          | Unbound_variable (p, _) ->
              let alt = detect_spaceless_fields ctx loc (Bwd.of_list parts) [] [] in
              (* We create a new diagnostic, preserving all the information except the message, but we have to recompute the 'explanation'. *)
              let message = Reporter.Code.Unbound_variable (p, alt) in
              let explanation = locate_opt explanation.loc (Reporter.Code.default_text message) in
              fatal_diagnostic { severity; message; backtrace; extra_remarks; explanation }
          | _ -> fatal_diagnostic d)
  | Constr (ident, _) -> { value = Raw.Constr ({ value = Constr.intern ident; loc }, []); loc }
  | Field _ ->
      (* This can happen if the user tries to project a field from a constructor. *)
      fatal Parse_error
  | Superscript (Some x, str, _) -> (
      match deg_of_string str with
      | Some (Any_deg s) ->
          let body = process ctx x in
          { value = Synth (Act (str, s, body)); loc }
      | None -> fatal (Invalid_degeneracy str))
  | Superscript (None, _, _) -> fatal (Anomaly "degeneracy is head")
  | Hole { li; ri; num; _ } ->
      let hloc = loc <|> Anomaly "missing location in Hole" in
      { value = Hole { scope = ctx; loc = hloc; li = Interval li; ri = Interval ri; num }; loc }

and process_spine : type n lt ls rt rs.
    (string option, n) Bwv.t ->
    (lt, ls, rt, rs) parse located ->
    (wrapped_parse * Asai.Range.t option) list ->
    n check located =
 fun ctx tm args ->
  match tm.value with
  | App { fn; arg; _ } -> process_spine ctx fn ((Wrap arg, tm.loc) :: args)
  | _ -> process_apps ctx tm args

and process_apps : type n lt ls rt rs.
    (string option, n) Bwv.t ->
    (lt, ls, rt, rs) parse located ->
    (wrapped_parse * Asai.Range.t option) list ->
    n check located =
 fun ctx tm args ->
  match process_head ctx tm with
  | `Deg (str, Any_deg s) -> (
      match args with
      | (Wrap arg, loc) :: args ->
          process_apply ctx
            { value = Act (str, s, { value = (process ctx arg).value; loc }); loc }
            args
      | [] -> fatal ?loc:tm.loc (Anomaly "TODO"))
  | `Constr c ->
      let c = { value = c; loc = tm.loc } in
      let loc = ref None in
      let args =
        List.map
          (fun (Wrap x, l) ->
            loc := l;
            process ctx x)
          args in
      { value = Raw.Constr (c, args); loc = !loc }
  | `Fn fn -> process_apply ctx fn args

and process_head : type n lt ls rt rs.
    (string option, n) Bwv.t ->
    (lt, ls, rt, rs) parse located ->
    [ `Deg of string * any_deg | `Constr of Constr.t | `Fn of n synth located ] =
 fun ctx tm ->
  match tm.value with
  | Constr (ident, _) -> `Constr (Constr.intern ident)
  | Ident ([ str ], _) -> (
      match deg_of_name str with
      | Some s -> `Deg (str, s)
      | None -> `Fn (process_synth ctx tm "function"))
  | _ -> `Fn (process_synth ctx tm "function")

and process_apply : type n.
    (string option, n) Bwv.t ->
    n synth located ->
    (wrapped_parse * Asai.Range.t option) list ->
    n check located =
 fun ctx fn fnargs ->
  match fnargs with
  | [] -> { value = Synth fn.value; loc = fn.loc }
  | (Wrap { value = Field (fld, pbij, _); _ }, loc) :: args -> (
      try
        let fld =
          try `Int (int_of_string fld) with Failure _ -> `Name (fld, List.map int_of_string pbij)
        in
        process_apply ctx { value = Field (fn, fld); loc } args
      with Failure _ -> fatal (Invalid_field (String.concat "." ("" :: fld :: pbij))))
  | (Wrap { value = Notn ((Braces, _), n); loc = braceloc }, loc) :: rest -> (
      match args n with
      | [ Token (LBrace, _); Term arg; Token (RBrace, _) ] ->
          process_apply ctx
            { value = Raw.App (fn, process ctx arg, locate_opt braceloc `Implicit); loc }
            rest
      | _ -> fatal (Anomaly "invalid notation arguments for braces"))
  | (Wrap arg, loc) :: args ->
      process_apply ctx
        { value = Raw.App (fn, process ctx arg, locate_opt arg.loc `Explicit); loc }
        args

and process_synth : type n lt ls rt rs.
    (string option, n) Bwv.t -> (lt, ls, rt, rs) parse located -> string -> n synth located =
 fun ctx x str ->
  match process ctx x with
  | { value = Synth value; loc } -> { value; loc }
  | { loc; _ } -> fatal ?loc (Nonsynthesizing str)

type _ processed_tel =
  | Processed_tel :
      ('n, 'k, 'nk) Raw.tel * (string option, 'nk) Bwv.t * (Whitespace.t list, 'k) Vec.t
      -> 'n processed_tel

let rec process_tel : type n. (string option, n) Bwv.t -> Parameter.t list -> n processed_tel =
 fun ctx parameters ->
  match parameters with
  | [] -> Processed_tel (Emp, ctx, [])
  | { names; ty; _ } :: parameters -> process_vars ctx names ty parameters

and process_vars : type n.
    (string option, n) Bwv.t ->
    (string option * Whitespace.t list) list ->
    wrapped_parse ->
    Parameter.t list ->
    n processed_tel =
 fun ctx names (Wrap ty) parameters ->
  match names with
  | [] -> process_tel ctx parameters
  | (name, w) :: names ->
      let pty = process ctx ty in
      let (Processed_tel (tel, ctx, ws)) =
        process_vars (Bwv.snoc ctx name) names (Wrap ty) parameters in
      Processed_tel (Ext (name, pty, tel), ctx, w :: ws)
