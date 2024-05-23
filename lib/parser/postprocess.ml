open Util
open Dim
open Core
open Syntax
open Raw
open Reporter
open Notation
open Asai.Range
open Monad.Ops (Monad.Maybe)

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

(* Now the master postprocessing function.  Note that this function calls the "process" functions registered for individual notations, but those functions will be defined to call *this* function on their constituents, so we have some "open recursion" going on. *)

let rec process :
    type n lt ls rt rs.
    (string option, n) Bwv.t -> (lt, ls, rt, rs) parse located -> n check located =
 fun ctx res ->
  let loc = res.loc in
  with_loc loc @@ fun () ->
  match res.value with
  | Notn n -> (processor (notn n)).process ctx (args n) loc (whitespace n)
  (* "Application" nodes in result trees are used for anything that syntactically *looks* like an application.  In addition to actual applications of functions, this includes applications of constructors and degeneracy operators, and also field projections.  *)
  | App { fn; arg; _ } -> process_spine ctx fn [ (Term arg, res.loc) ]
  | Placeholder _ -> fatal (Unimplemented "unification arguments")
  | Ident (parts, _) -> (
      let open Monad.Ops (Monad.Maybe) in
      match
        match parts with
        | [ x ] ->
            let* _, n = Bwv.find_opt (fun y -> y = Some x) ctx in
            Some (Synth (Var (n, None)))
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
              try process_numeral loc (Q.of_string (String.concat "." parts))
              with Invalid_argument _ -> (
                match parts with
                | [ str ] when Option.is_some (deg_of_name str) ->
                    fatal (Missing_argument_of_degeneracy str)
                | _ -> fatal (Unbound_variable (String.concat "." parts))))))
  | Constr (ident, _) -> { value = Raw.Constr ({ value = Constr.intern ident; loc }, []); loc }
  | Field _ -> fatal (Anomaly "field is head")
  | Superscript (Some x, str, _) -> (
      match deg_of_string str with
      | Some (Any s) -> (
          let body = process ctx x in
          match body.value with
          | Synth arg -> { value = Synth (Act (str, s, { value = arg; loc = body.loc })); loc }
          | _ -> fatal ?loc:body.loc (Nonsynthesizing "argument of degeneracy"))
      | None -> fatal (Invalid_degeneracy str))
  | Superscript (None, _, _) -> fatal (Anomaly "degeneracy is head")

and process_spine :
    type n lt ls rt rs.
    (string option, n) Bwv.t ->
    (lt, ls, rt, rs) parse located ->
    (observation * Asai.Range.t option) list ->
    n check located =
 fun ctx tm args ->
  match tm.value with
  | App { fn; arg; _ } -> process_spine ctx fn ((Term arg, tm.loc) :: args)
  | _ -> process_apps ctx tm args

and process_apps :
    type n lt ls rt rs.
    (string option, n) Bwv.t ->
    (lt, ls, rt, rs) parse located ->
    (observation * Asai.Range.t option) list ->
    n check located =
 fun ctx tm args ->
  match process_head ctx tm with
  | `Deg (str, Any s) -> (
      match args with
      | (Term arg, loc) :: args -> (
          match process ctx arg with
          | { value = Synth arg; _ } ->
              process_apply ctx { value = Act (str, s, { value = arg; loc }); loc } args
          | { loc; _ } -> fatal ?loc (Nonsynthesizing "argument of degeneracy"))
      | [] -> fatal ?loc:tm.loc (Anomaly "TODO"))
  | `Constr c ->
      let c = { value = c; loc = tm.loc } in
      let loc = ref None in
      let args =
        List.map
          (fun (Term x, l) ->
            loc := l;
            process ctx x)
          args in
      { value = Raw.Constr (c, args); loc = !loc }
  | `Fn fn -> process_apply ctx fn args

and process_head :
    type n lt ls rt rs.
    (string option, n) Bwv.t ->
    (lt, ls, rt, rs) parse located ->
    [ `Deg of string * any_deg | `Constr of Constr.t | `Fn of n synth located ] =
 fun ctx tm ->
  let process_fn () =
    let tm = process ctx tm in
    match tm.value with
    | Synth value -> `Fn { value; loc = tm.loc }
    | _ -> fatal (Anomaly "") in
  match tm.value with
  | Constr (ident, _) -> `Constr (Constr.intern ident)
  | Ident ([ str ], _) -> (
      match deg_of_name str with
      | Some s -> `Deg (str, s)
      | None -> process_fn ())
  | _ -> process_fn ()

and process_apply :
    type n.
    (string option, n) Bwv.t ->
    n synth located ->
    (observation * Asai.Range.t option) list ->
    n check located =
 fun ctx fn args ->
  match args with
  | [] -> { value = Synth fn.value; loc = fn.loc }
  | (Term { value = Field (fld, _); _ }, loc) :: args ->
      process_apply ctx { value = Field (fn, Field.intern_ori fld); loc } args
  | (Term arg, loc) :: args -> process_apply ctx { value = Raw.App (fn, process ctx arg); loc } args

type _ processed_tel =
  | Processed_tel : ('n, 'k, 'nk) Raw.tel * (string option, 'nk) Bwv.t -> 'n processed_tel

let rec process_tel : type n. (string option, n) Bwv.t -> Parameter.t list -> n processed_tel =
 fun ctx parameters ->
  match parameters with
  | [] -> Processed_tel (Emp, ctx)
  | { names; ty; _ } :: parameters -> process_vars ctx names ty parameters

and process_vars :
    type n b.
    (string option, n) Bwv.t ->
    (string option * b) list ->
    observation ->
    Parameter.t list ->
    n processed_tel =
 fun ctx names (Term ty) parameters ->
  match names with
  | [] -> process_tel ctx parameters
  | (name, _) :: names ->
      let pty = process ctx ty in
      let (Processed_tel (tel, ctx)) = process_vars (Bwv.snoc ctx name) names (Term ty) parameters in
      Processed_tel (Ext (name, pty, tel), ctx)
