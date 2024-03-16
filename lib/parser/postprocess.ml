open Util
open Dim
open Core
open Syntax
open Raw
open Bwd
open Reporter
open Notation
open Asai.Range
open Monad.Ops (Monad.Maybe)

(* Require the argument to be either a valid local variable name (to be bound, so faces of cubical variables are not allowed) or an underscore, and return a corresponding 'string option'. *)
let get_var : type lt ls rt rs. (lt, ls, rt, rs) parse -> string option = function
  | Ident ([ x ], _) -> Some x
  | Ident (xs, _) -> fatal (Invalid_variable xs)
  | Placeholder _ -> None
  | _ -> fatal Parse_error

(* At present we only know how to postprocess natural number numerals. *)
let process_numeral loc (n : Q.t) =
  let rec process_nat (n : Z.t) =
    (* TODO: Would be better not to hardcode these. *)
    if n = Z.zero then { value = Raw.Constr ({ value = Constr.intern "zero"; loc }, Emp); loc }
    else
      {
        value =
          Raw.Constr ({ value = Constr.intern "suc"; loc }, Snoc (Emp, process_nat (Z.sub n Z.one)));
        loc;
      } in
  if n.den = Z.one && n.num >= Z.zero then process_nat n.num else fatal (Unsupported_numeral n)

(* Now the master postprocessing function.  Note that this function calls the "process" functions registered for individual notations, but those functions will be defined to call *this* function on their constituents, so we have some "open recursion" going on. *)

let rec process :
    type n lt ls rt rs. n Varscope.t -> (lt, ls, rt, rs) parse located -> n check located =
 fun ctx res ->
  let loc = res.loc in
  match res.value with
  | Notn n -> (processor (notn n)).process ctx (args n) loc (whitespace n)
  (* "Application" nodes in result trees are used for anything that syntactically *looks* like an application.  In addition to actual applications of functions, this includes applications of constructors and degeneracy operators, and also field projections.  *)
  | App { fn; arg; _ } -> (
      match
        match fn.value with
        | Ident ([ str ], _) -> process_deg ctx str arg
        | _ -> None
      with
      | Some tm -> { value = tm; loc }
      | _ -> (
          let fn = process ctx fn in
          match fn.value with
          | Synth vfn -> (
              let fn = { value = vfn; loc = fn.loc } in
              match arg.value with
              | Field (fld, _) -> { value = Synth (Field (fn, Field.intern_ori fld)); loc }
              | _ -> { value = Synth (Raw.App (fn, process ctx arg)); loc })
          | Constr (head, args) ->
              let arg = process ctx arg in
              { value = Raw.Constr (head, Snoc (args, arg)); loc }
          | _ -> fatal (Nonsynthesizing "application head")))
  | Placeholder _ -> fatal (Unimplemented "unification arguments")
  | Ident (parts, _) -> (
      let open Monad.Ops (Monad.Maybe) in
      match
        match parts with
        | [ x ] -> (
            match Varscope.find x ctx with
            | `Var n -> Some (Synth (Var (n, None)))
            | `Field (n, fld) -> Some (Synth (Field ({ value = Var (n, None); loc }, `Name fld)))
            | `None -> None)
        | [ x; face ] -> (
            match Varscope.find x ctx with
            | `Var v ->
                let* fa = sface_of_string face in
                return (Synth (Var (v, Some fa)))
            | `Field _ | `None -> None)
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
  | Constr (ident, _) -> { value = Raw.Constr ({ value = Constr.intern ident; loc }, Emp); loc }
  | Field _ -> fatal (Anomaly "field is head")
  | Superscript (Some x, str, _) ->
      let len = String.length str in
      if str.[0] = '(' && str.[len - 1] = ')' then
        match deg_of_string (String.sub str 1 (len - 2)) with
        | Some (Any s) -> (
            let body = process ctx x in
            match body.value with
            | Synth arg -> { value = Synth (Act (str, s, { value = arg; loc = body.loc })); loc }
            | _ -> fatal (Nonsynthesizing "argument of degeneracy"))
        | None -> fatal (Invalid_degeneracy str)
      else fatal (Unimplemented "non-degeneracy superscripts (degeneracies must be parenthesized)")
  | Superscript (None, _, _) -> fatal (Anomaly "degeneracy is head")

and process_deg :
    type n lt ls rt rs. n Varscope.t -> string -> (lt, ls, rt, rs) parse located -> n check option =
 fun ctx str arg ->
  match deg_of_name str with
  | Some (Any s) -> (
      match process ctx arg with
      | { value = Synth arg; loc } -> Some (Synth (Act (str, s, { value = arg; loc })))
      | _ -> fatal (Nonsynthesizing "argument of degeneracy"))
  | None -> None

type _ processed_tel = Processed_tel : ('n, 'k, 'nk) Raw.tel * 'nk Varscope.t -> 'n processed_tel

let rec process_tel : type n. n Varscope.t -> Parameter.t list -> n processed_tel =
 fun ctx parameters ->
  match parameters with
  | [] -> Processed_tel (Emp, ctx)
  | { names; ty; _ } :: parameters -> process_vars ctx names ty parameters

and process_vars :
    type n b.
    n Varscope.t -> (string option * b) list -> observation -> Parameter.t list -> n processed_tel =
 fun ctx names (Term ty) parameters ->
  match names with
  | [] -> process_tel ctx parameters
  | (name, _) :: names ->
      let pty = process ctx ty in
      let (Processed_tel (tel, ctx)) =
        process_vars (Varscope.ext ctx name) names (Term ty) parameters in
      Processed_tel (Ext (name, pty, tel), ctx)
