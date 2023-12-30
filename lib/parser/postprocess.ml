open Util
open Dim
open Core
open Syntax
open Raw
open Bwd
open Reporter
open Notation
open Monad.Ops (Monad.Maybe)

(* Require the argument to be either a valid local variable name (to be bound, so faces of cubical variables are not allowed) or an underscore, and return a corresponding 'string option'. *)
let get_var : type lt ls rt rs. (lt, ls, rt, rs) parse -> string option = function
  | Ident [ x ] -> Some x
  | Ident xs -> fatal (Invalid_variable xs)
  | Placeholder -> None
  | _ -> fatal Parse_error

(* At present we only know how to postprocess natural number numerals. *)
let process_numeral (n : Q.t) =
  let rec process_nat (n : Z.t) =
    (* TODO: Would be better not to hardcode these. *)
    if n = Z.zero then Raw.Constr (Constr.intern "zero", Emp)
    else Raw.Constr (Constr.intern "suc", Snoc (Emp, process_nat (Z.sub n Z.one))) in
  if n.den = Z.one && n.num >= Z.zero then process_nat n.num else fatal (Unsupported_numeral n)

(* Now the master postprocessing function.  Note that this function calls the "process" functions registered for individual notations, but those functions will be defined to call *this* function on their constituents, so we have some "open recursion" going on. *)

let rec process : type n lt ls rt rs. (string option, n) Bwv.t -> (lt, ls, rt, rs) parse -> n check
    =
 fun ctx res ->
  match res with
  | Notn n -> (processor (notn n)).process ctx (args n)
  (* "Application" nodes in result trees are used for anything that syntactically *looks* like an application.  In addition to actual applications of functions, this includes applications of constructors and degeneracy operators, and also field projections.  *)
  | App { fn; arg; _ } -> (
      match
        match fn with
        | Ident [ str ] -> process_deg ctx str arg
        | _ -> None
      with
      | Some tm -> tm
      | _ -> (
          let fn = process ctx fn in
          match fn with
          | Synth fn -> (
              match arg with
              | Field fld -> Synth (Field (fn, Field.intern fld))
              | _ -> Synth (Raw.App (fn, process ctx arg)))
          | Constr (head, args) ->
              let arg = process ctx arg in
              Raw.Constr (head, Snoc (args, arg))
          | _ -> fatal (Nonsynthesizing "application head")))
  | Placeholder -> fatal (Unimplemented "unification arguments")
  | Ident parts -> (
      let open Monad.Ops (Monad.Maybe) in
      match
        match parts with
        | [ x ] -> Option.map (fun n -> Synth (Var (n, None))) (Bwv.find (Some x) ctx)
        | [ x; face ] ->
            let* v = Bwv.find (Some x) ctx in
            let* fa = sface_of_string face in
            return (Synth (Var (v, Some fa)))
        | _ -> None
      with
      | Some tm -> tm
      | None -> (
          match Scope.lookup parts with
          | Some c -> Synth (Const c)
          | None -> (
              try process_numeral (Q.of_string (String.concat "." parts))
              with Invalid_argument _ -> (
                match parts with
                | [ str ] when Option.is_some (deg_of_name str) ->
                    fatal (Missing_argument_of_degeneracy str)
                | _ -> fatal (Unbound_variable (String.concat "." parts))))))
  | Constr ident -> Raw.Constr (Constr.intern ident, Emp)
  | Field _ -> fatal (Anomaly "Field is head")

and process_deg :
    type n lt ls rt rs.
    (string option, n) Bwv.t -> string -> (lt, ls, rt, rs) parse -> n check option =
 fun ctx str arg ->
  match deg_of_name str with
  | Some (Any s) -> (
      match process ctx arg with
      | Synth arg -> Some (Synth (Act (str, s, arg)))
      | _ -> fatal (Nonsynthesizing "argument of degeneracy"))
  | None -> None
