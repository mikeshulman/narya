open Util
open Dim
open Core
open Raw
open Bwd
open Reporter
open Notation
open Monad.Ops (Monad.Maybe)

(* Require the argument to be either a local variable name or an underscore, and return a corresponding 'string option'. *)
let get_var : type lt ls rt rs. (lt, ls, rt, rs) parse -> string option = function
  | Ident x -> if Token.variableable x then Some x else fatal (Invalid_variable x)
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
  (* "Application" nodes in result trees are used for anything that syntactically *looks* like an application.  In addition to actual applications of functions, this includes applications of constructors and symbols, and also field projections.  *)
  | App { fn; arg; _ } -> (
      let fn = process ctx fn in
      match fn with
      | Synth fn -> (
          match fn with
          | Act (str, s, None) -> (
              match process ctx arg with
              | Synth arg -> Synth (Act (str, s, Some arg))
              | _ -> fatal (Nonsynthesizing "argument of degeneracy"))
          | _ -> (
              match arg with
              | Field fld -> (
                  match sface_of_string fld with
                  | Some fa -> (
                      match fn with
                      | Var (v, None) -> Synth (Var (v, Some fa))
                      | _ -> fatal Parse_error)
                  | _ -> Synth (Field (fn, Field.intern fld)))
              | _ ->
                  let arg = process ctx arg in
                  Synth (Raw.App (fn, arg))))
      | Constr (head, args) ->
          let arg = process ctx arg in
          Raw.Constr (head, Snoc (args, arg))
      | _ -> fatal (Nonsynthesizing "application head"))
  | Placeholder -> fatal (Unimplemented "unification arguments")
  | Ident x -> (
      match Bwv.index (Some x) ctx with
      | Some n -> Synth (Var (n, None))
      | None -> (
          match Scope.lookup x with
          | Some c -> Synth (Const c)
          | None -> fatal (Unbound_variable x)))
  | Constr ident -> Raw.Constr (Constr.intern ident, Emp)
  | Field _ -> fatal (Anomaly "Field is head")
  | Numeral n -> process_numeral n
