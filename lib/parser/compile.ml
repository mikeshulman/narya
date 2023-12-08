open Util
open Dim
open Core
open Raw
open Bwd
open Reporter
open Notation
open Monad.Ops (Monad.Maybe)

(* At present we only know how to compile natural number numerals. *)
let compile_numeral (n : Q.t) =
  let rec compile_nat (n : Z.t) =
    (* TODO: Would be better not to hardcode these. *)
    if n = Z.zero then Raw.Constr (Constr.intern "zero", Emp)
    else Raw.Constr (Constr.intern "suc", Snoc (Emp, compile_nat (Z.sub n Z.one))) in
  if n.den = Z.one && n.num >= Z.zero then compile_nat n.num else fatal (Unsupported_numeral n)

(* Now the master compilation function.  Note that this function calls the "compile" functions registered for individual notations, but those functions will be defined to call *this* function on their constituents, so we have some "open recursion" going on. *)

let rec compile : type n lt ls rt rs. (string option, n) Bwv.t -> (lt, ls, rt, rs) parse -> n check
    =
 fun ctx res ->
  match res with
  | Notn n -> (compiler (notn n)).compile ctx (args n)
  (* "Application" nodes in result trees are used for anything that syntactically *looks* like an application.  In addition to actual applications of functions, this includes applications of constructors and symbols, and also field projections.  *)
  | App { fn; arg; _ } -> (
      let fn = compile ctx fn in
      match fn with
      | Synth fn -> (
          match fn with
          | Act (str, s, None) -> (
              match compile ctx arg with
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
                  let arg = compile ctx arg in
                  Synth (Raw.App (fn, arg))))
      | Constr (head, args) ->
          let arg = compile ctx arg in
          Raw.Constr (head, Snoc (args, arg))
      | _ -> fatal (Nonsynthesizing "application head"))
  | Ident x -> (
      match Bwv.index (Some x) ctx with
      | Some n -> Synth (Var (n, None))
      | None -> (
          match Scope.lookup x with
          | Some c -> Synth (Const c)
          | None -> fatal (Unbound_variable x)))
  | Constr ident -> Raw.Constr (Constr.intern ident, Emp)
  | Field _ -> fatal (Anomaly "Field is head")
  | Numeral n -> compile_numeral n
