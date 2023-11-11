open Util
open Dim
open Core
open Raw
open Bwd
open Reporter
open Notation

(* The individual notation implementations are passed a list of "observations" which are the names, terms, and flags seen and recorded while parsing that notation.  They extract its pieces using these functions, which ignore all flags except those specifically requested (since other flags might pertain to other notations that got partially parsed).  *)

let rec get_flag flags (obs : observation list) =
  match obs with
  | [] -> None
  | Flagged f :: rest -> if List.mem f flags then Some f else get_flag flags rest
  | Constr _ :: _ | Field _ :: _ | Name _ :: _ | Term _ :: _ -> None

let rec get_name (obs : observation list) =
  match obs with
  | [] -> fatal (Anomaly "Missing name")
  | Flagged _ :: rest -> get_name rest
  | Name x :: rest -> (x, rest)
  | Constr _ :: _ | Field _ :: _ | Term _ :: _ -> fatal (Anomaly "Missing name")

let rec get_names (obs : observation list) =
  match obs with
  | [] | Constr _ :: _ | Field _ :: _ | Term _ :: _ -> ([], obs)
  | Flagged _ :: rest -> get_names rest
  | Name x :: rest ->
      let names, rest = get_names rest in
      (x :: names, rest)

let rec get_constr (obs : observation list) =
  match obs with
  | [] -> fatal (Anomaly "Missing constr")
  | Flagged _ :: rest -> get_constr rest
  | Constr x :: rest -> (x, rest)
  | Name _ :: _ | Field _ :: _ | Term _ :: _ -> fatal (Anomaly "Missing constr")

let rec get_term (obs : observation list) =
  match obs with
  | [] -> fatal (Anomaly "Missing term")
  | Flagged _ :: rest -> get_term rest
  | Constr _ :: _ | Field _ :: _ | Name _ :: _ -> fatal (Anomaly "Missing term")
  | Term x :: rest -> (x, rest)

let rec get_next (obs : observation list) =
  match obs with
  | [] -> `Done
  | Flagged _ :: rest -> get_next rest
  | Constr x :: rest -> `Constr (x, rest)
  | Field x :: rest -> `Field (x, rest)
  | Name x :: rest -> `Name (x, rest)
  | Term x :: rest -> `Term (x, rest)

(* Just a sanity check at the end that there's nothing left. *)
let rec get_done (obs : observation list) =
  match obs with
  | [] -> ()
  | Flagged _ :: rest -> get_done rest
  | _ :: _ -> fatal (Anomaly "Extra stuff")

open Monad.Ops (Monad.Maybe)

(* At present we only know how to compile natural number numerals. *)
let compile_numeral (n : Q.t) =
  let rec compile_nat (n : Z.t) =
    (* TODO: Would be better not to hardcode these. *)
    if n = Z.zero then Raw.Constr (Constr.intern "zero", Emp)
    else Raw.Constr (Constr.intern "suc", Snoc (Emp, compile_nat (Z.sub n Z.one))) in
  if n.den = Z.one && n.num >= Z.zero then compile_nat n.num else fatal (Unsupported_numeral n)

(* Now the master compilation function.  Note that this function calls the "compile" functions registered for individual notations, but those functions will be defined to call *this* function on their constituents, so we have some "open recursion" going on. *)

let rec compile : type n. (string option, n) Bwv.t -> parse -> n check =
 fun ctx res ->
  match res with
  | Notn (n, args) -> (compiler n).compile ctx args
  (* "Application" nodes in result trees are used for anything that syntactically *looks* like an application.  In addition to actual applications of functions, this includes applications of constructors and symbols, and also field projections.  *)
  | App (fn, arg) -> (
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
  | Name x -> (
      match Bwv.index (Some x) ctx with
      | Some n -> Synth (Var (n, None))
      | None -> (
          match Scope.lookup x with
          | Some c -> Synth (Const c)
          | None -> fatal (Unbound_variable x)))
  | Constr name -> Raw.Constr (Constr.intern name, Emp)
  | Field _ -> fatal (Anomaly "Field is head")
  | Numeral n -> compile_numeral n
  | Abs (_, [], body) -> compile ctx body
  | Abs (cube, x :: names, body) ->
      let body = compile (Snoc (ctx, x)) (Abs (cube, names, body)) in
      Lam (cube, body)
