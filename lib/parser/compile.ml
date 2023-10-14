open Util
open Core
open Raw
open Bwd
open Notations
open Logger

(* If we weren't using intrinsically well-scoped De Bruijn indices, then the typechecking context and the type of raw terms would be simply ordinary types, and we could use the one as the parsing State and the other as the parsing Result.  However, the Fmlib parser isn't set up to allow families of state and result types (and it would be tricky to do that correctly anyway), so instead we record the result of parsing as a syntax tree with names, and have a separate step of "compilation" that makes it into a raw term. *)

type observation = Flag of flag | Constr of string | Name of string option | Term of res

(* A "result" is traditionally known as a "parse tree" (not to be confused with our "notation trees"). *)
and res =
  | Notn of Notation.t * observation list
  | App of res * res
  | Name of string
  | Constr of string
  | Field of string
  | Numeral of float
  | Abs of string option list * res

(* These "result trees" don't know anything about the *meanings* of notations either; those are registered separately in a hashtable and called by the compile function below.  *)

type compiler = { compile : 'n. (string option, 'n) Bwv.t -> observation list -> 'n check option }

let compilers : (Notation.t, compiler) Hashtbl.t = Hashtbl.create 16
let add_compiler n c = Hashtbl.add compilers n c

(* The individual notation implementations are passed a list of "observations" which are the names, terms, and flags seen and recorded while parsing that notation.  They extract its pieces using these functions, which ignore all flags except those specifically requested (since other flags might pertain to other notations that got partially parsed).  *)

let rec get_flag flags obs =
  match obs with
  | [] -> None
  | Flag f :: rest -> if List.mem f flags then Some f else get_flag flags rest
  | Constr _ :: _ | Name _ :: _ | Term _ :: _ -> None

let rec get_name obs =
  match obs with
  | [] -> raise (Failure "Missing name")
  | Flag _ :: rest -> get_name rest
  | Name x :: rest -> (x, rest)
  | Constr _ :: _ | Term _ :: _ -> raise (Failure "Missing name")

let rec get_term obs =
  match obs with
  | [] -> raise (Failure "Missing term")
  | Flag _ :: rest -> get_term rest
  | Constr _ :: _ | Name _ :: _ -> raise (Failure "Missing term")
  | Term x :: rest -> (x, rest)

let rec get_next obs =
  match obs with
  | [] -> `Done
  | Flag _ :: rest -> get_next rest
  | Constr x :: rest -> `Constr (x, rest)
  | Name x :: rest -> `Name (x, rest)
  | Term x :: rest -> `Term (x, rest)

(* Just a sanity check at the end that there's nothing left. *)
let rec get_done obs =
  match obs with
  | [] -> ()
  | Flag _ :: rest -> get_done rest
  | _ :: _ -> raise (Failure "Extra stuff")

open Monad.Ops (Monad.Maybe)

(* At present we only know how to compile natural number numerals. *)
let compile_numeral n =
  let rec compile_nat n =
    if n = 0 then Raw.Constr (Constr.intern "0", Emp)
    else Raw.Constr (Constr.intern "1", Snoc (Emp, compile_nat (n - 1))) in
  let frac, n = modf n in
  if classify_float frac = FP_zero && n >= 0. then return (compile_nat (int_of_float n)) else None

(* Now the master compilation function.  Note that this function calls the "compile" functions registered for individual notatations, but those functions will be defined to call *this* function on their constituents, so we have some "open recursion" going on. *)

(* TODO: This function should probably raise Bugs (or maybe some Errors) rather than returning None on failure. *)
let rec compile : type n. (string option, n) Bwv.t -> res -> n check option =
 fun ctx res ->
  match res with
  | Notn (n, args) ->
      let c = Hashtbl.find compilers n in
      c.compile ctx args
  (* "Application" nodes in result trees are used for anything that syntactically *looks* like an application.  In addition to actual applications of functions, this includes applications of constructors and symbols, and also field projections.  *)
  | App (fn, arg) -> (
      let* fn = compile ctx fn in
      match fn with
      | Synth fn -> (
          match fn with
          | Symbol (s, (Suc _ as mn), args) ->
              let* arg = compile ctx arg in
              return (Synth (Symbol (s, N.suc_plus'' mn, Snoc (args, arg))))
          | _ -> (
              match arg with
              | Field fld -> return (Synth (Field (fn, Field.intern fld)))
              | _ ->
                  let* arg = compile ctx arg in
                  return (Synth (Raw.App (fn, arg)))))
      | Constr (head, args) ->
          let* arg = compile ctx arg in
          return (Raw.Constr (head, Snoc (args, arg)))
      | _ -> None)
  | Name x -> (
      match Bwv.index (Some x) ctx with
      | Some n -> return (Synth (Var n))
      | None -> (
          match Scope.lookup x with
          | Some c -> return (Synth (Const c))
          | None -> die Unbound_variable x))
  | Constr name -> return (Raw.Constr (Constr.intern name, Emp))
  | Field _ -> None (* Field projections have to occur as an "argument" to App. *)
  | Numeral n -> compile_numeral n
  | Abs ([], body) -> compile ctx body
  | Abs (x :: names, body) ->
      let* body = compile (Snoc (ctx, x)) (Abs (names, body)) in
      return (Lam body)
