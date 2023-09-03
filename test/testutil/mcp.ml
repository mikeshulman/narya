open Util
open Core
open Parser

(* The current context of assumptions, including names. *)
type ctx = Ctx : 'n Ctx.t * (string option, 'n) Bwv.t -> ctx

let ectx = Ctx (Ctx.empty, Emp)
let context = ref ectx

(* Functions to synth and check terms *)

let synth (tm : string) : Value.value * Value.value =
  let (Ctx (ctx, names)) = !context in
  let raw = Parse.term names tm in
  match raw with
  | [] -> raise (Failure "Parse failure")
  | _ :: _ :: _ -> raise (Failure "Ambiguous parse")
  | [ Synth raw ] -> (
      match Check.synth ctx raw with
      | Some (syn, ty) ->
          let esyn = Ctx.eval ctx syn in
          (esyn, ty)
      | None -> raise (Failure "Synthesis failure"))
  | _ -> raise (Failure "Non-synthesizing")

let check (tm : string) (ty : Value.value) : Value.value =
  let (Ctx (ctx, names)) = !context in
  let raw = Parse.term names tm in
  match raw with
  | [] -> raise (Failure "Parse failure")
  | _ :: _ :: _ -> raise (Failure "Ambiguous parse")
  | [ raw ] -> (
      match Check.check ctx raw ty with
      | Some chk -> Ctx.eval ctx chk
      | None -> raise (Failure "Checking failure"))

(* Assert that a term *doesn't* synthesize or check *)

let unsynth (tm : string) : unit =
  let (Ctx (ctx, names)) = !context in
  let raw = Parse.term names tm in
  match raw with
  | [] -> raise (Failure "Parse failure")
  | _ :: _ :: _ -> raise (Failure "Ambiguous parse")
  | [ Synth raw ] -> (
      match Check.synth ctx raw with
      | None -> ()
      | Some _ -> raise (Failure "Synthesis success"))
  | _ -> raise (Failure "Non-synthesizing")

let uncheck (tm : string) (ty : Value.value) : unit =
  let (Ctx (ctx, names)) = !context in
  let raw = Parse.term names tm in
  match raw with
  | [] -> raise (Failure "Parse failure")
  | _ :: _ :: _ -> raise (Failure "Ambiguous parse")
  | [ raw ] -> (
      match Check.check ctx raw ty with
      | None -> ()
      | Some _ -> raise (Failure "Checking success"))

(* Assert that a term doesn't parse *)

let unparse (tm : string) : unit =
  let (Ctx (_, names)) = !context in
  let raw = Parse.term names tm in
  match raw with
  | [ _ ] -> raise (Failure "Unexpected parse success")
  | _ :: _ :: _ -> raise (Failure "Unexpected parse ambiguity")
  | [] -> ()

let ambparse (tm : string) : unit =
  let (Ctx (_, names)) = !context in
  let raw = Parse.term names tm in
  match raw with
  | [ _ ] -> raise (Failure "Unexpected parse success")
  | [] -> raise (Failure "Unexpected parse failure")
  | _ :: _ :: _ -> ()

(* Add to the context of assumptions *)

let assume (x : string) (ty : Value.value) : Value.value =
  let (Ctx (ctx, names)) = !context in
  context := Ctx (Ctx.ext ctx ty, Snoc (names, Some x));
  fst (synth x)

(* Check that two terms are, or aren't, equal, at a type or synthesizing *)

let equal_at (tm1 : Value.value) (tm2 : Value.value) (ty : Value.value) : unit =
  let (Ctx (ctx, _)) = !context in
  if Option.is_some (Equal.equal_at ctx tm1 tm2 ty) then () else raise (Failure "Unequal terms")

let unequal_at (tm1 : Value.value) (tm2 : Value.value) (ty : Value.value) : unit =
  let (Ctx (ctx, _)) = !context in
  if Option.is_none (Equal.equal_at ctx tm1 tm2 ty) then () else raise (Failure "Equal terms")

let equal (tm1 : Value.value) (tm2 : Value.value) : unit =
  let (Ctx (ctx, _)) = !context in
  if Option.is_some (Equal.equal_val ctx tm1 tm2) then () else raise (Failure "Unequal terms")

let unequal (tm1 : Value.value) (tm2 : Value.value) : unit =
  let (Ctx (ctx, _)) = !context in
  if Option.is_none (Equal.equal_val ctx tm1 tm2) then () else raise (Failure "Equal terms")
