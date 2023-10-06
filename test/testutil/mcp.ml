open Util
open Core
open Parser

(* The current context of assumptions, including names. *)
type ctx = Ctx : 'n Ctx.t * (string option, 'n) Bwv.t -> ctx

let ectx = Ctx (Ctx.empty, Emp)
let context = ref ectx

(* Functions to synth and check terms *)

let parse_term : type n. (string option, n) Bwv.t -> string -> (n Raw.check, string) result =
 fun names tm ->
  match Parse.parse !Builtins.builtins tm with
  | Error str -> Error str
  | Ok res -> (
      match Compile.compile names res with
      | None -> Error "Compilation error"
      | Some t -> Ok t)

exception Synthesis_failure of Check.CheckErr.t
exception Checking_failure of Check.CheckErr.t

let synth (tm : string) : Value.value * Value.value =
  let (Ctx (ctx, names)) = !context in
  match parse_term names tm with
  | Ok (Synth raw) -> (
      match Check.synth ctx raw with
      | Ok (syn, ty) ->
          let esyn = Ctx.eval ctx syn in
          (esyn, ty)
      | Error e -> raise (Synthesis_failure e))
  | Ok _ -> raise (Failure "Non-synthesizing")
  | Error str ->
      print_endline str;
      raise (Failure "Parse error")

let check (tm : string) (ty : Value.value) : Value.value =
  let (Ctx (ctx, names)) = !context in
  match parse_term names tm with
  | Ok raw -> (
      match Check.check ctx raw ty with
      | Ok chk -> Ctx.eval ctx chk
      | Error e -> raise (Checking_failure e))
  | Error str ->
      print_endline str;
      raise (Failure "Parse error")

(* Assert that a term *doesn't* synthesize or check *)

let unsynth (tm : string) : unit =
  let (Ctx (ctx, names)) = !context in
  match parse_term names tm with
  | Ok (Synth raw) -> (
      match Check.synth ctx raw with
      | Error _ -> ()
      | Ok _ -> raise (Failure "Synthesis success"))
  | Ok _ -> raise (Failure "Non-synthesizing")
  | Error str ->
      print_endline str;
      raise (Failure "Parse error")

let uncheck (tm : string) (ty : Value.value) : unit =
  let (Ctx (ctx, names)) = !context in
  match parse_term names tm with
  | Ok raw -> (
      match Check.check ctx raw ty with
      | Error _ -> ()
      | Ok _ -> raise (Failure "Checking success"))
  | Error str ->
      print_endline str;
      raise (Failure "Parse error")

(* Assert that a term doesn't parse *)

let unparse (tm : string) : unit =
  let (Ctx (_, names)) = !context in
  match parse_term names tm with
  | Ok _ -> raise (Failure "Unexpected parse success")
  | Error _ -> ()

(* Add to the context of assumptions *)

let assume (x : string) (ty : Value.value) : Value.value =
  let (Ctx (ctx, names)) = !context in
  context := Ctx (Ctx.ext ctx ty, Snoc (names, Some x));
  fst (synth x)

(* Check that two terms are, or aren't, equal, at a type or synthesizing *)

let equal_at (tm1 : Value.value) (tm2 : Value.value) (ty : Value.value) : unit =
  let (Ctx (ctx, _)) = !context in
  if Option.is_some (Equal.equal_at (Ctx.level ctx) tm1 tm2 ty) then ()
  else raise (Failure "Unequal terms")

let unequal_at (tm1 : Value.value) (tm2 : Value.value) (ty : Value.value) : unit =
  let (Ctx (ctx, _)) = !context in
  if Option.is_none (Equal.equal_at (Ctx.level ctx) tm1 tm2 ty) then ()
  else raise (Failure "Equal terms")

let equal (tm1 : Value.value) (tm2 : Value.value) : unit =
  let (Ctx (ctx, _)) = !context in
  if Option.is_some (Equal.equal_val (Ctx.level ctx) tm1 tm2) then ()
  else raise (Failure "Unequal terms")

let unequal (tm1 : Value.value) (tm2 : Value.value) : unit =
  let (Ctx (ctx, _)) = !context in
  if Option.is_none (Equal.equal_val (Ctx.level ctx) tm1 tm2) then ()
  else raise (Failure "Equal terms")
