open Util
open Core
open Parser

(* The current context of assumptions, including names. *)
type ctx = Ctx : ('n, 'b) Ctx.t * (string option, 'n) Bwv.t -> ctx

let ectx = Ctx (Ctx.empty, Emp)
let context = ref ectx

(* Functions to synth and check terms *)

let parse_term : type n. (string option, n) Bwv.t -> string -> n Raw.check =
 fun names tm ->
  let (Term tm) = Parse.term (`String { title = Some "user-supplied term"; content = tm }) in
  Postprocess.process names tm

module Terminal = Asai.Tty.Make (Core.Reporter.Code)

let synth (tm : string) : Value.value * Value.value =
  let (Ctx (ctx, names)) = !context in
  Reporter.run ~emit:Terminal.display ~fatal:(fun d ->
      Terminal.display d;
      raise (Failure "Failed to synthesize"))
  @@ fun () ->
  match parse_term names tm with
  | Synth raw ->
      let syn, ty = Check.synth ctx raw in
      let esyn = Ctx.eval ctx syn in
      (esyn, ty)
  | _ -> Reporter.fatal (Nonsynthesizing "toplevel synth")

let check (tm : string) (ty : Value.value) : Value.value =
  let (Ctx (ctx, names)) = !context in
  Reporter.run ~emit:Terminal.display ~fatal:(fun d ->
      Terminal.display d;
      raise (Failure "Failed to check"))
  @@ fun () -> Ctx.eval ctx (Check.check ctx (parse_term names tm) ty)

(* Assert that a term *doesn't* synthesize or check, and possibly ensure it gives a specific error code. *)

let unsynth : ?code:Reporter.Code.t -> ?short:string -> string -> unit =
 fun ?code ?short tm ->
  let (Ctx (ctx, names)) = !context in
  Reporter.try_with ~fatal:(fun d ->
      match code with
      | None -> (
          match short with
          | None -> ()
          | Some str ->
              if Reporter.Code.short_code d.message = str then ()
              else (
                Terminal.display d;
                raise (Failure "Unexpected error code")))
      | Some c ->
          if d.message = c then ()
          else (
            Terminal.display d;
            raise (Failure "Unexpected error code")))
  @@ fun () ->
  match parse_term names tm with
  | Synth raw ->
      let _ = Check.synth ctx raw in
      raise (Failure "Synthesis success")
  | _ -> Reporter.fatal (Nonsynthesizing "top-level unsynth")

let uncheck : ?code:Reporter.Code.t -> ?short:string -> string -> Value.value -> unit =
 fun ?code ?short tm ty ->
  let (Ctx (ctx, names)) = !context in
  Reporter.try_with ~fatal:(fun d ->
      match code with
      | None -> (
          match short with
          | None -> ()
          | Some str ->
              if Reporter.Code.short_code d.message = str then ()
              else (
                Terminal.display d;
                raise (Failure "Unexpected error code")))
      | Some c ->
          if d.message = c then ()
          else (
            Terminal.display d;
            raise (Failure "Unexpected error code")))
  @@ fun () ->
  let _ = Check.check ctx (parse_term names tm) ty in
  raise (Failure "Checking success")

(* Assert that a term doesn't parse *)

let unparse (tm : string) : unit =
  let (Ctx (_, names)) = !context in
  Reporter.try_with
    ~fatal:(fun _ -> ())
    (fun () ->
      let _ = parse_term names tm in
      raise (Failure "Unexpected parse success"))

(* Add to the context of assumptions *)

let assume (x : string) (ty : Value.value) : Value.value =
  let (Ctx (ctx, names)) = !context in
  context := Ctx (Ctx.ext ctx ty, Snoc (names, Some x));
  fst (synth x)

(* Check that two terms are, or aren't, equal, at a type or synthesizing *)

let equal_at (tm1 : Value.value) (tm2 : Value.value) (ty : Value.value) : unit =
  let (Ctx (ctx, _)) = !context in
  if Option.is_some (Equal.equal_at (Ctx.length ctx) tm1 tm2 ty) then ()
  else raise (Failure "Unequal terms")

let unequal_at (tm1 : Value.value) (tm2 : Value.value) (ty : Value.value) : unit =
  let (Ctx (ctx, _)) = !context in
  if Option.is_none (Equal.equal_at (Ctx.length ctx) tm1 tm2 ty) then ()
  else raise (Failure "Equal terms")

let equal (tm1 : Value.value) (tm2 : Value.value) : unit =
  let (Ctx (ctx, _)) = !context in
  if Option.is_some (Equal.equal_val (Ctx.length ctx) tm1 tm2) then ()
  else raise (Failure "Unequal terms")

let unequal (tm1 : Value.value) (tm2 : Value.value) : unit =
  let (Ctx (ctx, _)) = !context in
  if Option.is_none (Equal.equal_val (Ctx.length ctx) tm1 tm2) then ()
  else raise (Failure "Equal terms")

let run f =
  Reporter.run ~emit:Terminal.display ~fatal:(fun d ->
      Terminal.display d;
      raise (Failure "Fatal error"))
  @@ fun () ->
  Builtins.run @@ fun () -> Scope.run f
