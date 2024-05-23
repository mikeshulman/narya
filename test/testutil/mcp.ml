open Util
open Core
open Parser
open Syntax
open Value
open Asai.Range

let () =
  Dim.Endpoints.set_len 2;
  Dim.Endpoints.set_internal true

(* The current context of assumptions, including names. *)
type ctx = Ctx : ('n, 'b) Ctx.t * (string option, 'n) Bwv.t -> ctx

let ectx = Ctx (Ctx.empty, Emp)
let context = ref ectx

(* Functions to synth and check terms *)

let parse_term : type n. (string option, n) Bwv.t -> string -> n Raw.check located =
 fun names tm ->
  let p = Parse.Term.parse (`String { content = tm; title = Some "user-supplied term" }) in
  let (Term tm) = Parse.Term.final p in
  Postprocess.process names tm

module Terminal = Asai.Tty.Make (Core.Reporter.Code)

let synth (tm : string) : kinetic value * kinetic value =
  let (Ctx (ctx, names)) = !context in
  Reporter.run ~emit:Terminal.display ~fatal:(fun d ->
      Terminal.display d;
      raise (Failure "Failed to synthesize"))
  @@ fun () ->
  match parse_term names tm with
  | { value = Synth raw; loc } ->
      let syn, ty = Check.synth ctx { value = raw; loc } in
      let esyn = Ctx.eval_term ctx syn in
      (esyn, ty)
  | _ -> Reporter.fatal (Nonsynthesizing "toplevel synth")

let check (tm : string) (ty : kinetic value) : kinetic value =
  let (Ctx (ctx, names)) = !context in
  Reporter.run ~emit:Terminal.display ~fatal:(fun d ->
      Terminal.display d;
      raise (Failure "Failed to check"))
  @@ fun () -> Ctx.eval_term ctx (Check.check Kinetic ctx (parse_term names tm) ty)

(* Assert that a term *doesn't* synthesize or check, and possibly ensure it gives a specific error code. *)

let unsynth : ?print:unit -> ?code:Reporter.Code.t -> ?short:string -> string -> unit =
 fun ?print ?code ?short tm ->
  let (Ctx (ctx, names)) = !context in
  Reporter.try_with ~fatal:(fun d ->
      match code with
      | None -> (
          match short with
          | None -> if Option.is_some print then Terminal.display d
          | Some str ->
              if Reporter.Code.short_code d.message = str then (
                if Option.is_some print then Terminal.display d)
              else (
                Terminal.display d;
                raise (Failure "Unexpected error code")))
      | Some c ->
          if d.message = c then (if Option.is_some print then Terminal.display d)
          else (
            Terminal.display d;
            raise (Failure "Unexpected error code")))
  @@ fun () ->
  match parse_term names tm with
  | { value = Synth raw; loc } ->
      let _ = Check.synth ctx { value = raw; loc } in
      raise (Failure "Synthesis success")
  | _ -> Reporter.fatal (Nonsynthesizing "top-level unsynth")

let uncheck :
    ?print:unit -> ?code:Reporter.Code.t -> ?short:string -> string -> kinetic value -> unit =
 fun ?print ?code ?short tm ty ->
  let (Ctx (ctx, names)) = !context in
  Reporter.try_with ~fatal:(fun d ->
      match code with
      | None -> (
          match short with
          | None -> if Option.is_some print then Terminal.display d
          | Some str ->
              if Reporter.Code.short_code d.message = str then (
                if Option.is_some print then Terminal.display d)
              else (
                Terminal.display d;
                raise (Failure "Unexpected error code")))
      | Some c ->
          if d.message = c then (if Option.is_some print then Terminal.display d)
          else (
            Terminal.display d;
            raise (Failure "Unexpected error code")))
  @@ fun () ->
  let _ = Check.check Kinetic ctx (parse_term names tm) ty in
  raise (Failure "Checking success")

(* Assert that a term doesn't parse *)

let unparse : ?print:unit -> string -> unit =
 fun ?print tm ->
  let (Ctx (_, names)) = !context in
  Reporter.try_with
    ~fatal:(fun d -> if Option.is_some print then Terminal.display d)
    (fun () ->
      let _ = parse_term names tm in
      raise (Failure "Unexpected parse success"))

(* Add to the context of assumptions *)

let assume (x : string) (ty : kinetic value) : kinetic value =
  let (Ctx (ctx, names)) = !context in
  context := Ctx (Ctx.ext ctx (Some x) ty, Bwv.snoc names (Some x));
  fst (synth x)

(* Check that two terms are, or aren't, equal, at a type or synthesizing *)

let equal_at (tm1 : kinetic value) (tm2 : kinetic value) (ty : kinetic value) : unit =
  let (Ctx (ctx, _)) = !context in
  if Option.is_some (Equal.equal_at (Ctx.length ctx) tm1 tm2 ty) then ()
  else raise (Failure "Unequal terms")

let unequal_at (tm1 : kinetic value) (tm2 : kinetic value) (ty : kinetic value) : unit =
  let (Ctx (ctx, _)) = !context in
  if Option.is_none (Equal.equal_at (Ctx.length ctx) tm1 tm2 ty) then ()
  else raise (Failure "Equal terms")

let equal (tm1 : kinetic value) (tm2 : kinetic value) : unit =
  let (Ctx (ctx, _)) = !context in
  if Option.is_some (Equal.equal_val (Ctx.length ctx) tm1 tm2) then ()
  else raise (Failure "Unequal terms")

let unequal (tm1 : kinetic value) (tm2 : kinetic value) : unit =
  let (Ctx (ctx, _)) = !context in
  if Option.is_none (Equal.equal_val (Ctx.length ctx) tm1 tm2) then ()
  else raise (Failure "Equal terms")

let run f = Repl.run f
