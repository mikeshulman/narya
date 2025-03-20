(* This module should not be opened, but used qualified. *)
open Status
open Reporter
open Printable

type 'a located = 'a Asai.Range.located

let locate_opt = Asai.Range.locate_opt

type _ Effect.t +=
  | Ty : printable located -> unit Effect.t
  | Tm : printable located -> unit Effect.t
  | Ctx : (('b, 's) status * ('a, 'b) Ctx.t * 'a Raw.check located) -> unit Effect.t

let ty ctx v = Effect.perform (Ty (locate_opt (get_loc ()) (PVal (ctx, v))))
let tm ctx x = Effect.perform (Tm (locate_opt (get_loc ()) (PTerm (ctx, x))))
let ctx status ctx tm = Effect.perform (Ctx (status, ctx, tm))

open Effect.Deep

type ctx_handler = {
  handle : 'a 'b 's. ('b, 's) status -> ('a, 'b) Ctx.t -> 'a Raw.check located -> unit;
}

type tm_handler = printable located -> unit
type ty_handler = printable located -> unit

let trivial_ctx_handler : ctx_handler = { handle = (fun _ _ _ -> ()) }

let handler : type b a.
    ctx:ctx_handler ->
    tm:tm_handler ->
    ty:ty_handler ->
    b Effect.t ->
    ((b, a) continuation -> a) option =
 fun ~ctx ~tm ~ty -> function
  | Tm p ->
      Some
        (fun k ->
          tm p;
          continue k ())
  | Ty p ->
      Some
        (fun k ->
          ty p;
          continue k ())
  | Ctx (s, c, tm) ->
      Some
        (fun k ->
          ctx.handle s c tm;
          continue k ())
  | _ -> None

let run (type a) ?(ctx = trivial_ctx_handler) ?(tm = fun _ -> ()) ?(ty = fun _ -> ())
    (f : unit -> a) =
  try_with f () { effc = (fun e -> handler ~ctx ~tm ~ty e) }
