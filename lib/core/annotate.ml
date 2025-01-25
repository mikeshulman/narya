(* This module should not be opened, but used qualified. *)
open Syntax
open Value
open Term

type _ Effect.t +=
  | Ty : (('a, 'b) Ctx.t * kinetic value) Asai.Range.located -> unit Effect.t
  | Tm : (('a, 'b) Ctx.t * ('b, 's) term) Asai.Range.located -> unit Effect.t

let ty ctx v = Effect.perform (Ty (Asai.Range.locate_opt (Reporter.get_loc ()) (ctx, v)))
let tm ctx x = Effect.perform (Tm (Asai.Range.locate_opt (Reporter.get_loc ()) (ctx, x)))

open Effect.Deep

type ty_handler = { handle : 'a 'b. (('a, 'b) Ctx.t * kinetic value) Asai.Range.located -> unit }
type tm_handler = { handle : 'a 'b 's. (('a, 'b) Ctx.t * ('b, 's) term) Asai.Range.located -> unit }

let trivial_ty_handler : ty_handler = { handle = (fun _ -> ()) }
let trivial_tm_handler : tm_handler = { handle = (fun _ -> ()) }

let handler :
    type b a. tm:tm_handler -> ty:ty_handler -> b Effect.t -> ((b, a) continuation -> a) option =
 fun ~tm ~ty -> function
  | Tm p ->
      Some
        (fun k ->
          tm.handle p;
          continue k ())
  | Ty p ->
      Some
        (fun k ->
          ty.handle p;
          continue k ())
  | _ -> None

let run (type a) ?(tm = trivial_tm_handler) ?(ty = trivial_ty_handler) (f : unit -> a) =
  try_with f () { effc = (fun e -> handler ~tm ~ty e) }
