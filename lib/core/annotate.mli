open Syntax
open Value
open Term
open Status
open Reporter

type 'a located = 'a Asai.Range.located

val ty : ('a, 'b) Ctx.t -> kinetic value -> unit
val tm : ('a, 'b) Ctx.t -> ('b, 's) term -> unit
val ctx : ('b, 's) status -> ('a, 'b) Ctx.t -> unit

type ctx_handler = {
  handle : 'a 'b 's. (('b, 's) status * ('a, 'b) Ctx.t) Asai.Range.located -> unit;
}

type tm_handler = printable located -> unit
type ty_handler = printable located -> unit

val run : ?ctx:ctx_handler -> ?tm:tm_handler -> ?ty:ty_handler -> (unit -> 'a) -> 'a
