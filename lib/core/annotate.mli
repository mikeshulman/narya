open Syntax
open Value
open Term

val ty : ('a, 'b) Ctx.t -> kinetic value -> unit
val tm : ('a, 'b) Ctx.t -> ('b, 's) term -> unit

type ty_handler = { handle : 'a 'b. (('a, 'b) Ctx.t * kinetic value) Asai.Range.located -> unit }
type tm_handler = { handle : 'a 'b 's. (('a, 'b) Ctx.t * ('b, 's) term) Asai.Range.located -> unit }

val run : ?tm:tm_handler -> ?ty:ty_handler -> (unit -> 'a) -> 'a
