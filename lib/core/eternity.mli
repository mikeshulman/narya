open Util
open Syntax
open Term

val find : ('a, 'b) Meta.t -> ('a, 'b) Metadef.def

val add :
  ('b, 's) Meta.t ->
  (string option, 'a) Bwv.t ->
  ('a, 'b) Termctx.t ->
  ('b, kinetic) term ->
  's energy ->
  unit

val unsolved : unit -> bool
val run_empty : (unit -> 'a) -> 'a
val end_command : unit -> int
