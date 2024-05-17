open Util
open Syntax
open Term

type (_, _) data =
  | Data : {
      vars : (string option, 'a) Bwv.t;
      termctx : ('a, 'b) Termctx.t;
      ty : ('b, kinetic) term;
      tm : ('b, 's) term option;
      energy : 's energy;
    }
      -> (unit, 'b * 's) data

val find_opt : ('a, 'b) Meta.t -> (unit, 'a * 'b) data option

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
