open Util
open Syntax
open Term

type ('b, 's) meta_value = [ `None | `Nonrec of ('b, 's) term ]

type (_, _) metadef =
  | Metadef : {
      vars : (string option, 'a) Bwv.t option;
      termctx : ('a, 'b) Termctx.t;
      ty : ('b, kinetic) term;
      tm : ('b, 's) meta_value;
      energy : 's energy;
    }
      -> (unit, 'b * 's) metadef

module Map : module type of Meta.Map.Make (struct
  type ('x, 'bs) t = ('x, 'bs) metadef
end)

val find_opt : ('a, 'b) Meta.t -> (unit, 'a * 'b) metadef option

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
