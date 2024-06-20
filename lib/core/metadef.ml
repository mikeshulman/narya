(* This module should not be opened, but used qualified. *)

open Util
open Syntax
open Term

type ('b, 's) value = [ `None | `Nonrec of ('b, 's) term ]

type ('a, 'b, 's) data = {
  vars : (string option, 'a) Bwv.t option;
  termctx : ('a, 'b) Termctx.t;
  ty : ('b, kinetic) term;
  tm : ('b, 's) value;
  energy : 's energy;
}

type (_, _) info =
  | Metainfo :
      ('a, 'b, 's) data
      (* This weird-looking parametrization is to match the implementation of Meta.Map. *)
      -> (unit, 'b * 's) info

type (_, _) def = Metadef : ('a, 'b, 's) data -> ('b, 's) def

let def_of_info = function
  | Metainfo d -> Metadef d

(* Both eternal and global state include definitions of metavariables.  We store these in an intrinsically well-typed map, since metavariables are parametrized by their context length and energy. *)

module Map = Meta.Map.Make (struct
  type ('x, 'bs) t = ('x, 'bs) info
end)
