open Util
open Tbwd
open Dim
open Core
open Term
module StringMap : module type of Map.Make (String)

val default : unit -> string

type 'n t

val empty : emp t
val lookup : 'n t -> 'n index -> string list
val lookup_field : 'n t -> 'n index -> string -> string list option
val add_cube : 'n D.t -> 'b t -> string option -> string option * ('b, 'n) snoc t
val add_cube_autogen : 'n D.t -> 'b t -> string * ('b, 'n) snoc t
val add : 'b t -> 'n variables -> 'n variables * ('b, 'n) snoc t
val of_ctx : ('a, 'b) Ctx.t -> 'b t

val uniquify_vars :
  (string option, 'a) Bwv.t -> (string * [ `Original | `Renamed ], 'a) Bwv.t * emp t

val unsafe_add : 'b t -> 'n variables -> (string, string) Abwd.t -> ('b, 'n) snoc t
