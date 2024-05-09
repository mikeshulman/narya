open Bwd
open Util
open Tbwd
open Dim
open Syntax
open Term
module StringMap : module type of Map.Make (String)

type 'n t

val empty : emp t
val lookup : 'n t -> 'n index -> string list
val add_cube : 'n D.t -> 'b t -> string option -> string option * ('b, 'n) snoc t
val add_cube_autogen : 'n D.t -> 'b t -> string * ('b, 'n) snoc t
val add : 'b t -> 'n variables -> 'n variables * ('b, 'n) snoc t

val uniquify_varscope :
  'a Varscope.t ->
  ( string * [ `Original | `Renamed ] * (string * [ `Original | `Renamed ] * Field.t) Bwd.t,
    'a )
  Bwv.t
  * emp t

val unsafe_add : 'b t -> 'n variables -> ('b, 'n) snoc t
