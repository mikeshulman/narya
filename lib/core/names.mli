open Util
open Tbwd
open Dim
open Syntax
open Term

type 'n t

val empty : emp t

(* Look up an index variable to find a name for it. *)
val lookup : 'n t -> 'n index -> string list

(* Add a new variable, generating a fresh version of its name if necessary to avoid conflicts. *)
val add_cube : 'b t -> string option -> string option * ('b, 'n) snoc t

val add_normals :
  'b t -> ('n, string option) CubeOf.t -> ('n, string option) CubeOf.t * ('b, 'n) snoc t

val add : 'b t -> 'n variables -> 'n variables * ('b, 'n) snoc t
val pp_variables : Format.formatter -> 'n variables -> unit
val pp_names : Format.formatter -> 'b t -> unit
