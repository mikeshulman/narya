open Dim
open Term
open Hctx

type 'n t

val empty : emp t

(* Look up an index variable to find a name for it. *)
val lookup : 'n t -> 'n index -> [ `Normal of string | `Cube of string * string ]

(* Add a new variable, generating a fresh version of its name if necessary to avoid conflicts. *)
val add_cube : 'b t -> string option -> string option * ('b, 'n) ext t

val add_normals :
  'b t -> ('n, string option) CubeOf.t -> ('n, string option) CubeOf.t * ('b, 'n) ext t

val add : 'b t -> 'n variables -> 'n variables * ('b, 'n) ext t
val pp_variables : Format.formatter -> 'n variables -> unit
val pp_names : Format.formatter -> 'b t -> unit
