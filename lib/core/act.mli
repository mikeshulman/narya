open Dim
open Reporter
open Syntax
open Value

val act_value : 's value -> ('m, 'n) deg -> 's value
val act_canonical : canonical -> ('m, 'n) deg -> canonical
val act_normal : normal -> ('a, 'b) deg -> normal
val gact_ty : ?err:Code.t -> kinetic value option -> kinetic value -> ('a, 'b) deg -> kinetic value
val act_ty : ?err:Code.t -> kinetic value -> kinetic value -> ('a, 'b) deg -> kinetic value

val act_value_cube :
  ('a -> 's value) -> ('n, 'a) CubeOf.t -> ('m, 'n) deg -> ('m, 's value) CubeOf.t

val lookup : ('n, 'b) env -> 'b Term.index -> kinetic value
