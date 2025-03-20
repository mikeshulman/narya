open Dim
open Reporter
open Value

type ('a, 'b) actor = { act : 'm 'n. 'a -> ('m, 'n) deg -> 'b }

val act_cube : ('a, 'b) actor -> ('n, 'a) CubeOf.t -> ('m, 'n) deg -> ('m, 'b) CubeOf.t
val forward_view_term : (kinetic value -> kinetic value) ref
val act_value : 's value -> ('m, 'n) deg -> 's value
val act_normal : normal -> ('a, 'b) deg -> normal
val gact_ty : ?err:Code.t -> kinetic value option -> kinetic value -> ('a, 'b) deg -> kinetic value
val act_ty : ?err:Code.t -> kinetic value -> kinetic value -> ('a, 'b) deg -> kinetic value
val act_evaluation : 's evaluation -> ('m, 'n) deg -> 's evaluation

val act_value_cube :
  ('a -> 's value) -> ('n, 'a) CubeOf.t -> ('m, 'n) deg -> ('m, 's value) CubeOf.t

val act_lazy_eval : 's lazy_eval -> ('m, 'n) deg -> 's lazy_eval
val field_lazy : 's lazy_eval -> 'i Field.t -> ('n, 't, 'i) insertion -> 's lazy_eval
