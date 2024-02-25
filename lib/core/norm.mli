open Dim
open Syntax
open Term
open Value

val field : kinetic value -> Field.t -> kinetic value

val tyof_field_withname :
  ?severity:Asai__.Diagnostic.severity ->
  ?degerr:Reporter.Code.t ->
  kinetic value ->
  kinetic value ->
  Field.or_index ->
  Field.t * kinetic value

val tyof_field :
  ?severity:Asai__.Diagnostic.severity ->
  ?degerr:Reporter.Code.t ->
  kinetic value ->
  kinetic value ->
  Field.t ->
  kinetic value

val tyof_app :
  ('k, unit) BindCube.t ->
  (D.zero, 'k, 'k, normal) TubeOf.t ->
  ('k, kinetic value) CubeOf.t ->
  kinetic value

val eval : ('m, 'b) env -> ('b, 's) term -> 's evaluation
val eval_term : ('m, 'b) env -> ('b, kinetic) term -> kinetic value
val apply_term : kinetic value -> ('n, kinetic value) CubeOf.t -> kinetic value
val apply_binder_term : ('n, kinetic) binder -> ('n, kinetic value) CubeOf.t -> kinetic value
