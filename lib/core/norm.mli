open Dim
open Syntax
open Term
open Value

(* These make sense in arbitrary situations: they issue no effects or exceptions. *)

val field : value -> Field.t -> value

val tyof_field_withname :
  ?severity:Asai__.Diagnostic.severity ->
  ?degerr:Reporter.Code.t ->
  value ->
  value ->
  Field.or_index ->
  Field.t * value

val tyof_field :
  ?severity:Asai__.Diagnostic.severity ->
  ?degerr:Reporter.Code.t ->
  value ->
  value ->
  Field.t ->
  value

(* This one calls "eval" internally, but only on the type of field, which is guaranteed to be a term rather than a case tree, so it should not issue any effects or exceptions either. *)

val tyof_app :
  ('k, unit) BindCube.t -> (D.zero, 'k, 'k, normal) TubeOf.t -> ('k, value) CubeOf.t -> value

(* These handle the effects and exceptions, not letting them escape.  (In the term case, they are handled by raising an anomaly.) *)

val eval_tree : ('m, 'b) env -> 'b term -> tree_value
val eval_term : ('m, 'b) env -> 'b term -> value
val apply_term : value -> ('n, value) CubeOf.t -> value
val apply_binder_term : 'n binder -> ('n, value) CubeOf.t -> value
