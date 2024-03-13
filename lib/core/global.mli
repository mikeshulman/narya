open Util
open Tbwd
open Syntax
open Term

type definition = Axiom | Defined of (emp, potential) term

val find_type_opt : Constant.t -> (emp, kinetic) term option
val find_definition_opt : Constant.t -> definition option
val run_empty : (unit -> 'a) -> 'a
val add : Constant.t -> (emp, kinetic) term -> definition -> unit
val remove : Constant.t -> unit
val run_with : Constant.t -> (emp, kinetic) term -> definition -> (unit -> 'a) -> 'a
val run_with_definition : Constant.t -> definition -> (unit -> 'a) -> 'a
