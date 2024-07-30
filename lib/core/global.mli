open Bwd
open Util
open Tbwd
open Syntax
open Term

type definition = Axiom of [ `Parametric | `Nonparametric ] | Defined of (emp, potential) term
type metamap

val find : Constant.t -> (emp, kinetic) term * definition
val find_meta : ('b, 's) Meta.t -> ('b, 's) Metadef.wrapped
val to_channel_unit : Out_channel.t -> Compunit.t -> Marshal.extern_flags list -> unit
val from_channel_unit : (Compunit.t -> Compunit.t) -> In_channel.t -> Compunit.t -> unit
val add : Constant.t -> (emp, kinetic) term -> definition -> unit
val set : Constant.t -> definition -> unit
val add_error : Constant.t -> Reporter.Code.t -> unit

val add_meta :
  ('b, 's) Meta.t ->
  termctx:('a, 'b) Termctx.t ->
  ty:('b, kinetic) term ->
  tm:('b, 's) term option ->
  energy:'s energy ->
  unit

val set_meta : ('b, 's) Meta.t -> tm:('b, 's) term option -> unit
val save_metas : metamap -> unit

val add_hole :
  ('b, 's) Meta.t ->
  unit Asai.Range.located ->
  vars:(string option, 'a) Bwv.t ->
  termctx:('a, 'b) Termctx.t ->
  ty:('b, kinetic) term ->
  status:('b, 's) Status.status ->
  unit

val with_definition : Constant.t -> definition -> (unit -> 'a) -> 'a
val with_meta_definition : ('b, 's) Meta.t -> ('b, 's) term option -> (unit -> 'a) -> 'a

type data

val empty : data
val get : unit -> data
val run : init:data -> (unit -> 'a) -> 'a
val try_with : ?get:(unit -> data) -> ?set:(data -> unit) -> (unit -> 'a) -> 'a

type eternity = {
  find_opt : 'b 's. ('b, 's) Meta.t -> ('b, 's) Metadef.wrapped option;
  add :
    'a 'b 's.
    ('b, 's) Meta.t ->
    (string option, 'a) Bwv.t ->
    ('a, 'b) Termctx.t ->
    ('b, kinetic) term ->
    ('b, 's) Status.status ->
    unit;
}

val eternity : eternity ref

module HolePos : module type of State.Make (struct
  type t = (int * int * int) Bwd.t
end)

val end_command : (int -> Reporter.Code.t) -> unit
val run_command_with : init:data -> (int -> Reporter.Code.t) -> (unit -> 'a) -> 'a
