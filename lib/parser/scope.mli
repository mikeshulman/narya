open Bwd
open Core
module Trie = Yuujinchou.Trie

module Param : sig
  type data =
    [ `Constant of Constant.t | `Notation of User.prenotation * User.notation ]
    * Asai.Range.t option

  type tag = unit
  type hook = unit
  type context = unit
end

module Mod : sig
  include module type of Yuujinchou.Modifier.Make (Param)

  val union :
    ?prefix:Trie.bwd_path ->
    ?context:Param.context ->
    (Param.data, Param.tag) Trie.t ->
    (Param.data, Param.tag) Trie.t ->
    (Param.data, Param.tag) Trie.t

  val union_subtree :
    ?prefix:Trie.bwd_path ->
    ?context:Param.context ->
    (Param.data, Param.tag) Trie.t ->
    Trie.path * (Param.data, Param.tag) Trie.t ->
    (Param.data, Param.tag) Trie.t

  val union_singleton :
    ?prefix:Trie.bwd_path ->
    ?context:Param.context ->
    (Param.data, Param.tag) Trie.t ->
    Trie.path * (Param.data * Param.tag) ->
    (Param.data, Param.tag) Trie.t

  val union_root :
    ?prefix:Trie.bwd_path ->
    ?context:Param.context ->
    (Param.data, Param.tag) Trie.t ->
    Param.data * Param.tag ->
    (Param.data, Param.tag) Trie.t
end

exception Locked

type trie = (Param.data, Param.tag) Trie.t
type t

val empty : t
val resolve : Trie.path -> (Param.data * Param.tag) option
val modify_visible : ?context_visible:Param.context -> Param.hook Yuujinchou.Language.t -> unit
val modify_export : ?context_export:Param.context -> Param.hook Yuujinchou.Language.t -> unit
val modify_options : (Options.t -> Options.t) -> unit

val export_visible :
  ?context_modifier:Param.context ->
  ?context_export:Param.context ->
  Param.hook Yuujinchou.Language.t ->
  unit

val include_singleton :
  ?context_visible:Param.context ->
  ?context_export:Param.context ->
  Trie.path * (Param.data * Param.tag) ->
  unit

val import_singleton :
  ?context_visible:Param.context -> Trie.path * (Param.data * Param.tag) -> unit

val unsafe_include_subtree :
  ?context_modifier:Param.context ->
  ?context_visible:Param.context ->
  ?context_export:Param.context ->
  ?modifier:Param.hook Yuujinchou.Language.t ->
  Trie.path * (Param.data, Param.tag) Trie.t ->
  unit

val include_subtree :
  ?context_modifier:Param.context ->
  ?context_visible:Param.context ->
  ?context_export:Param.context ->
  ?modifier:Param.hook Yuujinchou.Language.t ->
  Trie.path * (Param.data, Param.tag) Trie.t ->
  unit

val import_subtree :
  ?context_modifier:Param.context ->
  ?context_visible:Param.context ->
  ?modifier:Param.hook Yuujinchou.Language.t ->
  Trie.path * (Param.data, Param.tag) Trie.t ->
  unit

val get_visible : unit -> trie
val get_export : unit -> trie
val get_options : unit -> Options.t
val set_visible : trie -> unit
val start_section : string list -> unit
val end_section : unit -> string list option
val count_sections : unit -> int

val run :
  ?export_prefix:string Bwd.t ->
  ?init_visible:(Param.data, Param.tag) Trie.t ->
  ?options:Options.t ->
  (unit -> 'a) ->
  'a

val run_with : ?get:(unit -> t) -> ?set:(t -> unit) -> (unit -> 'a) -> 'a
val lookup : Trie.path -> Constant.t option
val find_data : ('a * 'c, 'b) Trie.t -> 'a -> Trie.path option
val name_of : Constant.t -> Trie.path
val define : Compunit.t -> ?loc:Asai.Range.t -> Trie.path -> Constant.t
val check_name : Trie.path -> Asai.Range.t option -> unit
