(* This state module tracks user-configurable display states.  These are set by command-line flags or by the "display" command which is out-of-band, i.e. doesn't appear in files and is instead issued by the user interactively or through proof general. *)

type chars = [ `Unicode | `ASCII ]
type metas = [ `Anonymous | `Numbered ]
type argstyle = [ `Spaces | `Parens ]
type spacing = [ `Wide | `Narrow ]
type show = [ `Show | `Hide ]
type holes = [ `With_number | `Without_number ]
type values = [ `Unicode | `ASCII | `Show | `Hide ]

let to_string : values -> string = function
  | `Unicode -> "unicode"
  | `ASCII -> "ASCII"
  | `Show -> "on"
  | `Hide -> "off"

module Config = struct
  type t = {
    chars : chars;
    metas : metas;
    argstyle : argstyle;
    spacing : spacing;
    holes : holes;
    function_boundaries : show;
    type_boundaries : show;
  }
end

let default : Config.t =
  {
    chars = `Unicode;
    metas = `Numbered;
    argstyle = `Spaces;
    spacing = `Wide;
    holes = `Without_number;
    function_boundaries = `Hide;
    type_boundaries = `Hide;
  }

module State = Util.State.Make (Config)

let () =
  State.register_printer (function
    | `Get -> Some "unhandled Display get effect"
    | `Set _ -> Some "unhandled Display set effect")

(*  *)
let chars () = (State.get ()).chars
let metas () = (State.get ()).metas
let argstyle () = (State.get ()).argstyle
let spacing () = (State.get ()).spacing
let function_boundaries () = (State.get ()).function_boundaries
let type_boundaries () = (State.get ()).type_boundaries
let holes () = (State.get ()).holes

let alt_char uni asc =
  match (State.get ()).chars with
  | `Unicode -> uni
  | `ASCII -> asc

let run = State.run
let modify = State.modify

(* For now, we hardcode this. *)
let columns () = 77
