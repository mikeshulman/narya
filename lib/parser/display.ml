(* This state module tracks user-configurable display states.  These are set by command-line flags or by the "display" command which is out-of-band, i.e. doesn't appear in files and is instead issued by the user interactively or through proof general. *)

type style = [ `Compact | `Noncompact ]
type chars = [ `Unicode | `ASCII ]
type metas = [ `Anonymous | `Numbered ]
type argstyle = [ `Spaces | `Parens ]
type spacing = [ `Wide | `Narrow ]
type values = [ `Unicode | `ASCII | `Compact | `Noncompact ]

let to_string : values -> string = function
  | `Compact -> "compact"
  | `Unicode -> "unicode"
  | `Noncompact -> "noncompact"
  | `ASCII -> "ASCII"

module Config = struct
  type t = { style : style; chars : chars; metas : metas; argstyle : argstyle; spacing : spacing }
end

let default : Config.t =
  { style = `Compact; chars = `Unicode; metas = `Numbered; argstyle = `Spaces; spacing = `Wide }

module State = Util.State.Make (Config)

let () =
  State.register_printer (function
    | `Get -> Some "unhandled Display get effect"
    | `Set _ -> Some "unhandled Display set effect")

(*  *)
let style () = (State.get ()).style
let chars () = (State.get ()).chars
let metas () = (State.get ()).metas
let argstyle () = (State.get ()).argstyle
let spacing () = (State.get ()).spacing

let alt_char uni asc =
  match (State.get ()).chars with
  | `Unicode -> uni
  | `ASCII -> asc

let run = State.run
let modify = State.modify
