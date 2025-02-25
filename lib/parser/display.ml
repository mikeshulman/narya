type style = [ `Compact | `Noncompact ]
type chars = [ `Unicode | `ASCII ]
type metas = [ `Anonymous | `Numbered ]
type argstyle = [ `Spaces | `Parens ]
type spacing = [ `Wide | `Narrow ]

module Config = struct
  type t = { style : style; chars : chars; metas : metas; argstyle : argstyle; spacing : spacing }
end

let default : Config.t =
  { style = `Compact; chars = `Unicode; metas = `Numbered; argstyle = `Spaces; spacing = `Wide }

module Reader = Algaeff.Reader.Make (Config)

let () = Reader.register_printer (function `Read -> Some "unhandled Display read effect")

(*  *)
let style () = (Reader.read ()).style
let chars () = (Reader.read ()).chars
let metas () = (Reader.read ()).metas
let argstyle () = (Reader.read ()).argstyle
let spacing () = (Reader.read ()).spacing

let alt_char uni asc =
  match (Reader.read ()).chars with
  | `Unicode -> uni
  | `ASCII -> asc

let run = Reader.run
