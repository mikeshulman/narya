type style = [ `Compact | `Noncompact ]
type state = [ `Term | `Case ]
type chars = [ `Unicode | `ASCII ]
type metas = [ `Anonymous | `Numbered ]
type argstyle = [ `Spaces | `Parens ]
type spacing = [ `Wide | `Narrow ]

module Config = struct
  type t = {
    style : style;
    state : state;
    chars : chars;
    metas : metas;
    argstyle : argstyle;
    spacing : spacing;
  }
end

let default : Config.t =
  {
    style = `Compact;
    state = `Term;
    chars = `Unicode;
    metas = `Numbered;
    argstyle = `Spaces;
    spacing = `Wide;
  }

module Reader = Algaeff.Reader.Make (Config)

let () = Reader.register_printer (function `Read -> Some "unhandled Printconfig read effect")

(*  *)
let style () = (Reader.read ()).style
let state () = (Reader.read ()).state
let as_term f = Reader.scope (fun c -> { c with state = `Term }) f
let as_case f = Reader.scope (fun c -> { c with state = `Case }) f
let chars () = (Reader.read ()).chars
let metas () = (Reader.read ()).metas
let argstyle () = (Reader.read ()).argstyle
let spacing () = (Reader.read ()).spacing

let alt_char uni asc =
  match (Reader.read ()).chars with
  | `Unicode -> uni
  | `ASCII -> asc

let run = Reader.run
