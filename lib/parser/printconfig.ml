type style = [ `Compact | `Noncompact ]
type state = [ `Term | `Case ]
type chars = [ `Unicode | `ASCII ]

module Config = struct
  type t = { style : style; state : state; chars : chars }
end

module Reader = Algaeff.Reader.Make (Config)

let style () = (Reader.read ()).style
let state () = (Reader.read ()).state
let as_term f = Reader.scope (fun c -> { c with state = `Term }) f
let as_case f = Reader.scope (fun c -> { c with state = `Case }) f
let chars () = (Reader.read ()).chars

let alt_char uni asc =
  match (Reader.read ()).chars with
  | `Unicode -> uni
  | `ASCII -> asc

let run = Reader.run
