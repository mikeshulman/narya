type t =
  | Field of string (* Starting with . *)
  | Constr of string (* Ending with . *)
  | LParen (* ( *)
  | RParen (* ) *)
  | LBracket (* [ *)
  | RBracket (* ] *)
  | LBrace (* { *)
  | RBrace (* } *)
  | Arrow (* Both -> and → *)
  | Mapsto (* Both |-> and ↦ *)
  | DblMapsto (* Both |=> and ⤇ *)
  | Colon (* : *)
  | Coloneq (* Both := and ≔ *)
  | DblColoneq (* Both ::= and ⩴ *)
  | Pluseq (* Both += and ⩲ *)
  | Dot (* . *)
  | Ellipsis (* ... and … *)
  | String of string (* Double-quoted *)
  | Numeral of int
  | Underscore (* _ *)
  | Internal of string (* Starting or ending with _ *)
  | Def
  | Record
  | Data
  | Codata
  | Section
  | Let
  | In
  | Op of string (* Sequence of common ASCII symbols *)
  (* Alphanumeric/unicode with only internal dots and underscores only.  We can't separate these out into those that are parts of mixfix notations and those that are potential identifiers, since the mixfix notations in scope change as we go through a file. *)
  | Name of string
  | Eof

let compare : t -> t -> int = compare

(* Only "names" not containing internal periods are valid for local variable names, since internal periods are used for namespace qualification. *)
let variableable s = not (String.exists (fun c -> c = '.') s)

let to_string = function
  | Field s -> "." ^ s
  | Constr s -> s ^ "."
  | LParen -> "("
  | RParen -> ")"
  | LBracket -> "["
  | RBracket -> "]"
  | LBrace -> "{"
  | RBrace -> "}"
  | Arrow -> "→"
  | Mapsto -> "↦"
  | DblMapsto -> "⤇"
  | Colon -> ":"
  | Coloneq -> "≔"
  | DblColoneq -> "⩴"
  | Pluseq -> "⩲"
  | Dot -> "."
  | Ellipsis -> "..."
  | String s -> "\"" ^ s ^ "\""
  | Numeral s -> Int.to_string s
  | Underscore -> "_"
  | Internal s -> s
  | Def -> "def"
  | Record -> "record"
  | Data -> "data"
  | Codata -> "codata"
  | Section -> "section"
  | Let -> "let"
  | In -> "in"
  | Op s -> s
  | Name s -> s
  | Eof -> "EOF"

(* Given a token, create a constant pretty-printer that prints that token. *)
let pp tok ppf () = Uuseg_string.pp_utf_8 ppf (to_string tok)
