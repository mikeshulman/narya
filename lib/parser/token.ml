type t =
  | Field of string (* Starting with . *)
  | Constr of string (* Ending with . *)
  | LParen (* ( *)
  | RParen (* ) *)
  | LBrace (* { *)
  | RBrace (* } *)
  | Arrow (* Both -> and → *)
  | Mapsto (* Both |-> and ↦ *)
  | Colon (* : *)
  | Coloneq (* Both := and ≔ *)
  | Dot (* . *)
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

(* Only "names" not containing internal periods are valid for local variable names, fields, or constructors, since internal periods are used for namespace qualification. *)
let variableable s = not (String.exists (fun c -> c = '.') s)

let to_string = function
  | Field s -> "." ^ s
  | Constr s -> s ^ "."
  | LParen -> "("
  | RParen -> ")"
  | LBrace -> "{"
  | RBrace -> "}"
  | Arrow -> "->"
  | Mapsto -> "|->"
  | Colon -> ":"
  | Coloneq -> ":="
  | Dot -> "."
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
