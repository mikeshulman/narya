open Uuseg_string
open Printconfig

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
  | Underscore (* _ *)
  | Internal of string (* Starting or ending with _ *)
  | Axiom (* axiom *)
  | Def (* def *)
  | Echo (* echo *)
  | Record (* record *)
  | Data (* data *)
  | Codata (* codata *)
  | Section (* section *)
  | Let (* let *)
  | In (* in *)
  | Op of string (* Sequence of common ASCII symbols, other than : := ::= += -> |-> |=> etc. *)
  (* Alphanumeric/unicode other than common ASCII symbols and above single-token characters, with dots and underscores occuring only internally, and each dot-separated piece being nonempty.  Those not containing any dots could be local variable names (with one dot, they could be a face of a cube variable), and those consisting entirely of digits could be numerals.  We can't separate these out at lexing time into those that are parts of mixfix notations and those that are potential identifiers, since the mixfix notations in scope change as we go through a file. *)
  | Ident of string list
  | Eof

let compare : t -> t -> int = compare

(* Whether a string is valid as a dot-separated piece of an identifier name, or equivalently as a local variable name.  We don't test for absence of the delimited symbols, since they will automatically be lexed separately; this is for testing validity after the lexer has split things into potential tokens.  We also don't test for absence of dots, since identifiers will be split on dots automatically. *)
let ok_ident s =
  let len = String.length s in
  len > 0 && s.[0] <> '_' && s.[len - 1] <> '_'

let to_string = function
  | Field s -> "." ^ s
  | Constr s -> s ^ "."
  | LParen -> "("
  | RParen -> ")"
  | LBracket -> "["
  | RBracket -> "]"
  | LBrace -> "{"
  | RBrace -> "}"
  | Arrow -> alt_char "→" "->"
  | Mapsto -> alt_char "↦" "|->"
  | DblMapsto -> alt_char "⤇" "|=>"
  | Colon -> ":"
  | Coloneq -> alt_char "≔" ":="
  | DblColoneq -> alt_char "⩴" "::="
  | Pluseq -> alt_char "⩲" "+="
  | Dot -> "."
  | Ellipsis -> alt_char "…" "..."
  | String s -> "\"" ^ s ^ "\""
  | Underscore -> "_"
  | Internal s -> s
  | Axiom -> "axiom"
  | Def -> "def"
  | Echo -> "echo"
  | Record -> "record"
  | Data -> "data"
  | Codata -> "codata"
  | Section -> "section"
  | Let -> "let"
  | In -> "in"
  | Op s -> s
  | Ident s -> String.concat "." s
  | Eof -> "EOF"

(* Given a token, create a constant pretty-printer that prints that token. *)
let pp tok ppf () = pp_utf_8 ppf (to_string tok)
