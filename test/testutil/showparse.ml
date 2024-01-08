open Parser
open Parse

(* Translate a parse observation into something that shows the names of notations rather than their internal abstract representations, for easier inspection and testing.  Note that since we intercept the parse tree before the "compilation" step, there is no name resolution, so this doesn't need to be run inside a Yuujinchou handler and can use unbound variables. *)

type obs = Term of parse_tree

and parse_tree =
  | Notn of string * obs list
  | App of parse_tree * parse_tree
  | Placeholder
  | Ident of string list
  | Constr of string
  | Field of string
  | Numeral of Q.t

let rec get_obs (obs : Notation.observation) : obs =
  match obs with
  | Term r -> Term (get_tree r.value)

and get_tree : type lt ls rt rs. (lt, ls, rt, rs) Notation.parse -> parse_tree =
 fun r ->
  match r with
  | Notn n -> Notn (Notation.name (Notation.notn n), List.map get_obs (Notation.args n))
  | App a -> App (get_tree a.fn.value, get_tree a.arg.value)
  | Placeholder -> Placeholder
  | Ident x -> Ident x
  | Constr x -> Constr x
  | Field x -> Field x
  | Numeral n -> Numeral n

let parse tm =
  let p, _ =
    Parse_term.parse (`New (`Full, `String { content = tm; title = Some "user-supplied term" }))
  in
  let (Term tm) = Parse_term.final p in
  get_tree tm.value
