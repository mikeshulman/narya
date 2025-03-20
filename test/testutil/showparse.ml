open Parser

(* Translate a parse observation into something that shows the names of notations rather than their internal abstract representations, for easier inspection and testing.  Note that since we intercept the parse tree before the "compilation" step, there is no name resolution, so this doesn't need to be run inside a Yuujinchou handler and can use unbound variables. *)

type obs = Term of parse_tree

and parse_tree =
  | Notn of string * obs list
  | App of parse_tree * parse_tree
  | Placeholder
  | Ident of string list
  | Constr of string
  | Field of string * string list
  | Superscript of parse_tree option * string
  | Hole

let rec get_obs (obs : Notation.observation) : obs option =
  match obs with
  | Term r -> Some (Term (get_tree r.value))
  | Token _ -> None

and get_tree : type lt ls rt rs. (lt, ls, rt, rs) Notation.parse -> parse_tree =
 fun r ->
  match r with
  | Notn (n, a) -> Notn (Notation.name n, List.filter_map get_obs (Notation.args a))
  | App a -> App (get_tree a.fn.value, get_tree a.arg.value)
  | Placeholder _ -> Placeholder
  | Ident (x, _) -> Ident x
  | Constr (x, _) -> Constr x
  | Field (x, b, _) -> Field (x, b)
  | Superscript (None, s, _) -> Superscript (None, s)
  | Superscript (Some x, s, _) -> Superscript (Some (get_tree x.value), s)
  | Hole _ -> Hole

let parse tm =
  let p = Parse.Term.parse (`String { content = tm; title = Some "user-supplied term" }) in
  let (Wrap tm) = Parse.Term.final p in
  get_tree tm.value
