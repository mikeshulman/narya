(* DN = Danielsson-Norell, "Parsing mixfix operators" *)

open Util
open Core
open Effect.Deep
open Bwd
open Parsing
open ParseOps
open Raw

(* ********************
   Notations
   *********************)

(* These maps store the notations in each node. *)
let nonassoc_notations : Notation.non Node.Map.t ref =
  ref
    (Node.Map.make
    |> Node.Map.add Node.max (new Notation.parens "(" ")")
    |> Node.Map.add Node.max (new Notation.symbol "Type" N.zero UU)
    |> Node.Map.add Node.max (new Notation.symbol "refl" N.one Refl)
    |> Node.Map.add Node.max (new Notation.symbol "sym" N.one Sym)
    |> Node.Map.add Node.max (new Notation.symbol "Id" N.three Id)
    |> Node.Map.add Node.max (new Notation.struc)
    |> Node.Map.add Node.max (new Notation.constr)
    (* |> Node.Map.add Node.max (new Notation.default) *)
    (* |> Node.Map.add Node.max (new Notation.uvar) *)
    |> Node.Map.add Node.min (new Notation.ascription))

let get_nonassocs node = Node.Map.get node !nonassoc_notations

let leftassoc_notations : Notation.left Node.Map.t ref =
  ref
    (Node.Map.make
    |> Node.Map.add Node.premax (new Notation.application)
    |> Node.Map.add Node.premax (new Notation.field))

let get_leftassocs node = Node.Map.get node !leftassoc_notations

let rightassoc_notations : Notation.right Node.Map.t ref =
  ref
    (Node.Map.make
    |> Node.Map.add Node.min (new Notation.lambda)
    |> Node.Map.add Node.min (new Notation.letin)
    |> Node.Map.add Node.arrow (new Notation.arrow)
    |> Node.Map.add Node.arrow (new Notation.pi :> Fixity.right Notation.t))

let get_rightassocs node = Node.Map.get node !rightassoc_notations

(* There's a theoretical problem of ambiguity when combining type ascription with Nuprl-style Pi-types.  Is "(x : A) → B" a function with domain A, or a function with domain x ascribed to A?  However, it seems unlikely that both possibilities would ever simultaneously typecheck, so if we use typechecking to decide on which of ambiguous parses to reject we should be okay. *)

(* ********************
   Memoization
   ******************** *)

(* We maintain a memo table for memoizing the results of the "group" = "\hat{p}" nonterminal, as suggested by DN.  This does seem to improve performance vastly, making church numerals like 8 practical to parse. *)
type memotbl = (Node.t * parse_in, Notation.any Tree.t parse_out) Hashtbl.t

(* We might try to supply that memo table as a reader monad incorporated into Parsing.t.  Unfortunately, the circle of type dependencies makes that difficult or impossible, as memotbl depends on tree, which depends on notation, which depends on Parsing.t.  Moreover, in that case we would have to be extra careful to make sure the memo table persists through backtracking.  Thus, we instead expose the memo table with Effects. *)
type _ Effect.t +=
  | Lookup : Node.t * parse_in -> Notation.any Tree.t parse_out option Effect.t
  | Save : Node.t * parse_in * Notation.any Tree.t parse_out -> unit Effect.t

(* ********************
   Parsing
   ******************** *)

(* Parse an identifier.  *)
let ident : Notation.any Tree.t Parsing.t =
  let* str = consume_ident in
  return (Tree.leaf str)

(* DN nonterminal "expr".  It has to take a unit argument so that OCaml recognizes it as a "function" that can be defined by recursion. *)
let rec expr : unit -> Notation.any Tree.t Parsing.t =
 fun () ->
  (* An expression is either an identifier, *)
  ident
  (* or a notation belonging to an open node. *)
  <|> let* node = choose_from (Node.get_all ()) in
      group node

(* DN nonterminal "p↑".  This is similar to "expr", but instead of looking at all open nodes, we look at those with higher precedence than the current one. *)
and higher (node : Node.t) : Notation.any Tree.t Parsing.t =
  ident
  <|> let* hnode = choose_from (Node.get_highers node) in
      group hnode

(* DN nonterminal "p̂".  This function is just a wrapper around compute_group that handles the memoization. *)
and group (node : Node.t) : Notation.any Tree.t Parsing.t =
 fun toks ->
  match Effect.perform (Lookup (node, toks)) with
  | Some res -> res
  | None ->
      let res = compute_group node toks in
      Effect.perform (Save (node, toks, res));
      res

(* Here we do the work of "p̂".  We choose an associativity, and a notation with that associativity in the given node, and attempt to parse it. *)
and compute_group (node : Node.t) : Notation.any Tree.t Parsing.t =
  group_non node
  <|> group_right node
  <|>
  (* p↑, the first argument *)
  let* first = higher node in
  (* (p⃖)⁺, the rest *)
  group_left node first

(* DN nonterminal "p̂" for nonassociative operators.  This is straightforward: we choose a notation and parse all its pieces at higher node.  The coercions to Fixity.non, and others like them below, are workarounds for https://github.com/ocaml/ocaml/issues/10664.  This bug has been fixed in https://github.com/ocaml/ocaml/pull/11600 which will appear in Ocaml 5.1. *)
and group_non (node : Node.t) : Notation.any Tree.t Parsing.t =
  let* notn = choose_from (get_nonassocs node) in
  (* If the notation is postfix or infix, we start by parsing its first argument, which must be in higher node since it is nonassociative. *)
  let* args =
    match (notn#fixity :> Fixity.non) with
    | `Postfix | `Infix ->
        let* first = higher node in
        return (Snoc (Emp, first))
    | _ -> return Emp in
  (* Then we pass off to the "op" nonterminal to parse the notation parts and inner arguments. *)
  let* notn, args = op notn args in
  (* If the notation is prefix or infix, we end by parsing its last argument. *)
  let* args =
    match (notn#fixity :> Fixity.non) with
    | `Prefix | `Infix ->
        let* last = higher node in
        return (Snoc (args, last))
    | _ -> return args in
  (* Finally we assemble all the arguments in order. *)
  return (Tree.node (Notation.Any notn) args)

(* DN "p̂" for right-associative operators, which is the combination "(p⃗)⁺ p̂". *)
and group_right (node : Node.t) : Notation.any Tree.t Parsing.t =
  (* We choose a right-associative operator in the node, and parse all of it except its last argument. *)
  let* notn = choose_from (get_rightassocs node) in
  let* notn, args =
    match (notn#fixity :> Fixity.right) with
    (* Fabulously, our hackery with polymorphic variants makes this match exhaustive, while still allowing us to call the polymorphic function "op" on "notn". *)
    | `Prefix ->
        (* In the prefix case, we start right away parsing name parts. *)
        op notn Emp
    | `Infix ->
        (* In the infix case, we have to parse an expression in higher node before we get to the name parts in "op". *)
        let* pre = higher node in
        op notn (Snoc (Emp, pre)) in
  (* Then we either recurse, parsing another right-associative operator and so on, or stop by parsing a single expression in higher node. *)
  let* rest = group_right node <|> higher node in
  (* Returning through the recursive calls, we assemble the trees, essentially performing a right fold (as DN remarks is necessary). *)
  return (Tree.node (Notation.Any notn) (Snoc (args, rest)))

(* DN "(p⃖)⁺" for left-associative operators.  Here, on the first call, "p↑" has already been parsed. *)
and group_left (node : Node.t) (first : Notation.any Tree.t) : Notation.any Tree.t Parsing.t =
  let* notn = choose_from (get_leftassocs node) in
  let* notn, args = op notn (Snoc (Emp, first)) in
  let* args =
    match (notn#fixity :> Fixity.left) with
    | `Postfix -> return args
    | `Infix ->
        (* In the infix case, we have to parse one last expression in higher node *)
        let* post = higher node in
        return (Snoc (args, post)) in
  (* Now we have all the information needed to assemble the parse tree for this piece. *)
  let res = Tree.node (Notation.Any notn) args in
  (* We then either stop, or continue parsing left-associative operators with this result taking the place of their initial "p↑". *)
  return res <|> group_left node res

(* DN nonterminal "op".  Returns a fully-parsed notation object along with its list of *inner* arguments. *)
and op :
      'fixity.
      ([< `Infix | `Outfix | `Prefix | `Postfix ] as 'fixity) Notation.t ->
      Notation.any Tree.t Bwd.t ->
      ('fixity Notation.t * Notation.any Tree.t Bwd.t) Parsing.t =
 fun notn args ->
  (* First we consume a name part. *)
  let* notn = notn#consume in
  (* If we're done, we return (no more *inner* arguments) *)
  if notn#finished then return (notn, args)
  else
    (* Otherwise, we parse an inner argument, record it, and recurse. *)
    let* this = expr () in
    op notn (Snoc (args, this))

(* ********************
   Entry points
   ******************** *)

(* Parse a string into a raw term, in a context of variables with or without names.  Must parse the *whole* string, with nothing left over. *)
let term : type n. (string option, n) Bwv.t -> string -> n check list =
 fun ctx str ->
  (* This is the entry point, so we create a new memo table. *)
  let memo = Hashtbl.create 100 in
  try_with
    (fun toks ->
      let open ChoiceOps in
      let* tr = execute (expr ()) toks in
      Notation.compile ctx tr)
    (Token.ize str)
    {
      effc =
        (fun (type a) (eff : a Effect.t) ->
          match eff with
          | Lookup (node, toks) ->
              Some
                (fun (k : (a, _) continuation) -> continue k (Hashtbl.find_opt memo (node, toks)))
          | Save (node, toks, res) ->
              Some
                (fun (k : (a, _) continuation) ->
                  Hashtbl.add memo (node, toks) res;
                  continue k ())
          | _ -> None);
    }
