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

(* These maps store the notations in each scope. *)
let nonassoc_notations : Notation.non Scope.Map.t ref =
  ref
    (Scope.Map.make
    |> Scope.Map.add Scope.max (new Notation.parens "(" ")")
    |> Scope.Map.add Scope.max (new Notation.symbol "Type" N.zero UU)
    |> Scope.Map.add Scope.max (new Notation.symbol "refl" N.one Refl)
    |> Scope.Map.add Scope.max (new Notation.symbol "sym" N.one Sym)
    |> Scope.Map.add Scope.max (new Notation.symbol "Id" N.three Id)
    |> Scope.Map.add Scope.max (new Notation.struc)
    (* |> Scope.Map.add Scope.max (new Notation.default) *)
    (* |> Scope.Map.add Scope.max (new Notation.uvar) *)
    |> Scope.Map.add Scope.min (new Notation.ascription))

let get_nonassocs scope = Scope.Map.get scope !nonassoc_notations

let leftassoc_notations : Notation.left Scope.Map.t ref =
  ref
    (Scope.Map.make
    |> Scope.Map.add Scope.premax (new Notation.application)
    |> Scope.Map.add Scope.premax (new Notation.field))

let get_leftassocs scope = Scope.Map.get scope !leftassoc_notations

let rightassoc_notations : Notation.right Scope.Map.t ref =
  ref
    (Scope.Map.make
    |> Scope.Map.add Scope.min (new Notation.lambda)
    |> Scope.Map.add Scope.arrow (new Notation.arrow)
    |> Scope.Map.add Scope.arrow (new Notation.pi :> Fixity.right Notation.t))

let get_rightassocs scope = Scope.Map.get scope !rightassoc_notations

(* There's a theoretical problem of ambiguity when combining type ascription with Nuprl-style Pi-types.  Is "(x : A) → B" a function with domain A, or a function with domain x ascribed to A?  However, it seems unlikely that both possibilities would ever simultaneously typecheck, so if we use typechecking to decide on which of ambiguous parses to reject we should be okay. *)

(* ********************
   Memoization
   ******************** *)

(* We maintain a memo table for memoizing the results of the "group" = "\hat{p}" nonterminal, as suggested by DN.  This does seem to improve performance vastly, making church numerals like 8 practical to parse. *)
type memotbl = (Scope.t * parse_in, Notation.any Tree.t parse_out) Hashtbl.t

(* We might try to supply that memo table as a reader monad incorporated into Parsing.t.  Unfortunately, the circle of type dependencies makes that difficult or impossible, as memotbl depends on tree, which depends on notation, which depends on Parsing.t.  Moreover, in that case we would have to be extra careful to make sure the memo table persists through backtracking.  Thus, we instead expose the memo table with Effects. *)
type _ Effect.t +=
  | Lookup : Scope.t * parse_in -> Notation.any Tree.t parse_out option Effect.t
  | Save : Scope.t * parse_in * Notation.any Tree.t parse_out -> unit Effect.t

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
  (* or a notation belonging to an open scope. *)
  <|> let* scope = choose_from (Scope.get_opens ()) in
      group scope

(* DN nonterminal "p↑".  This is similar to "expr", but instead of looking at all open scopes, we look at those with higher precedence than the current one. *)
and higher (scope : Scope.t) : Notation.any Tree.t Parsing.t =
  ident
  <|> let* hscope = choose_from (Scope.get_highers scope) in
      group hscope

(* DN nonterminal "p̂".  This function is just a wrapper around compute_group that handles the memoization. *)
and group (scope : Scope.t) : Notation.any Tree.t Parsing.t =
 fun toks ->
  match Effect.perform (Lookup (scope, toks)) with
  | Some res -> res
  | None ->
      let res = compute_group scope toks in
      Effect.perform (Save (scope, toks, res));
      res

(* Here we do the work of "p̂".  We choose an associativity, and a notation with that associativity in the given scope, and attempt to parse it. *)
and compute_group (scope : Scope.t) : Notation.any Tree.t Parsing.t =
  group_non scope
  <|> group_right scope
  <|>
  (* p↑, the first argument *)
  let* first = higher scope in
  (* (p⃖)⁺, the rest *)
  group_left scope first

(* DN nonterminal "p̂" for nonassociative operators.  This is straightforward: we choose a notation and parse all its pieces at higher scope.  The coercions to Fixity.non, and others like them below, are workarounds for https://github.com/ocaml/ocaml/issues/10664.  This bug has been fixed in https://github.com/ocaml/ocaml/pull/11600 which will appear in Ocaml 5.1. *)
and group_non (scope : Scope.t) : Notation.any Tree.t Parsing.t =
  let* notn = choose_from (get_nonassocs scope) in
  (* If the notation is postfix or infix, we start by parsing its first argument, which must be in higher scope since it is nonassociative. *)
  let* args =
    match (notn#fixity :> Fixity.non) with
    | `Postfix | `Infix ->
        let* first = higher scope in
        return (Snoc (Emp, first))
    | _ -> return Emp in
  (* Then we pass off to the "op" nonterminal to parse the notation parts and inner arguments. *)
  let* notn, args = op notn args in
  (* If the notation is prefix or infix, we end by parsing its last argument. *)
  let* args =
    match (notn#fixity :> Fixity.non) with
    | `Prefix | `Infix ->
        let* last = higher scope in
        return (Snoc (args, last))
    | _ -> return args in
  (* Finally we assemble all the arguments in order. *)
  return (Tree.node (Notation.Any notn) args)

(* DN "p̂" for right-associative operators, which is the combination "(p⃗)⁺ p̂". *)
and group_right (scope : Scope.t) : Notation.any Tree.t Parsing.t =
  (* We choose a right-associative operator in the scope, and parse all of it except its last argument. *)
  let* notn = choose_from (get_rightassocs scope) in
  let* notn, args =
    match (notn#fixity :> Fixity.right) with
    (* Fabulously, our hackery with polymorphic variants makes this match exhaustive, while still allowing us to call the polymorphic function "op" on "notn". *)
    | `Prefix ->
        (* In the prefix case, we start right away parsing name parts. *)
        op notn Emp
    | `Infix ->
        (* In the infix case, we have to parse an expression in higher scope before we get to the name parts in "op". *)
        let* pre = higher scope in
        op notn (Snoc (Emp, pre)) in
  (* Then we either recurse, parsing another right-associative operator and so on, or stop by parsing a single expression in higher scope. *)
  let* rest = group_right scope <|> higher scope in
  (* Returning through the recursive calls, we assemble the trees, essentially performing a right fold (as DN remarks is necessary). *)
  return (Tree.node (Notation.Any notn) (Snoc (args, rest)))

(* DN "(p⃖)⁺" for left-associative operators.  Here, on the first call, "p↑" has already been parsed. *)
and group_left (scope : Scope.t) (first : Notation.any Tree.t) : Notation.any Tree.t Parsing.t =
  let* notn = choose_from (get_leftassocs scope) in
  let* notn, args = op notn (Snoc (Emp, first)) in
  let* args =
    match (notn#fixity :> Fixity.left) with
    | `Postfix -> return args
    | `Infix ->
        (* In the infix case, we have to parse one last expression in higher scope *)
        let* post = higher scope in
        return (Snoc (args, post)) in
  (* Now we have all the information needed to assemble the parse tree for this piece. *)
  let res = Tree.node (Notation.Any notn) args in
  (* We then either stop, or continue parsing left-associative operators with this result taking the place of their initial "p↑". *)
  return res <|> group_left scope res

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
          | Lookup (scope, toks) ->
              Some
                (fun (k : (a, _) continuation) -> continue k (Hashtbl.find_opt memo (scope, toks)))
          | Save (scope, toks, res) ->
              Some
                (fun (k : (a, _) continuation) ->
                  Hashtbl.add memo (scope, toks) res;
                  continue k ())
          | _ -> None);
    }
