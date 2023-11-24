open Util
open Core
open Raw
open Reporter
module TokMap = Map.Make (Token)

(* A notation is either open or closed, on both sides.  We call these two properties combined its "fixity", since they are equivalent to the traditional classification as infix, prefix, postfix, or "outfix".

    left | right | traditional name
   ------|-------|------------------
    open | open  | infix
   closed| open  | prefix
    open |closed | postfix
   closed|closed | closed / outfix / around-fix

   A notation is left-associative, right-associative, or non-associative.  It can only be associative on a side where it is open, i.e. only an infix or prefix notation can meaningfully be right-associative, while only an infix or postfix notation can meaningfully be left-associative.  Thus, instead of storing associativity separately, we store a "strictness" along with openness. *)

type closed = Dummy_closed
type 's opn = Dummy_open
type _ openness = Open : 's No.strictness -> 's opn openness | Closed : closed openness

(* These opennesses are determined by a more traditional fixity. *)
type (_, _, _) fixity =
  | Infix : 'tight No.t -> (No.strict opn, 'tight, No.strict opn) fixity
  | Infixl : 'tight No.t -> (No.nonstrict opn, 'tight, No.strict opn) fixity
  | Infixr : 'tight No.t -> (No.strict opn, 'tight, No.nonstrict opn) fixity
  | Prefix : 'tight No.t -> (closed, 'tight, No.strict opn) fixity
  | Prefixr : 'tight No.t -> (closed, 'tight, No.nonstrict opn) fixity
  | Postfix : 'tight No.t -> (No.strict opn, 'tight, closed) fixity
  | Postfixl : 'tight No.t -> (No.nonstrict opn, 'tight, closed) fixity
  | Outfix : (closed, No.plus_omega, closed) fixity

(* This is where we enforce that an infix notation can't be associative on both sides. *)
let fixprops :
    type left tight right.
    (left, tight, right) fixity -> left openness * tight No.t * right openness = function
  | Infix t -> (Open Strict, t, Open Strict)
  | Infixl t -> (Open Nonstrict, t, Open Strict)
  | Infixr t -> (Open Strict, t, Open Nonstrict)
  | Prefix t -> (Closed, t, Open Strict)
  | Prefixr t -> (Closed, t, Open Nonstrict)
  | Postfix t -> (Open Strict, t, Closed)
  | Postfixl t -> (Open Nonstrict, t, Closed)
  | Outfix -> (Closed, No.plus_omega, Closed)

(* While parsing a notation, we may need to record certain information other than the identifiers, constructors, fields, and subterms encountered.  We store this in "flags". *)
type flag = ..

(* A "notation tree" (not to be confused with a "parse tree", which is the *result* of parsing) carries the information about how to parse one or more notations.  Each individual notation is defined by giving one tree, but multiple such trees can also be "merged" together.  This allows different notations that start out looking the same to be parsed with minimal backtracking, as we don't need to "decide" which notation we're parsing until we get to the point of the tree where they diverge.  Accordingly, although each notation is associated to a defining tree, a tree also stores pointers to notations at its leaves, since a merged tree could parse many different notations depending on which path through it is taken. *)

(* The trees corresponding to notations that are open on one side or the other do *not* record the existence of the leftmost or rightmost subterm: they only store the operators, constructors, fields, identifiers, and fully delimited "inner" subterms.  Thus, a notation tree does not fully characterize the behavior of a notation until paired with the information of its openness on each side. *)
type tree =
  | Inner : branch -> tree
  | Done : ('left, 'tight, 'right) notation -> tree
  | Flag : flag * tree -> tree
  (* Trees associated to notations of arbitrary length are infinite, so we allow them to be computed lazily as needed. *)
  | Lazy : tree Lazy.t -> tree

(* When there is a choice in parsing, we arrange it so that there is as little backtracking required as possible: we test all the possible next literal tokens, the possibility of a field or constructor, variable, other term, or being done with this node.  With this arrangement, the only necessary backtracking is that an identifier or constructor could also be a term.  So if both of those options are present, we have to backtrack after trying to parse a constructor or identifier and failing. *)
and branch = {
  ops : tree TokMap.t;
  constr : tree option;
  field : tree option;
  ident : tree option;
  term : tree TokMap.t option;
}

(* The entry point of a notation tree must begin with an operator symbol. *)
and entry = tree TokMap.t

(* If we weren't using intrinsically well-scoped De Bruijn indices, then the typechecking context and the type of raw terms would be simply ordinary types, and we could use the one as the parsing State and the other as the parsing Result.  However, the Fmlib parser isn't set up to allow a parametrized family of state types, with the output of a parsing combinator depending on the state (and it would be tricky to do that correctly anyway).  So instead we record the result of parsing as a syntax tree with idents, and have a separate step of "compilation" that makes it into a raw term.  This has the additional advantage that by parsing and pretty-printing we can reformat code even if it is not well-scoped. *)
and observation =
  | Flagged of flag
  | Constr of string
  | Field of string
  | Ident of string option
  | Term of parse

(* A "parse tree" is not to be confused with our "notation trees".  Note that these parse trees don't know anything about the *meanings* of notations either; those are stored by the "compilation" functions.  *)
and parse =
  | Notn : ('left, 'tight, 'right) notation * observation list -> parse
  | App of parse * parse
  | Ident of string
  | Constr of string
  | Field of string
  | Numeral of Q.t
  (* A parsed abstraction already knows whether it is a normal abstraction or a cubical one, since different symbols ↦ and ⤇ are used. *)
  | Abs of [ `Cube | `Normal ] * string option list * parse

(* A compilation function has to be polymorphic over the length of the context so as to produce intrinsically well-scoped terms.  Thus, we have to wrap it as a field of a record (or object). *)
and compiler = { compile : 'n. (string option, 'n) Bwv.t -> observation list -> 'n check }

(* A notation has a precedence, which we call "tightness" to make it obvious that higher numbers bind more tightly, and is a floating-point number.  Using a DAG for precedence, as in Danielsson-Norell, is a nice idea, but it seems to require a lot of backtracking: if when parsing the right-hand argument of a notation ∧ you encounter a notation * that isn't tighter than ∧, you can't know yet that it is forbidden; you have to keep parsing in case you encounter another notation like = that is tighter than ∧ and looser than *, or in fact multiple such notations forming some arbitrarily complicated path through the DAG.  This is incompatible with the minimal-backtracking approach we take, so we stick to numerical tightnesses.

   Our approach is based on the parsing technique of Pratt.  This means that a notation that's closed on both sides doesn't need a tightness at all (it behaves like the highest possible tightness on a closed side), so we give those a tightness of NaN.  User-defined notations that are open on at least one side have finite tightness, while +∞ and −∞ tightness are reserved for internal built-in notations (let-in, abstraction, and ascription are −∞, while +∞ is currently unused.  (Danielsson-Norell say that parentheses are tighter than everything, but in our setup they don't need a tightness at all since they are closed on both sides.) *)
and ('left, 'tight, 'right) notation = {
  name : string;
  id : int; (* Autonumber primary key *)
  dummy : unit -> unit; (* Block polymorphic comparison *)
  tightness : 'tight No.t;
  left : 'left openness;
  right : 'right openness;
  (* The remaining fields are mutable because they have to be able to refer to the notation object itself, so we have a circular data structure.  They aren't expected to mutate further after being set once.  Thus we store them as options, to record whether they have been set. *)
  mutable tree : entry option;
  mutable compiler : compiler option;
  (* Some notations only make sense in terms, others only make sense in case trees, and some make sense in either.  Thus, a notation can supply either or both of these printing functions. *)
  mutable print : (Format.formatter -> observation list -> unit) option;
  mutable print_as_case : (Format.formatter -> observation list -> unit) option;
}

(* The primary key is used to compare notations. *)
let counter = ref 0

let equal : type l1 t1 r1 l2 t2 r2. (l1, t1, r1) notation -> (l2, t2, r2) notation -> bool =
 fun x y -> x.id = y.id

(* A "comparable" module that we can pass to functors like Map.Make. *)
module Notation = struct
  type t = Wrap : ('l, 't, 'r) notation -> t

  let compare : t -> t -> int = fun (Wrap x) (Wrap y) -> compare x.id y.id
end

(* The definition of Notation.t is abstract outside this file, so that we can guarantee they are only created with "make" below and the primary key increments every time.  Thus, we have to provide getter functions for all the fields that should be visible outside this file. *)
let name n = n.name
let tightness n = n.tightness
let left n = n.left
let right n = n.right

(* For the mutable fields, we also have to provide setter functions.  Since these fields are only intended to be set once, the setters throw an exception if the value is already set (and the getters for tree and compiler throw an exception if it is not yet set).  *)

let tree n = Option.get n.tree

let set_tree n t =
  match n.tree with
  | Some _ -> raise (Invalid_argument "notation tree already set")
  | None -> n.tree <- Some t

let compiler n = Option.get n.compiler

let set_compiler n c =
  match n.compiler with
  | Some _ -> raise (Invalid_argument "notation compiler already set")
  | None -> n.compiler <- Some c

let print n = n.print
let set_print n p = n.print <- Some p
let print_as_case n = n.print_as_case
let set_print_as_case n p = n.print_as_case <- Some p

(* Create a new notation with specified name, fixity, and tightness.  Its mutable fields must be set later. *)
let make :
    type left tight right. string -> (left, tight, right) fixity -> (left, tight, right) notation =
 fun name fixity ->
  let left, tightness, right = fixprops fixity in
  let id = !counter in
  let dummy () = () in
  counter := !counter + 1;
  {
    name;
    id;
    dummy;
    tightness;
    left;
    right;
    tree = None;
    print = None;
    print_as_case = None;
    compiler = None;
  }

(* Helper functions for constructing notation trees *)

let op tok x =
  Inner { ops = TokMap.singleton tok x; constr = None; field = None; ident = None; term = None }

let ops toks =
  Inner { ops = TokMap.of_list toks; constr = None; field = None; ident = None; term = None }

let term tok x =
  Inner
    {
      ops = TokMap.empty;
      constr = None;
      field = None;
      ident = None;
      term = Some (TokMap.singleton tok x);
    }

let terms toks =
  Inner
    {
      ops = TokMap.empty;
      constr = None;
      field = None;
      ident = None;
      term = Some (TokMap.of_list toks);
    }

let constr x =
  Inner { ops = TokMap.empty; constr = Some x; field = None; ident = None; term = None }

let field x = Inner { ops = TokMap.empty; constr = None; field = Some x; ident = None; term = None }
let ident x = Inner { ops = TokMap.empty; constr = None; field = None; ident = Some x; term = None }
let of_entry e = Inner { ops = e; constr = None; field = None; ident = None; term = None }

(* Similar, but for "entries". *)
let eop tok x = TokMap.singleton tok x
let eops toks = TokMap.of_list toks
let empty_entry = TokMap.empty

(* Merging notation trees. *)

let merge_opt : ('a -> 'a -> 'a) -> 'a option -> 'a option -> 'a option =
 fun m x y ->
  match (x, y) with
  | None, None -> None
  | Some x, None -> Some x
  | None, Some y -> Some y
  | Some x, Some y -> Some (m x y)

let rec to_branch : tree -> (flag list * branch) option = function
  | Flag (f, x) ->
      let open Monad.Ops (Monad.Maybe) in
      let* fs, br = to_branch x in
      Some (f :: fs, br)
  | Inner b -> Some ([], b)
  | Done _ -> None
  | Lazy (lazy t) -> to_branch t

(* If either trees have flags, we just combine them all.  Flags for different notations are disjoint, so they can just ignore each other's. *)
let rec merge_tree : tree -> tree -> tree =
 fun xs ys ->
  (* Yes, I really do mean physical equality here.  The purpose of this test is to prevent merging a tree with itself, since that leads to an infinite loop.  And since each defining notation tree is created just once, it only exists in one place in memory, so a physical equality test will usually work.  (A structural equality test *won't* work, since trees can contain functional (lazy) values which can't be compared for structural equality.)  TODO: I think attempting to merge a notation tree with itself should always indicate a bug, but if so then we have at least one bug. *)
  if xs == ys then xs (* fatal (Anomaly "Merging a notation tree with itself") *)
  else
    let open Monad.Ops (Monad.Maybe) in
    Option.value
      (let* xf, xb = to_branch xs in
       let* yf, yb = to_branch ys in
       return
         (List.fold_right
            (fun f z -> Flag (f, z))
            xf
            (List.fold_right (fun f z -> Flag (f, z)) yf (Inner (merge_branch xb yb)))))
      (* We are not maximally tolerant of ambiguity.  In principle, it is possible to have one mixfix notation that is a strict initial segment of the other, like the "if_then_" and "if_then_else_" discussed in Danielsson-Norell.  However, it seems very hard to parse such a setup without a significant amount of backtracking, so we forbid it.  This is detected here at merge time.  Note that this includes the case of two notations that are identical.  (It is, of course, possible to have two notations that start out the same but then diverge, like _⊢_⦂_ and _⊢_type -- this is the whole point of merging trees.)  However, because this could happen accidentally when importing many notations from different libraries, we don't raise the error unless it actually comes up during parsing, by wrapping it in a lazy branch of the notation tree. *)
      ~default:(Lazy (lazy (fatal (Parsing_ambiguity "One notation is a prefix of another"))))

and merge_tmap : tree TokMap.t -> tree TokMap.t -> tree TokMap.t =
 fun x y -> TokMap.union (fun _ xb yb -> Some (merge_tree xb yb)) x y

and merge_branch : branch -> branch -> branch =
 fun x y ->
  let ops = merge_tmap x.ops y.ops in
  let ident = merge_opt merge_tree x.ident y.ident in
  let constr = merge_opt merge_tree x.constr y.constr in
  let field = merge_opt merge_tree x.field y.field in
  let term = merge_opt merge_tmap x.term y.term in
  { ops; constr; field; ident; term }

let merge : entry -> entry -> entry =
 fun x y -> TokMap.union (fun _ xb yb -> Some (merge_tree xb yb)) x y
