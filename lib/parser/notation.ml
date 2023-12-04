open Bwd
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
type (_, _) tree =
  | Inner : ('t, 's) branch -> ('t, 's) tree
  | Done_open : ('t, 's, 'tight) No.lt * ('left opn, 'tight, 'right) notation -> ('t, 's) tree
  | Done_closed : (closed, 'tight, 'right) notation -> ('t, 's) tree
  | Flag : flag * ('t, 's) tree -> ('t, 's) tree
  (* Trees associated to notations of arbitrary length are infinite, so we allow them to be computed lazily as needed. *)
  | Lazy : ('t, 's) tree Lazy.t -> ('t, 's) tree

(* When there is a choice in parsing, we arrange it so that there is as little backtracking required as possible: we test all the possible next literal tokens, the possibility of a field or constructor, variable, other term, or being done with this node.  With this arrangement, the only necessary backtracking is that an identifier or constructor could also be a term.  So if both of those options are present, we have to backtrack after trying to parse a constructor or identifier and failing. *)
and ('t, 's) branch = {
  ops : ('t, 's) tree TokMap.t;
  constr : ('t, 's) tree option;
  field : ('t, 's) tree option;
  ident : ('t, 's) tree option;
  term : ('t, 's) tree TokMap.t option;
}

(* The entry point of a notation tree must begin with an operator symbol. *)
and ('t, 's) entry = ('t, 's) tree TokMap.t

(* If we weren't using intrinsically well-scoped De Bruijn indices, then the typechecking context and the type of raw terms would be simply ordinary types, and we could use the one as the parsing State and the other as the parsing Result.  However, the Fmlib parser isn't set up to allow a parametrized family of state types, with the output of a parsing combinator depending on the state (and it would be tricky to do that correctly anyway).  So instead we record the result of parsing as a syntax tree with idents, and have a separate step of "compilation" that makes it into a raw term.  This has the additional advantage that by parsing and pretty-printing we can reformat code even if it is not well-scoped. *)
and observation =
  | Flagged of flag
  | Constr of string
  | Field of string
  | Ident of string option
  | Term : ('lt, 'ls, 'rt, 'rs) parse -> observation

(* A parsed notation, with its own tightness and openness, and lying in specified left and right tightness intervals, has a Bwd of observations in its inner holes, plus possibly a first and/or last term depending on its openness, and may require witnesses that it is tight enough on the left and/or the right also depending on its openness. *)
and ('left, 'tight, 'right, 'lt, 'ls, 'rt, 'rs) parsed_notn = {
  notn : ('left, 'tight, 'right) notation;
  first : ('lt, 'ls, 'tight, 'left) first_arg;
  inner : observation Bwd.t;
  last : ('tight, 'right, 'rt, 'rs) last_arg;
  left_ok : ('lt, 'ls, 'tight, 'left) tighter_than;
  right_ok : ('rt, 'rs, 'tight, 'right) tighter_than;
}

and (_, _, _, _) first_arg =
  | Some_first : ('lt, 'ls, 'tight, 'l) parse -> ('lt, 'ls, 'tight, 'l opn) first_arg
  | No_first : ('lt, 'ls, 'tight, closed) first_arg

and (_, _, _, _) last_arg =
  | Some_last : ('tight, 'r, 'rt, 'rs) parse -> ('tight, 'r opn, 'rt, 'rs) last_arg
  | No_last : ('tight, closed, 'rt, 'rs) last_arg

and (_, _, _, _) tighter_than =
  | Open_ok : ('lt, 'ls, 'tight) No.lt -> ('lt, 'ls, 'tight, 'l opn) tighter_than
  | Closed_ok : ('lt, 'ls, 'tight, closed) tighter_than

(* A "parse tree" is not to be confused with our "notation trees".  Note that these parse trees don't know anything about the *meanings* of notations either; those are stored by the "compilation" functions.  *)
and (_, _, _, _) parse =
  | Notn : ('left, 'tight, 'right, 'lt, 'ls, 'rt, 'rs) parsed_notn -> ('lt, 'ls, 'rt, 'rs) parse
  (* We treat application as a left-associative binary infix operator of tightness +ω.  Note that like any infix operator, its left argument must be in its left interval and its right argument must be in its right interval. *)
  | App : {
      fn : ('lt, 'ls, No.plus_omega, No.nonstrict) parse;
      arg : (No.plus_omega, No.strict, 'rt, 'rs) parse;
      left_ok : ('lt, 'ls, No.plus_omega) No.lt;
      right_ok : ('rt, 'rs, No.plus_omega) No.lt;
    }
      -> ('lt, 'ls, 'rt, 'rs) parse
  | Ident : string -> ('lt, 'ls, 'rt, 'rs) parse
  | Constr : string -> ('lt, 'ls, 'rt, 'rs) parse
  | Field : string -> ('lt, 'ls, 'rt, 'rs) parse
  | Numeral : Q.t -> ('lt, 'ls, 'rt, 'rs) parse
  (* A parsed abstraction already knows whether it is a normal abstraction or a cubical one, since different symbols ↦ and ⤇ are used.  We treat abstraction as a non-associative prefix operator of tightness -ω.  TODO: Should really be more like an infix operator, since it can't appear inside anything tighter than -ω coming from the left either.  But then we need to special-case somehow that it can right-associate with *itself* though not ascription. *)
  | Abs : {
      cube : [ `Cube | `Normal ];
      vars : string option list;
      body : (No.minus_omega, No.strict, 'rt, 'rs) parse;
      right_ok : ('rt, 'rs, No.minus_omega) No.lt;
    }
      -> ('lt, 'ls, 'rt, 'rs) parse

(* A compilation function has to be polymorphic over the length of the context so as to produce intrinsically well-scoped terms.  Thus, we have to wrap it as a field of a record (or object). *)
and compiler = { compile : 'n. (string option, 'n) Bwv.t -> observation list -> 'n check }

and ('left, 'tight) notation_entry =
  | Open_entry : ('tight, No.nonstrict) entry -> ('strict opn, 'tight) notation_entry
  | Closed_entry : (No.plus_omega, No.strict) entry -> (closed, 'tight) notation_entry

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
  mutable tree : ('left, 'tight) notation_entry option;
  mutable compiler : compiler option;
  (* Some notations only make sense in terms, others only make sense in case trees, and some make sense in either.  Thus, a notation can supply either or both of these printing functions. *)
  mutable print : (Format.formatter -> observation list -> unit) option;
  mutable print_as_case : (Format.formatter -> observation list -> unit) option;
}

let infix ~notn ~first ~inner ~last ~left_ok ~right_ok =
  Notn
    {
      notn;
      first = Some_first first;
      inner;
      last = Some_last last;
      left_ok = Open_ok left_ok;
      right_ok = Open_ok right_ok;
    }

let prefix ~notn ~inner ~last ~right_ok =
  Notn
    {
      notn;
      first = No_first;
      inner;
      last = Some_last last;
      left_ok = Closed_ok;
      right_ok = Open_ok right_ok;
    }

let postfix ~notn ~first ~inner ~left_ok =
  Notn
    {
      notn;
      first = Some_first first;
      inner;
      last = No_last;
      left_ok = Open_ok left_ok;
      right_ok = Closed_ok;
    }

let outfix ~notn ~inner =
  Notn { notn; first = No_first; inner; last = No_last; left_ok = Closed_ok; right_ok = Closed_ok }

let args :
    type left tight right lt ls rt rs.
    (left, tight, right, lt, ls, rt, rs) parsed_notn -> observation list =
 fun n ->
  let args =
    match n.last with
    | Some_last tm -> Snoc (n.inner, Term tm)
    | No_last -> n.inner in
  match n.first with
  | Some_first tm -> Term tm :: Bwd.to_list args
  | No_first -> Bwd.to_list args

type wrapped_parse = Wrap : ('lt, 'ls, 'rt, 'rs) parse -> wrapped_parse

(* When parsing from left to right, we have to return a partial parse tree without knowing yet what tightness interval it will have to be in from the right.  So we return it as a callback that takes that interval as an argument and can fail, returning the name of the offending notation if it fails.  One could argue that instead the allowable tightness intervals should be returned along with the partial parse tree and used to restrict the allowable notations parsed afterwards.  But for one thing, that would require indexing those pre-merged trees by *two* tightness values, so that we'd have to maintain n² such trees where n is the number of tightness values in use, and that makes me worry a bit about efficiency.  Furthermore, doing it this way makes it easier to trap it and issue a more informative error message, which I think is a good thing because this includes examples like "let x ≔ M in N : A" and "x ↦ M : A" where the need for parentheses in Narya may be surprising to a new user. *)
type ('lt, 'ls) right_wrapped_parse = {
  get : 'rt 'rs. ('rt, 'rs) Interval.tt -> (('lt, 'ls, 'rt, 'rs) parse, string) Result.t;
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

(* A partially-wrapped notation that can appear in a specified upper tightness interval. *)
type (_, _) notation_in_interval =
  | Open_in_interval :
      ('lt, 'ls, 'tight) No.lt * ('left opn, 'tight, 'right) notation
      -> ('lt, 'ls) notation_in_interval
  | Closed_in_interval : (closed, 'tight, 'right) notation -> ('lt, 'ls) notation_in_interval

(* The definition of Notation.t is abstract outside this file, so that we can guarantee they are only created with "make" below and the primary key increments every time.  Thus, we have to provide getter functions for all the fields that should be visible outside this file. *)
let name n = n.name
let tightness n = n.tightness
let left n = n.left
let right n = n.right

(* A notation has associated upper tightness intervals on both the left and the right, which specify what tightnesses of other notations can appear in an open subterm on that side.  Thus, both of these intervals start at the tightness of the notation, with their open- or closed-ness determined by its associativity. *)
let interval_left : ('s opn, 'tight, 'right) notation -> ('tight, 's) Interval.tt =
 fun n ->
  let (Open s) = left n in
  (s, tightness n)

let interval_right : ('left, 'tight, 's opn) notation -> ('tight, 's) Interval.tt =
 fun n ->
  let (Open s) = right n in
  (s, tightness n)

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
let done_open n = Done_open (No.le_refl (tightness n), n)

(* Similar, but for "entries". *)
let eop tok x = TokMap.singleton tok x
let eops toks = TokMap.of_list toks
let empty_entry = TokMap.empty

(* Merging notation trees. *)

let merge_opt : type a b. (a -> b -> a) -> (b -> a) -> a option -> b option -> a option =
 fun m l x y ->
  match (x, y) with
  | None, None -> None
  | Some x, None -> Some x
  | None, Some y -> Some (l y)
  | Some x, Some y -> Some (m x y)

let rec to_branch : type t s. (t, s) tree -> (flag list * (t, s) branch) option = function
  | Flag (f, x) ->
      let open Monad.Ops (Monad.Maybe) in
      let* fs, br = to_branch x in
      Some (f :: fs, br)
  | Inner b -> Some ([], b)
  | Done_open _ | Done_closed _ -> None
  | Lazy (lazy t) -> to_branch t

let rec lower_tree :
    type t1 s1 t2 s2. (t2, s2, t1, s1) Interval.subset -> (t2, s2) tree -> (t1, s1) tree =
 fun sub xs ->
  match xs with
  | Inner br -> Inner (lower_branch sub br)
  | Done_open (lt, n) -> Done_open (Interval.subset_contains sub lt, n)
  | Done_closed n -> Done_closed n
  | Flag (f, tr) -> Flag (f, lower_tree sub tr)
  | Lazy tr -> Lazy (lazy (lower_tree sub (Lazy.force tr)))

and lower_branch :
    type t1 s1 t2 s2. (t2, s2, t1, s1) Interval.subset -> (t2, s2) branch -> (t1, s1) branch =
 fun sub { ops; constr; field; ident; term } ->
  {
    ops = TokMap.map (lower_tree sub) ops;
    constr = Option.map (lower_tree sub) constr;
    field = Option.map (lower_tree sub) field;
    ident = Option.map (lower_tree sub) ident;
    term = Option.map (TokMap.map (lower_tree sub)) term;
  }

let lower : type t1 s1 t2 s2. (t2, s2, t1, s1) Interval.subset -> (t2, s2) entry -> (t1, s1) entry =
 fun sub map -> TokMap.map (lower_tree sub) map

let rec names : type t s. (t, s) tree -> string list = function
  | Inner { ops; constr; ident; field; term } ->
      Option.fold ~none:[] ~some:names constr
      @ Option.fold ~none:[] ~some:names ident
      @ Option.fold ~none:[] ~some:names field
      @ names_tmap ops
      @ Option.fold ~none:[] ~some:names_tmap term
  | Done_open (_, n) -> [ name n ]
  | Done_closed n -> [ name n ]
  | Flag (_, t) -> names t
  | Lazy _ -> []

and names_tmap : type t s. (t, s) tree TokMap.t -> string list =
 fun trees -> TokMap.fold (fun _ t xs -> names t @ xs) trees []

(* If either trees have flags, we just combine them all.  Flags for different notations are disjoint, so they can just ignore each other's. *)
let rec merge_tree :
    type t1 s1 t2 s2.
    (t2, s2, t1, s1) Interval.subset -> (t1, s1) tree -> (t2, s2) tree -> (t1, s1) tree =
 fun sub xs ys ->
  let open Monad.Ops (Monad.Maybe) in
  Option.value
    (let* xf, xb = to_branch xs in
     let* yf, yb = to_branch ys in
     return
       (List.fold_right
          (fun f z -> Flag (f, z))
          xf
          (List.fold_right (fun f z -> Flag (f, z)) yf (Inner (merge_branch sub xb yb)))))
    (* We are not maximally tolerant of ambiguity.  In principle, it is possible to have one mixfix notation that is a strict initial segment of the other, like the "if_then_" and "if_then_else_" discussed in Danielsson-Norell.  However, it seems very hard to parse such a setup without a significant amount of backtracking, so we forbid it.  This is detected here at merge time.  Note that this includes the case of two notations that are identical.  (It is, of course, possible to have two notations that start out the same but then diverge, like _⊢_⦂_ and _⊢_type -- this is the whole point of merging trees.)  However, because this could happen accidentally when importing many notations from different libraries, we don't raise the error unless it actually comes up during parsing, by wrapping it in a lazy branch of the notation tree. *)
    ~default:
      (Lazy
         (lazy
           (fatal
              (Parsing_ambiguity
                 (Printf.sprintf "One notation is a prefix of another: [%s] and [%s]"
                    (String.concat "; " (names xs))
                    (String.concat "; " (names ys)))))))

and merge_tmap :
    type t1 s1 t2 s2.
    (t2, s2, t1, s1) Interval.subset ->
    (t1, s1) tree TokMap.t ->
    (t2, s2) tree TokMap.t ->
    (t1, s1) tree TokMap.t =
 fun sub x y ->
  TokMap.fold
    (fun k yb ->
      TokMap.update k (function
        | None -> Some (lower_tree sub yb)
        | Some xb -> Some (merge_tree sub xb yb)))
    y x

and merge_branch :
    type t1 s1 t2 s2.
    (t2, s2, t1, s1) Interval.subset -> (t1, s1) branch -> (t2, s2) branch -> (t1, s1) branch =
 fun sub x y ->
  let ops = merge_tmap sub x.ops y.ops in
  let ident = merge_opt (merge_tree sub) (lower_tree sub) x.ident y.ident in
  let constr = merge_opt (merge_tree sub) (lower_tree sub) x.constr y.constr in
  let field = merge_opt (merge_tree sub) (lower_tree sub) x.field y.field in
  let term = merge_opt (merge_tmap sub) (TokMap.map (lower_tree sub)) x.term y.term in
  { ops; constr; field; ident; term }

let merge :
    type t1 t2 s1 s2.
    (t2, s2, t1, s1) Interval.subset -> (t1, s1) entry -> (t2, s2) entry -> (t1, s1) entry =
 fun sub xs ys -> merge_tmap sub xs ys
