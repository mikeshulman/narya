open Bwd
open Util
open Core
open Syntax.Raw
open Reporter
module TokMap = Map.Make (Token)
open Asai.Range

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

(* A "notation tree" (not to be confused with a "parse tree", which is the *result* of parsing) carries the information about how to parse one or more notations.  Each individual notation is defined by giving one tree, but multiple such trees can also be "merged" together.  This allows different notations that start out looking the same to be parsed with minimal backtracking, as we don't need to "decide" which notation we're parsing until we get to the point of the tree where they diverge.  Accordingly, although each notation is associated to a defining tree, a tree also stores pointers to notations at its leaves, since a merged tree could parse many different notations depending on which path through it is taken. *)

(* The trees corresponding to notations that are open on one side or the other do *not* record the existence of the leftmost or rightmost subterm: they only record the positions of the operators and fully delimited "inner" subterms.  Thus, a notation tree does not fully characterize the behavior of a notation until paired with the information of its openness on each side. *)

(* A notation tree is parametrized by an upper tightness interval and is guaranteed to produce only notations that lie in that interval from the left. *)
type (_, _) tree =
  | Inner : ('t, 's) branch -> ('t, 's) tree
  | Done_open : ('t, 's, 'tight) No.lt * ('left opn, 'tight, 'right) notation -> ('t, 's) tree
  (* However, left-closed notations can lie in any tightness interval on that side. *)
  | Done_closed : (closed, 'tight, 'right) notation -> ('t, 's) tree
  (* Trees associated to notations of arbitrary length are infinite, so we allow them to be computed lazily as needed. *)
  | Lazy : ('t, 's) tree Lazy.t -> ('t, 's) tree

(* When there is a choice in parsing, we arrange it so that no backtracking is required (except for a single token of lookahead).  We test all the possible next literal tokens, considering the possibility of a notation operator, field, or other term.  (Constructors and identifiers are considered special terms, and extracted during postprocessing.)  Operators and fields cannot also be other terms, so there is no need for backtracking. *)
and ('t, 's) branch = {
  ops : ('t, 's) tree TokMap.t;
  field : ('t, 's) tree option;
  term : ('t, 's) tree TokMap.t option;
}

(* The entry point of a notation tree must begin with an operator symbol. *)
and ('t, 's) entry = ('t, 's) tree TokMap.t

(* If we weren't using intrinsically well-scoped De Bruijn indices, then the typechecking context and the type of raw terms would be simply ordinary types, and we could use the one as the parsing State and the other as the parsing Result.  However, the Fmlib parser isn't set up to allow a parametrized family of state types, with the output of a parsing combinator depending on the state (and it would be tricky to do that correctly anyway).  So instead we record the result of parsing as a syntax tree with idents, and have a separate step of "postprocessing" that makes it into a raw term.  This has the additional advantage that by parsing and pretty-printing we can reformat code even if it is not well-scoped. *)
and observation = Term : ('lt, 'ls, 'rt, 'rs) parse located -> observation

(* A parsed notation, with its own tightness and openness, and lying in specified left and right tightness intervals, has a Bwd of observations in its inner holes, plus possibly a first and/or last term depending on its openness.  It is parametrized by the openness and tightness of the notation, and also by upper tightness intervals from the left and right in which it is guaranteed to lie.  Thus, the first and last term (if any) can be guaranteed statically to be valid, and we may require witnesses that the notation is tight enough on the left and/or the right (also depending on its openness) to fit in the specified intervals. *)
and ('left, 'tight, 'right, 'lt, 'ls, 'rt, 'rs) parsed_notn =
  | Infix : {
      notn : ('left opn, 'tight, 'right opn) notation;
      first : ('lt, 'ls, 'tight, 'left) parse located;
      inner : observation Bwd.t;
      last : ('tight, 'right, 'rt, 'rs) parse located;
      left_ok : ('lt, 'ls, 'tight) No.lt;
      right_ok : ('rt, 'rs, 'tight) No.lt;
    }
      -> ('left opn, 'tight, 'right opn, 'lt, 'ls, 'rt, 'rs) parsed_notn
  | Prefix : {
      notn : (closed, 'tight, 'right opn) notation;
      inner : observation Bwd.t;
      last : ('tight, 'right, 'rt, 'rs) parse located;
      right_ok : ('rt, 'rs, 'tight) No.lt;
    }
      -> (closed, 'tight, 'right opn, 'lt, 'ls, 'rt, 'rs) parsed_notn
  | Postfix : {
      notn : ('left opn, 'tight, closed) notation;
      first : ('lt, 'ls, 'tight, 'left) parse located;
      inner : observation Bwd.t;
      left_ok : ('lt, 'ls, 'tight) No.lt;
    }
      -> ('left opn, 'tight, closed, 'lt, 'ls, 'rt, 'rs) parsed_notn
  | Outfix : {
      notn : (closed, 'tight, closed) notation;
      inner : observation Bwd.t;
    }
      -> (closed, 'tight, closed, 'lt, 'ls, 'rt, 'rs) parsed_notn

(* A "parse tree" is not to be confused with our "notation trees".  Note that these parse trees don't know anything about the *meanings* of notations either; those are stored by the "postprocessing" functions. *)
and (_, _, _, _) parse =
  | Notn : ('left, 'tight, 'right, 'lt, 'ls, 'rt, 'rs) parsed_notn -> ('lt, 'ls, 'rt, 'rs) parse
  (* We treat application as a left-associative binary infix operator of tightness +ω.  Note that like any infix operator, its left argument must be in its left interval and its right argument must be in its right interval. *)
  | App : {
      fn : ('lt, 'ls, No.plus_omega, No.nonstrict) parse located;
      arg : (No.plus_omega, No.strict, 'rt, 'rs) parse located;
      left_ok : ('lt, 'ls, No.plus_omega) No.lt;
      right_ok : ('rt, 'rs, No.plus_omega) No.lt;
    }
      -> ('lt, 'ls, 'rt, 'rs) parse
  | Placeholder : ('lt, 'ls, 'rt, 'rs) parse
  | Ident : string list -> ('lt, 'ls, 'rt, 'rs) parse
  | Constr : string -> ('lt, 'ls, 'rt, 'rs) parse
  | Field : string -> ('lt, 'ls, 'rt, 'rs) parse
  | Numeral : Q.t -> ('lt, 'ls, 'rt, 'rs) parse

(* A postproccesing function has to be polymorphic over the length of the context so as to produce intrinsically well-scoped terms.  Thus, we have to wrap it as a field of a record (or object). *)
and processor = {
  process :
    'n. (string option, 'n) Bwv.t -> observation list -> Asai.Range.t option -> 'n check located;
}

(* The entry point of the parse tree defining a particular notation must be parametrized either by the representable non-strict interval at that tightness, or by the empty interval in case of a left-closed notation. *)
and ('left, 'tight) notation_entry =
  | Open_entry : ('tight, No.nonstrict) entry -> ('strict opn, 'tight) notation_entry
  | Closed_entry : (No.plus_omega, No.strict) entry -> (closed, 'tight) notation_entry

(* A notation has a precedence, which we call "tightness" to make it obvious that higher numbers bind more tightly, and is a floating-point number.  Using a DAG for precedence, as in Danielsson-Norell, is a nice idea, but it seems to require a lot of backtracking: if when parsing the right-hand argument of a notation ∧ you encounter a notation * that isn't tighter than ∧, you can't know yet that it is forbidden; you have to keep parsing in case you encounter another notation like = that is tighter than ∧ and looser than *, or in fact multiple such notations forming some arbitrarily complicated path through the DAG.  This is incompatible with the minimal-backtracking approach we take, so we stick to numerical tightnesses.

   Our approach is based on the parsing technique of Pratt.  This means that a notation that's closed on both sides doesn't need a tightness at all (it behaves like the highest possible tightness on a closed side), so we give those a tightness of NaN.  User-defined notations that are open on at least one side have finite tightness, while +ω and −ω tightness are reserved for internal built-in notations (let-in, abstraction, and ascription are −ω, while all outfix notations such as parentheses (and also, morally, application) have tightness +ω. *)
and ('left, 'tight, 'right) notation = {
  name : string;
  id : int; (* Autonumber primary key *)
  dummy : unit -> unit; (* Block polymorphic comparison *)
  tightness : 'tight No.t;
  left : 'left openness;
  right : 'right openness;
  (* The remaining fields are mutable because they have to be able to refer to the notation object itself, so we have a circular data structure.  They aren't expected to mutate further after being set once.  Thus we store them as options, to record whether they have been set. *)
  mutable tree : ('left, 'tight) notation_entry option;
  mutable processor : processor option;
  (* Some notations only make sense in terms, others only make sense in case trees, and some make sense in either.  Thus, a notation can supply either or both of these printing functions. *)
  mutable print : (Format.formatter -> observation list -> unit) option;
  mutable print_as_case : (Format.formatter -> observation list -> unit) option;
}

module Notation = struct
  type t = Wrap : ('left, 'tight, 'right) notation -> t
end

let empty_branch = { ops = TokMap.empty; field = None; term = None }

let infix ~notn ~first ~inner ~last ~left_ok ~right_ok =
  Notn (Infix { notn; first; inner; last; left_ok; right_ok })

let prefix ~notn ~inner ~last ~right_ok = Notn (Prefix { notn; inner; last; right_ok })
let postfix ~notn ~first ~inner ~left_ok = Notn (Postfix { notn; first; inner; left_ok })
let outfix ~notn ~inner = Notn (Outfix { notn; inner })

let args :
    type left tight right lt ls rt rs.
    (left, tight, right, lt, ls, rt, rs) parsed_notn -> observation list = function
  | Infix { first; inner; last; _ } -> Term first :: Bwd.to_list (Snoc (inner, Term last))
  | Prefix { inner; last; _ } -> Bwd.to_list (Snoc (inner, Term last))
  | Postfix { first; inner; _ } -> Term first :: Bwd.to_list inner
  | Outfix { inner; _ } -> Bwd.to_list inner

let notn :
    type left tight right lt ls rt rs.
    (left, tight, right, lt, ls, rt, rs) parsed_notn -> (left, tight, right) notation = function
  | Infix { notn; _ } -> notn
  | Prefix { notn; _ } -> notn
  | Postfix { notn; _ } -> notn
  | Outfix { notn; _ } -> notn

(* When parsing from left to right, we have to return a partial parse tree without knowing yet what tightness interval it will have to be in from the right.  So we return it as a callback that takes that interval as an argument and can fail, returning the name of the offending notation if it fails.  One could argue that instead the allowable tightness intervals should be returned along with the partial parse tree and used to restrict the allowable notations parsed afterwards.  But that would require indexing those pre-merged trees by *two* tightness values, so that we'd have to maintain n² such trees where n is the number of tightness values in use, and that makes me worry a bit about efficiency.  Doing it this way also makes it easier to trap it and issue a more informative error message. *)
type ('lt, 'ls) right_wrapped_parse = {
  get : 'rt 'rs. ('rt, 'rs) Interval.tt -> (('lt, 'ls, 'rt, 'rs) parse located, string) Result.t;
}

(* The primary key is used to compare notations. *)
let counter = ref 0

let equal : type l1 t1 r1 l2 t2 r2. (l1, t1, r1) notation -> (l2, t2, r2) notation -> bool =
 fun x y -> x.id = y.id

(* A partially-wrapped notation that can appear in a specified upper tightness interval on the left. *)
type (_, _) notation_in_interval =
  | Open_in_interval :
      ('lt, 'ls, 'tight) No.lt * ('left opn, 'tight, 'right) notation
      -> ('lt, 'ls) notation_in_interval
  | Closed_in_interval : (closed, 'tight, 'right) notation -> ('lt, 'ls) notation_in_interval

(* The definition of 'notation' is abstract outside this file, so that we can guarantee they are only created with "make" below and the primary key increments every time.  Thus, we have to provide getter functions for all the fields that should be visible outside this file. *)
let name n = n.name
let tightness n = n.tightness
let left n = n.left
let right n = n.right

(* A notation has associated upper tightness intervals on both the left and the right, which specify what tightnesses of other notations can appear in an open subterm on that side.  Thus, both of these intervals start at the tightness of the notation, with their open- or closed-ness determined by its associativity. *)
let interval_left : ('s opn, 'tight, 'right) notation -> ('tight, 's) Interval.tt =
 fun n ->
  let (Open strictness) = left n in
  { strictness; endpoint = tightness n }

let interval_right : ('left, 'tight, 's opn) notation -> ('tight, 's) Interval.tt =
 fun n ->
  let (Open strictness) = right n in
  { strictness; endpoint = tightness n }

(* For the mutable fields, we also have to provide setter functions.  Since these fields are only intended to be set once, the setters throw an exception if the value is already set (and the getters for tree and processor throw an exception if it is not yet set).  *)

let tree n = Option.get n.tree

let set_tree n t =
  match n.tree with
  | Some _ -> raise (Invalid_argument "notation tree already set")
  | None -> n.tree <- Some t

let processor n =
  match n.processor with
  | Some c -> c
  | None -> raise (Invalid_argument "notation has no processor")

let set_processor n c =
  match n.processor with
  | Some _ -> raise (Invalid_argument "notation processor already set")
  | None -> n.processor <- Some c

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
    processor = None;
  }

(* Helper functions for constructing notation trees *)

let op tok x = Inner { empty_branch with ops = TokMap.singleton tok x }
let ops toks = Inner { empty_branch with ops = TokMap.of_list toks }
let term tok x = Inner { empty_branch with term = Some (TokMap.singleton tok x) }
let terms toks = Inner { empty_branch with term = Some (TokMap.of_list toks) }
let field x = Inner { empty_branch with field = Some x }
let of_entry e = Inner { empty_branch with ops = e }
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

let rec to_branch : type t s. (t, s) tree -> (t, s) branch option = function
  | Inner b -> Some b
  | Done_open _ | Done_closed _ -> None
  | Lazy (lazy t) -> to_branch t

let rec lower_tree :
    type t1 s1 t2 s2. (t2, s2, t1, s1) Interval.subset -> (t2, s2) tree -> (t1, s1) tree =
 fun sub xs ->
  match xs with
  | Inner br -> Inner (lower_branch sub br)
  | Done_open (lt, n) -> Done_open (Interval.subset_contains sub lt, n)
  | Done_closed n -> Done_closed n
  | Lazy tr -> Lazy (lazy (lower_tree sub (Lazy.force tr)))

and lower_branch :
    type t1 s1 t2 s2. (t2, s2, t1, s1) Interval.subset -> (t2, s2) branch -> (t1, s1) branch =
 fun sub { ops; field; term } ->
  {
    ops = TokMap.map (lower_tree sub) ops;
    field = Option.map (lower_tree sub) field;
    term = Option.map (TokMap.map (lower_tree sub)) term;
  }

let lower : type t1 s1 t2 s2. (t2, s2, t1, s1) Interval.subset -> (t2, s2) entry -> (t1, s1) entry =
 fun sub map -> TokMap.map (lower_tree sub) map

let rec names : type t s. (t, s) tree -> string list = function
  | Inner { ops; field; term } ->
      Option.fold ~none:[] ~some:names field
      @ names_tmap ops
      @ Option.fold ~none:[] ~some:names_tmap term
  | Done_open (_, n) -> [ name n ]
  | Done_closed n -> [ name n ]
  | Lazy _ -> []

and names_tmap : type t s. (t, s) tree TokMap.t -> string list =
 fun trees -> TokMap.fold (fun _ t xs -> names t @ xs) trees []

let rec merge_tree :
    type t1 s1 t2 s2.
    (t2, s2, t1, s1) Interval.subset -> (t1, s1) tree -> (t2, s2) tree -> (t1, s1) tree =
 fun sub xs ys ->
  let open Monad.Ops (Monad.Maybe) in
  Option.value
    (let* xb = to_branch xs in
     let* yb = to_branch ys in
     return (Inner (merge_branch sub xb yb)))
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
  let field = merge_opt (merge_tree sub) (lower_tree sub) x.field y.field in
  let term = merge_opt (merge_tmap sub) (TokMap.map (lower_tree sub)) x.term y.term in
  { ops; field; term }

let merge :
    type t1 t2 s1 s2.
    (t2, s2, t1, s1) Interval.subset -> (t1, s1) entry -> (t2, s2) entry -> (t1, s1) entry =
 fun sub xs ys -> merge_tmap sub xs ys
