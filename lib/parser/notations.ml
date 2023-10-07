open Util
module TokMap = Map.Make (Token)
module TokSet = Set.Make (Token)

(* A mixfix notation is an abstract object with a global existence.  They are represented internally by integers, to make them easily comparable and look-up-able. *)
module Notation : sig
  type t

  val make : unit -> t
  val compare : t -> t -> int
end = struct
  type t = int

  let counter = ref 0

  let make () =
    let n = !counter in
    counter := !counter + 1;
    n

  let compare : t -> t -> int = fun x y -> compare x y
end

(* A notation is either open or closed, on both sides.  We call these two properties combined its "fixity", since they are equivalent to the traditional classification as infix, prefix, postfix, or "outfix".

    left | right | traditional name
   ------|-------|------------------
    open | open  | infix
   closed| open  | prefix
    open |closed | postfix
   closed|closed | closed / outfix / around-fix
*)
type openness = Open | Closed

(* A notation is left-associative, right-associative, or non-associative.  Note that only an infix or prefix notation can meaningfully be right-associative, while only an infix or postfix notation can meaningfully be left-associative. *)
type associativity = Left | Right | Non

(* While parsing a notation, we may need to record certain information other than the names and subterms encountered.  We store this in "flags". *)
type flag = ..

(* A "notation tree" (not to be confused with a "parse tree", which is the *result* of parsing) carries the information about how to parse one or more notations.  Each individual notation is defined by giving one tree, but multiple such trees can also be "merged" together.  This allows different notations that start out looking the same to be parsed with minimal backtracking, as we don't need to "decide" which notation we're parsing until we get to the point of the tree where they diverge.  Accordingly, although each notation is associated to a defining tree, a tree also stores pointers to notations at its leaves, since a merged tree could parse many different notations depending on which path through it is taken. *)

(* The trees corresponding to notations that are open on one side or the other do *not* record the existence of the leftmost or rightmost subterm: they only store the operators, names, and fully delimited "inner" subterms.  Thus, a notation tree does not fully characterize the behavior of a notation until paired with the information of its openness on each side. *)
type tree =
  | Inner : branch -> tree
  | Done : Notation.t -> tree
  | Flag : flag * tree -> tree
  (* Trees associated to notations of arbitrary length are infinite, so we allow them to be computed lazily as needed. *)
  | Lazy : tree Lazy.t -> tree

(* When there is a choice in parsing, we arrange it so that there is as little backtracking required as possible: we test all the possible next literal tokens, the possibility of a field or constructor, variable, other term, or being done with this node.  With this arrangement, the only necessary backtracking is that a var could also be a term, so if both of those options are present, we have to backtrack after trying to parse a var and failing. *)
and branch = {
  ops : tree TokMap.t;
  constr : tree option;
  name : tree option;
  term : tree TokMap.t option;
  fail : string list;
}

(* Helper functions for constructing notation trees *)

let op tok x =
  Inner { ops = TokMap.singleton tok x; constr = None; name = None; term = None; fail = [] }

let ops toks =
  Inner { ops = TokMap.of_list toks; constr = None; name = None; term = None; fail = [] }

let term tok x =
  Inner
    {
      ops = TokMap.empty;
      constr = None;
      name = None;
      term = Some (TokMap.singleton tok x);
      fail = [];
    }

let terms toks =
  Inner
    { ops = TokMap.empty; constr = None; name = None; term = Some (TokMap.of_list toks); fail = [] }

let constr x = Inner { ops = TokMap.empty; constr = Some x; name = None; term = None; fail = [] }
let name x = Inner { ops = TokMap.empty; constr = None; name = Some x; term = None; fail = [] }
let fail err = { ops = TokMap.empty; constr = None; name = None; term = None; fail = [ err ] }

(* The entry point of a notation tree must begin with an operator symbol. *)
type entry = tree TokMap.t

let of_entry e = Inner { ops = e; constr = None; name = None; term = None; fail = [] }
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
  (* Yes, I really do mean physical equality here.  The purpose of this test is to prevent merging a tree with itself, since that leads to an infinite loop.  And since each defining notation tree is created just once, it only exists in one place in memory, so a physical equality test will usually work.  (A structural equality test *won't* work, since trees can contain functional (lazy) values which can't be compared for structural equality.) *)
  if xs == ys then xs
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
      (* We are not maximally tolerant of ambiguity.  In principle, it is possible to have one mixfix notation that is a strict initial segment of the other, like the "if_then_" and "if_then_else_" discussed in Danielsson-Norell.  However, it seems very hard to parse such a setup without a significant amount of backtracking, so we forbid it.  This is detected here at merge time.  Note that this includes the case of two notations that are identical.  (It is, of course, possible to have two notations that start out the same but then diverge, like _⊢_⦂_ and _⊢_type -- this is the whole point of merging trees.)  *)
      ~default:(Inner (fail "Incompatible notations: one is a prefix of the another."))

and merge_tmap : tree TokMap.t -> tree TokMap.t -> tree TokMap.t =
 fun x y -> TokMap.union (fun _ xb yb -> Some (merge_tree xb yb)) x y

and merge_branch : branch -> branch -> branch =
 fun x y ->
  let ops = merge_tmap x.ops y.ops in
  let name = merge_opt merge_tree x.name y.name in
  let constr = merge_opt merge_tree x.constr y.constr in
  let term = merge_opt merge_tmap x.term y.term in
  let fail = x.fail @ y.fail in
  { ops; constr; name; term; fail }

let merge : entry -> entry -> entry =
 fun x y -> TokMap.union (fun _ xb yb -> Some (merge_tree xb yb)) x y

(* Finally, this data structure stores *all* the information about a particular notation: its tree, openness, associativity and also precedence.  The latter, which we call "tightness" to make it obvious that higher numbers bind more tightly, is a floating-point number.

   Using a DAG for precedence, as in Danielsson-Norell, is a nice idea, but it seems to require a lot of backtracking: if when parsing the right-hand argument of a notation ∧ you encounter a notation * that isn't tighter than ∧, you can't know yet that it is forbidden; you have to keep parsing in case you encounter another notation like = that is tighter than ∧ and looser than *, or in fact multiple such notations forming some arbitrarily complicated path through the DAG.  This is incompatible with the minimal-backtracking approach we take, so we stick to numerical tightnesses.

   Our approach is based on the parsing technique of Pratt.  This means that a notation that's closed on both sides doesn't need a tightness at all (it behaves like the highest possible tightness on a closed side), so we give those a tightness of NaN.  User-defined notations that are open on at least one side have finite tightness, while +∞ and −∞ tightness are reserved for internal built-in notations (let-in, abstraction, and ascription are −∞, while +∞ is currently unused -- Danielsson-Norell say that parentheses are tighter than everything, but in our setup they don't need a tightness at all since they are closed on both sides. *)
type data = {
  name : string;
  tightness : float;
  left : openness;
  right : openness;
  assoc : associativity;
  tree : entry;
}

(* An "upper tightness interval" is of the form [p,+∞] or (p,+∞] for some tightness p. *)
module Interval = struct
  (* This meaning of "open" and "closed" refers to "open intervals" and "closed intervals", which is unfortunately unrelated to the notions of "left-open" and "right-open" notations. *)
  type t = Closed of float | Open of float

  let entire = Closed Float.neg_infinity

  let to_string = function
    | Closed x -> Printf.sprintf "[%f,inf]" x
    | Open x -> Printf.sprintf "(%f,inf]" x

  let endpoint : t -> float = function
    | Closed x -> x
    | Open x -> x

  let right_assoc (tight : float) (assoc : associativity) : t =
    match assoc with
    | Right -> Closed tight
    | Left | Non -> Open tight

  let contains : t -> float -> bool =
   fun i x ->
    match i with
    | Closed p -> p <= x
    | Open p -> p < x

  (* A notation has associated upper tightness intervals on both the left and the right, which specify what tightnesses of other notations can appear in an open subterm on that side.  Thus, both of these intervals start at the tightness of the notation, with their open- or closed-ness determined by its associativity. *)
  let left : data -> t =
   fun d ->
    match d.assoc with
    | Left -> Closed d.tightness
    | Right | Non -> Open d.tightness

  let right : data -> t =
   fun d ->
    match d.assoc with
    | Right -> Closed d.tightness
    | Left | Non -> Open d.tightness

  let compare : t -> t -> int = fun x y -> compare x y
end

module FSet = Set.Make (Float)
module FMap = Map.Make (Float)
module NSet = Set.Make (Notation)
module TIMap = Map.Make (Interval)

(* This global hashtable stores the tightness, fixity, and associativity of all existing notations (which, recall, are global objects), without regard to namespacing or scopes. *)
let all_notations : (Notation.t, data) Hashtbl.t = Hashtbl.create 16
let get_data : Notation.t -> data = fun n -> Hashtbl.find all_notations n

(* Create a new notation, with given tightness, fixity, associativity, and defining tree, and add it to the global hashtable. *)
let make ~name ~tightness ~left ~right ~assoc ~tree =
  let n = Notation.make () in
  Hashtbl.add all_notations n { name; tightness; left; right; assoc; tree = tree n };
  n

(* This module doesn't deal with the reasons why notations are turned on and off.  Instead we just provide a data structure that stores a "notation state", which can be used for parsing, and let other modules manipulate those states by adding notations to them.  (Because we store precomputed trees, removing a notation doesn't work as well; it's probably better to just pull out the set of all notations in a state, remove some, and then create a new state with just those.) *)
module State = struct
  type t = {
    (* All the available notations. *)
    notations : NSet.t;
    (* We store a pre-merged tree of all left-closed notations. *)
    left_closeds : entry;
    (* For each upper tightness interval, we store a pre-merged tree of all left-closed trees along with all left-open trees whose tightness lies in that interval. *)
    tighters : entry TIMap.t;
    (* We store a map associating to each starting token of a left-open notation its left-hand upper tightness interval.  Since more than one left-open notation could in theory start with the same token, we actually store a list of such intervals.  In practice, the loosest one will be used preferentially. *)
    left_opens : Interval.t list TokMap.t;
  }

  let notations : t -> NSet.t = fun s -> s.notations

  let empty : t =
    {
      notations = NSet.empty;
      left_closeds = empty_entry;
      tighters =
        TIMap.of_list
          [
            (Open Float.infinity, empty_entry);
            (Closed Float.infinity, empty_entry);
            (Open Float.neg_infinity, empty_entry);
            (Closed Float.neg_infinity, empty_entry);
          ];
      left_opens = TokMap.empty;
    }

  let add (n : Notation.t) (s : t) : t =
    let data = get_data n in
    let notations = NSet.add n s.notations in
    let left_closeds =
      if data.left = Closed then merge s.left_closeds data.tree else s.left_closeds in
    (* First we merge the new notation to all the tighter-trees in which it should lie. *)
    let tighters =
      TIMap.mapi
        (fun i tr ->
          if data.left = Closed || Interval.contains i data.tightness then merge tr data.tree
          else tr)
        s.tighters in
    (* Then, if its tightness is new for this state, we create new tighter-trees for the corresponding two intervals. *)
    let tighters =
      (* We use Open here, but we could equally have used Closed, since we always add them in pairs. *)
      if not (TIMap.mem (Open data.tightness) tighters) then
        let open_tighters =
          NSet.fold
            (fun m tr ->
              let d = get_data m in
              if d.left = Closed || data.tightness < d.tightness then merge d.tree tr else tr)
            notations empty_entry in
        let closed_tighters =
          NSet.fold
            (fun m tr ->
              let d = get_data m in
              (* Leaving off "d.left = Open" here would re-merge in all the left-closed notations, and merging a tree with itself can lead to infinite loops.  (The physical equality test above should catch most of them, but when it comes to avoiding infinite loops I'm a belt-and-suspenders person.) *)
              if d.left = Open && data.tightness = d.tightness then merge d.tree tr else tr)
            notations open_tighters in
        tighters
        |> TIMap.add (Open data.tightness) open_tighters
        |> TIMap.add (Closed data.tightness) closed_tighters
      else tighters in
    let left_opens =
      if data.left = Open then
        let ivl = Interval.left data in
        TokMap.fold (fun tok _ map -> TokMap.add_to_list tok ivl map) data.tree s.left_opens
      else s.left_opens in
    { notations; left_closeds; left_opens; tighters }
end

(* Note that we are not storing here any information about the "meaning" of a notation, i.e. about how to "compile" a parsed notation into a term.  That is done by the Compile module. *)
