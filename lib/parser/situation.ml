open Util
open Core
open Reporter
open Notation
open Postprocess
open Format
open Print
open User
module TokMap = Map.Make (Token)

(* A notation "situation" is the collection of all the notations currently available.  Unfortunately, good words like "state" and "context" and "scope" are taken for other things, so "situation" is the best I've been able to come up with to uniquely identify this object. *)

module EntryPair = struct
  type ('x, 'a) t = { strict : ('a, No.strict) entry; nonstrict : ('a, No.nonstrict) entry }
end

module EntryMap = No.Map.Make (EntryPair)

module PrintKey = struct
  type t = printkey

  let compare : t -> t -> int = compare
end

module PrintMap = Map.Make (PrintKey)

(* This module doesn't deal with the reasons why notations are turned on and off.  Instead we just provide a data structure that stores a "notation situation", which can be used for parsing, and let other modules manipulate those situations by adding notations to them.  (Because we store precomputed trees, removing a notation doesn't work as well; it's probably better to just pull out the set of all notations in a situation, remove some, and then create a new situation with just those.) *)
type t = {
  (* For each upper tightness interval, we store a pre-merged tree of all left-closed trees along with all left-open trees whose tightness lies in that interval.  In particular, for the empty interval (+ω,+ω] this contains only the left-closed trees, and for the entire interval [-ω,+ω] it contains all notation trees. *)
  tighters : unit EntryMap.t;
  (* We store a map associating to each starting token of a left-open notation its left-hand upper tightness interval.  If there is more than one left-open notation starting with the same token, we store the loosest such interval. *)
  left_opens : Interval.t TokMap.t;
  (* For unparsing we also store backwards maps turning constants and constructors into notations.  Since the arguments of a notation can occur in a different order from those of the constant or constructor, we store lists of the argument names in the order they occur in the pattern and in the term value.  Note that these permutations are only used for printing; when parsing, the postprocessor function must ALSO incorporate the inverse permutation. *)
  unparse : permuted_notation PrintMap.t;
}

let empty : t =
  {
    tighters =
      EntryMap.empty
      |> EntryMap.add No.plus_omega { strict = empty_entry; nonstrict = empty_entry }
      |> EntryMap.add No.minus_omega { strict = empty_entry; nonstrict = empty_entry };
    left_opens = TokMap.empty;
    unparse = PrintMap.empty;
  }

(* Add a new notation to the current situation of available ones. *)
let add : type left tight right. (left, tight, right) notation -> t -> t =
 fun n s ->
  (* First, if its tightness is new for this situation, we create new tighter-trees for the corresponding two interval_vars.  The strict one is a copy of the next-smallest nonstrict interval, while the nonstrict one is a copy of the next-largest strict interval. *)
  let tighters =
    EntryMap.add_cut (tightness n)
      (fun _ up ->
        match up with
        | Upper (lt, u) ->
            let nonstrict = lower (Subset_strict lt) u.nonstrict in
            let strict = lower (Subset_strict lt) u.nonstrict in
            { strict; nonstrict }
        | _ -> fatal (Anomaly "Missing +ω in notation situation"))
      s.tighters in
  (* Then we merge the new notation to all the tighter-trees in which it should lie. *)
  let tighters =
    match (left n, tree n) with
    | Open _, Open_entry tr ->
        EntryMap.map_compare
          {
            map_lt =
              (fun lt { strict; nonstrict } ->
                {
                  nonstrict = merge (Subset_strict lt) nonstrict tr;
                  strict = merge (Subset_strict lt) strict tr;
                });
            map_gt = (fun _ e -> e);
            map_eq =
              (fun { strict; nonstrict } -> { nonstrict = merge Subset_eq nonstrict tr; strict });
          }
          (tightness n) tighters
    | Closed, Closed_entry tr ->
        EntryMap.map_compare
          {
            map_lt =
              (fun lt { strict; nonstrict } ->
                {
                  nonstrict = merge (Subset_strict lt) nonstrict tr;
                  strict = merge (Subset_strict lt) strict tr;
                });
            map_gt = (fun _ e -> e);
            map_eq =
              (fun { strict; nonstrict } ->
                {
                  nonstrict = merge Subset_nonstrict_strict nonstrict tr;
                  strict = merge Subset_eq strict tr;
                });
          }
          No.plus_omega tighters in
  (* Finally, we update the map of all starting tokens of left-open notations. *)
  let left_opens =
    match (left n, tree n) with
    | Open _, Open_entry tr ->
        let ivl = Interval.Interval (interval_left n) in
        TokMap.fold
          (fun tok _ map ->
            TokMap.update tok
              (function
                | None -> Some ivl
                | Some ivl2 -> Some (Interval.union ivl ivl2))
              map)
          tr s.left_opens
    | Closed, _ -> s.left_opens in
  (* We don't update the printing map since this is used for builtins that are printed specially. *)
  { s with tighters; left_opens }

(* Add a notation along with the information about how to unparse a constant or constructor into that notation. *)
let add_with_print : permuted_notation -> t -> t =
 fun notn sit ->
  let (Wrap n) = notn.notn in
  let sit = add n sit in
  { sit with unparse = sit.unparse |> PrintMap.add notn.key notn }

type pattern =
  [ `Op of Token.t * space * Whitespace.t list
  | `Var of string * space * Whitespace.t list
  | `Ellipsis of Whitespace.t list ]
  list

let user_tree :
    type left tight right.
    (left, tight, right) fixity ->
    (left, tight, right) notation ->
    pattern ->
    (left, tight) notation_entry =
 fun fixity notn pattern ->
  let left, _, _ = fixprops fixity in
  let rec user_tree pattern n =
    match (pattern, left) with
    | [], Closed -> n
    | [], Open _ -> fatal (Anomaly "pattern doesn't match deduced fixity")
    | [ `Var _ ], Open _ -> n
    | [ `Var _ ], Closed -> fatal (Anomaly "pattern doesn't match deduced fixity")
    | `Op (tok, _, _) :: pat_vars, _ -> op tok (user_tree pat_vars n)
    | `Var _ :: `Op (tok, _, _) :: pat_vars, _ -> term tok (user_tree pat_vars n)
    | `Var _ :: `Var _ :: _, _ -> fatal Missing_notation_symbol
    | `Var _ :: `Ellipsis _ :: _, _ -> fatal (Unimplemented "internal ellipses in notation")
    | `Ellipsis _ :: _, _ -> fatal (Unimplemented "internal ellipses in notation") in
  match (pattern, left) with
  | [], _ -> fatal (Anomaly "empty pattern")
  | `Op (tok, _, _) :: pat_vars, Closed ->
      Closed_entry (eop tok (user_tree pat_vars (Done_closed notn)))
  | `Var _ :: `Op (tok, _, _) :: pat_vars, Open _ ->
      Open_entry (eop tok (user_tree pat_vars (done_open notn)))
  | `Var _ :: _, Closed | `Op _ :: _, Open _ ->
      fatal (Anomaly "pattern doesn't match deduced fixity")
  | `Var _ :: `Ellipsis _ :: _, _ | `Ellipsis _ :: _, _ ->
      fatal (Unimplemented "internal ellipses in notation")
  | `Var _ :: `Var _ :: _, _ -> fatal Missing_notation_symbol
  | [ `Var _ ], _ -> fatal Zero_notation_symbols

let make_user : user_notation -> permuted_notation =
 fun (User { name; fixity; pattern; key; val_vars }) ->
  let n = make name fixity in
  let pat_vars =
    List.filter_map
      (function
        | `Op _ | `Ellipsis _ -> None
        | `Var (x, _, _) -> Some x)
      pattern in
  set_tree n (user_tree fixity n pattern);
  set_processor n
    { process = (fun ctx obs loc _ -> process_user key pat_vars val_vars ctx obs loc) };
  set_print n (fun space ppf obs ws ->
      pp_open_hvbox ppf 0;
      pp_user pattern n true ppf pattern obs ws `None;
      pp_close_box ppf ();
      pp_space ppf space);
  { key; notn = Wrap n; pat_vars; val_vars }

let add_user : user_notation -> t -> t * (permuted_notation * bool) =
 fun user sit ->
  let notn = make_user user in
  let shadow = PrintMap.mem notn.key sit.unparse in
  (add_with_print notn sit, (notn, shadow))

module S = Algaeff.State.Make (struct
  type nonrec t = t
end)

let () =
  S.register_printer (function
    | `Get -> Some "unhandled notation state get effect"
    | `Set _ -> Some "unhandled notation state set effect")

module Current = struct
  let add : type left tight right. (left, tight, right) notation -> unit =
   fun notn -> S.modify (add notn)

  let add_user : user_notation -> permuted_notation * bool =
   fun user ->
    let sit = S.get () in
    let sit, (notn, shadow) = add_user user sit in
    S.set sit;
    (notn, shadow)

  let left_closeds : unit -> (No.plus_omega, No.strict) entry =
   fun () -> (Option.get (EntryMap.find_opt No.plus_omega (S.get ()).tighters)).strict

  let tighters : type strict tight. (tight, strict) Interval.tt -> (tight, strict) entry =
   fun { strictness; endpoint } ->
    let ep = Option.get (EntryMap.find_opt endpoint (S.get ()).tighters) in
    match strictness with
    | Nonstrict -> ep.nonstrict
    | Strict -> ep.strict

  let left_opens : Token.t -> Interval.t option =
   fun tok -> TokMap.find_opt tok (S.get ()).left_opens

  let unparse : PrintKey.t -> permuted_notation option =
   fun c -> PrintMap.find_opt c (S.get ()).unparse
end

let run_on init f = S.run ~init f
