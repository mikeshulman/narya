open Util
open Core
open Reporter
open Notation
module TokMap = Map.Make (Token)
module ConstMap = Map.Make (Core.Constant)

module StringListMap = Map.Make (struct
  type t = string list

  let compare : t -> t -> int = compare
end)

module EntryPair = struct
  type 'a t = { strict : ('a, No.strict) entry; nonstrict : ('a, No.nonstrict) entry }
end

module EntryMap = No.MapMake (EntryPair)

type permuted_notation = { notn : Notation.t; pats : string list; vals : string list }

(* This module doesn't deal with the reasons why notations are turned on and off.  Instead we just provide a data structure that stores a "notation state", which can be used for parsing, and let other modules manipulate those states by adding notations to them.  (Because we store precomputed trees, removing a notation doesn't work as well; it's probably better to just pull out the set of all notations in a state, remove some, and then create a new state with just those.) *)
type t = {
  (* For each upper tightness interval, we store a pre-merged tree of all left-closed trees along with all left-open trees whose tightness lies in that interval.  In particular, for the empty interval (+ω,+ω] this contains only the left-closed trees, and for the entire interval [-ω,+ω] it contains all notation trees. *)
  tighters : EntryMap.t;
  (* We store a map associating to each starting token of a left-open notation its left-hand upper tightness interval.  If there is more than one left-open notation starting with the same token, we store the loosest such interval. *)
  left_opens : Interval.t TokMap.t;
  (* For unparsing we also store backwards maps turning constants and constructors into notations.  Since the arguments of a notation can occur in a different order from those of the constant or constructor, we store lists of the argument names in the order they occur in the pattern and in the term value.  Note that these permutations are only used for printing; when parsing, the postprocessor function must ALSO incorporate the inverse permutation. *)
  print_const : permuted_notation ConstMap.t;
  print_constr : permuted_notation Constr.Map.t;
}

let empty : t =
  {
    tighters =
      EntryMap.empty
      |> EntryMap.add No.plus_omega { strict = empty_entry; nonstrict = empty_entry }
      |> EntryMap.add No.minus_omega { strict = empty_entry; nonstrict = empty_entry };
    left_opens = TokMap.empty;
    print_const = ConstMap.empty;
    print_constr = Constr.Map.empty;
  }

(* Add a new notation to the current state of available ones. *)
let add : type left tight right. (left, tight, right) notation -> t -> t =
 fun n s ->
  (* First, if its tightness is new for this state, we create new tighter-trees for the corresponding two intervals.  The strict one is a copy of the next-smallest nonstrict interval, while the nonstrict one is a copy of the next-largest strict interval. *)
  let tighters =
    EntryMap.add_cut (tightness n)
      (fun _ up ->
        match up with
        | Upper (lt, u) ->
            let nonstrict = lower (Subset_strict lt) u.nonstrict in
            let strict = lower (Subset_strict lt) u.nonstrict in
            { strict; nonstrict }
        | _ -> fatal (Anomaly "Missing +ω in notation state"))
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

let add_const : Core.Constant.t -> permuted_notation -> t -> t =
 fun const notn state ->
  if ConstMap.mem const state.print_const then state
  else
    let (Wrap n) = notn.notn in
    let state = add n state in
    { state with print_const = state.print_const |> ConstMap.add const notn }

let add_constr : Core.Constr.t -> permuted_notation -> t -> t =
 fun constr notn state ->
  if Constr.Map.mem constr state.print_constr then state
  else
    let (Wrap n) = notn.notn in
    let state = add n state in
    { state with print_constr = state.print_constr |> Constr.Map.add constr notn }

module S = Algaeff.State.Make (struct
  type nonrec t = t
end)

module Current = struct
  let add : type left tight right. (left, tight, right) notation -> unit =
   fun notn -> S.modify (add notn)

  let add_const : Core.Constant.t -> permuted_notation -> unit =
   fun const notn -> S.modify (add_const const notn)

  let add_constr : Core.Constr.t -> permuted_notation -> unit =
   fun constr notn -> S.modify (add_constr constr notn)

  let left_closeds : unit -> (No.plus_omega, No.strict) entry =
   fun () -> (Option.get (EntryMap.find (S.get ()).tighters No.plus_omega)).strict

  let tighters : type strict tight. (tight, strict) Interval.tt -> (tight, strict) entry =
   fun { strictness; endpoint } ->
    let ep = Option.get (EntryMap.find (S.get ()).tighters endpoint) in
    match strictness with
    | Nonstrict -> ep.nonstrict
    | Strict -> ep.strict

  let left_opens : Token.t -> Interval.t option =
   fun tok -> TokMap.find_opt tok (S.get ()).left_opens

  let print_const : Core.Constant.t -> permuted_notation option =
   fun c -> ConstMap.find_opt c (S.get ()).print_const

  let print_constr : Core.Constr.t -> permuted_notation option =
   fun c -> Constr.Map.find_opt c (S.get ()).print_constr
end

let run_on init f = S.run ~init f
