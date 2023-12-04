open Util
open Core.Reporter
open Notation
module TokMap = Map.Make (Token)
module NSet = Set.Make (Notation)

module EntryPair = struct
  type 'a t = { strict : entry; nonstrict : entry }
end

module EntryMap = No.MapMake (EntryPair)

(* This module doesn't deal with the reasons why notations are turned on and off.  Instead we just provide a data structure that stores a "notation state", which can be used for parsing, and let other modules manipulate those states by adding notations to them.  (Because we store precomputed trees, removing a notation doesn't work as well; it's probably better to just pull out the set of all notations in a state, remove some, and then create a new state with just those.) *)
type t = {
  (* For each upper tightness interval, we store a pre-merged tree of all left-closed trees along with all left-open trees whose tightness lies in that interval.  In particular, for the empty interval (+ω,+ω] this contains only the left-closed trees, and for the entire interval [-ω,+ω] it contains all notation trees. *)
  tighters : EntryMap.t;
  (* We store a map associating to each starting token of a left-open notation its left-hand upper tightness interval.  If there is more than one left-open notation starting with the same token, we store the loosest such interval. *)
  left_opens : Interval.t TokMap.t;
}

let empty : t =
  {
    tighters =
      EntryMap.empty
      |> EntryMap.add No.plus_omega { strict = empty_entry; nonstrict = empty_entry }
      |> EntryMap.add No.minus_omega { strict = empty_entry; nonstrict = empty_entry };
    left_opens = TokMap.empty;
  }

let merger :
    type a s b. entry -> (a, s, b) No.lt -> s No.strictness -> a EntryPair.t -> a EntryPair.t =
 fun tr _ str { strict; nonstrict } ->
  let nonstrict = merge nonstrict tr in
  let strict =
    match str with
    | Nonstrict -> strict
    | Strict -> merge strict tr in
  { nonstrict; strict }

let merge_all :
    type a s b. entry -> (a, s, b) No.lt -> s No.strictness -> a EntryPair.t -> a EntryPair.t =
 fun tr _ _ { strict; nonstrict } ->
  let nonstrict = merge nonstrict tr in
  let strict = merge strict tr in
  { nonstrict; strict }

let add : type left tight right. (left, tight, right) notation -> t -> t =
 fun n s ->
  (* First we merge the new notation to all the tighter-trees in which it should lie. *)
  let tighters =
    match left n with
    | Open _ ->
        EntryMap.map_le { map = (fun lt str -> merger (tree n) lt str) } (tightness n) s.tighters
    | Closed ->
        EntryMap.map_le { map = (fun lt str -> merge_all (tree n) lt str) } No.plus_omega s.tighters
  in
  (* Then, if its tightness is new for this state, we create new tighter-trees for the corresponding two intervals.  The strict one is a copy of the next-smallest nonstrict interval, while the nonstrict one is a copy of the next-largest strict interval. *)
  let tighters =
    EntryMap.add_cut (tightness n)
      (fun lower upper ->
        match (lower, upper) with
        | Lower (_, l), Upper (_, u) -> { strict = u.nonstrict; nonstrict = l.strict }
        | _ -> fatal (Anomaly "Missing ±ω in notation state"))
      tighters in
  (* Finally, we update the map of all starting tokens of left-open notations. *)
  let left_opens =
    match left n with
    | Open _ ->
        let ivl = Interval.Interval (interval_left n) in
        TokMap.fold
          (fun tok _ map ->
            TokMap.update tok
              (function
                | None -> Some ivl
                | Some ivl2 -> Some (Interval.union ivl ivl2))
              map)
          (tree n) s.left_opens
    | Closed -> s.left_opens in
  { tighters; left_opens }

let left_closeds s = (Option.get (EntryMap.find s.tighters No.plus_omega)).strict

let tighters : type strict tight. t -> strict No.strictness * tight No.t -> entry =
 fun state (strict, tight) ->
  let ep = Option.get (EntryMap.find state.tighters tight) in
  match strict with
  | Nonstrict -> ep.nonstrict
  | Strict -> ep.strict
