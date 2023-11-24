open Util
open Notation
module TokMap = Map.Make (Token)
module NSet = Set.Make (Notation)
module TIMap = Map.Make (Interval)

(* This module doesn't deal with the reasons why notations are turned on and off.  Instead we just provide a data structure that stores a "notation state", which can be used for parsing, and let other modules manipulate those states by adding notations to them.  (Because we store precomputed trees, removing a notation doesn't work as well; it's probably better to just pull out the set of all notations in a state, remove some, and then create a new state with just those.) *)
type t = {
  (* All the available notations. *)
  notations : NSet.t;
  (* We store a pre-merged tree of all left-closed notations.  TODO: This should really be the same as tighters of the empty interval (-∞,+∞], but that doesn't seem to work right now. *)
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
          (Interval (Strict, No.plus_omega), empty_entry);
          (Interval (Nonstrict, No.plus_omega), empty_entry);
          (Interval (Strict, No.minus_omega), empty_entry);
          (Interval (Nonstrict, No.minus_omega), empty_entry);
        ];
    left_opens = TokMap.empty;
  }

let add (n : 'tight notation) (s : t) : t =
  let notations = NSet.add (Wrap n) s.notations in
  let left_closeds = if left n = Closed then merge s.left_closeds (tree n) else s.left_closeds in
  (* First we merge the new notation to all the tighter-trees in which it should lie. *)
  let tighters =
    TIMap.mapi
      (fun i tr ->
        if
          (left n = Closed && Interval.contains i No.plus_omega)
          || Interval.contains i (tightness n)
        then merge tr (tree n)
        else tr)
      s.tighters in
  (* Then, if its tightness is new for this state, we create new tighter-trees for the corresponding two intervals. *)
  let tighters =
    (* We use Open here, but we could equally have used Closed, since we always add them in pairs. *)
    if not (TIMap.mem (Interval (Strict, tightness n)) tighters) then
      let open_tighters =
        NSet.fold
          (fun (Wrap m) tr ->
            match (left m, No.compare Strict (tightness n) (tightness m)) with
            | Closed, _ | _, Some _ -> merge (tree m) tr
            | _ -> tr)
          notations empty_entry in
      let closed_tighters =
        NSet.fold
          (fun (Wrap m) tr ->
            (* Leaving off "left m = Open" here would re-merge in all the left-closed notations, and merging a tree with itself can lead to infinite loops.  (The physical equality test above should catch most of them, but when it comes to avoiding infinite loops I'm a belt-and-suspenders person.) *)
            match (left m, No.equalb (tightness n) (tightness m)) with
            | Open, _ | _, true -> merge (tree m) tr
            | _ -> tr)
          notations open_tighters in
      tighters
      |> TIMap.add (Interval (Strict, tightness n)) open_tighters
      |> TIMap.add (Interval (Nonstrict, tightness n)) closed_tighters
    else tighters in
  let left_opens =
    if left n = Open then
      let ivl = Interval.left n in
      TokMap.fold (fun tok _ map -> TokMap.add_to_list tok ivl map) (tree n) s.left_opens
    else s.left_opens in
  { notations; left_closeds; left_opens; tighters }
