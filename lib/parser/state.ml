open Util
open Notation
module TokMap = Map.Make (Token)
module NSet = Set.Make (Notation)
module TIMap = Map.Make (Interval)

(* This module doesn't deal with the reasons why notations are turned on and off.  Instead we just provide a data structure that stores a "notation state", which can be used for parsing, and let other modules manipulate those states by adding notations to them.  (Because we store precomputed trees, removing a notation doesn't work as well; it's probably better to just pull out the set of all notations in a state, remove some, and then create a new state with just those.) *)
type t = {
  (* We store a pre-merged tree of all left-closed notations.  TODO: This should really be the same as tighters of the empty interval (+∞,+∞], but that doesn't seem to work right now. *)
  left_closeds : entry;
  (* For each upper tightness interval, we store a pre-merged tree of all left-closed trees along with all left-open trees whose tightness lies in that interval. *)
  tighters : entry TIMap.t;
  (* We store a map associating to each starting token of a left-open notation its left-hand upper tightness interval.  Since more than one left-open notation could in theory start with the same token, we actually store a list of such intervals.  In practice, the loosest one will be used preferentially. *)
  left_opens : Interval.t list TokMap.t;
}

let empty : t =
  {
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

let add : type left tight right. (left, tight, right) notation -> t -> t =
 fun n s ->
  let left_closeds =
    match left n with
    | Closed -> merge s.left_closeds (tree n)
    | Open _ -> s.left_closeds in
  (* First we merge the new notation to all the tighter-trees in which it should lie. *)
  let tighters =
    TIMap.mapi
      (fun (Interval i) tr ->
        match left n with
        | Closed -> (
            match Interval.contains i No.plus_omega with
            | Some _ -> merge tr (tree n)
            | None -> tr)
        | Open _ -> (
            match Interval.contains i (tightness n) with
            | Some _ -> merge tr (tree n)
            | None -> tr))
      s.tighters in
  (* Then, if its tightness is new for this state, we create new tighter-trees for the corresponding two intervals.  The strict one is a copy of the next-smallest nonstrict interval, while the nonstrict one is a copy of the next-largest strict interval. *)
  let tighters =
    (* We use Open here, but we could equally have used Closed, since we always add them in pairs. *)
    if not (TIMap.mem (Interval (Strict, tightness n)) tighters) then
      let _, open_tighters =
        TIMap.fold
          (fun (Interval (strict, tight)) entry ((No.Wrap next_tight, _) as next) ->
            match
              ( strict,
                No.compare Nonstrict (tightness n) tight,
                No.compare Nonstrict tight next_tight )
            with
            | Nonstrict, Some _, Some _ -> (No.Wrap tight, entry)
            | _ -> next)
          tighters
          (No.Wrap No.plus_omega, empty_entry) in
      let _, closed_tighters =
        TIMap.fold
          (fun (Interval (strict, tight)) entry ((No.Wrap prev_tight, _) as prev) ->
            match
              ( strict,
                No.compare Nonstrict tight (tightness n),
                No.compare Nonstrict prev_tight tight )
            with
            | Strict, Some _, Some _ -> (No.Wrap tight, entry)
            | _ -> prev)
          tighters
          (No.Wrap No.minus_omega, empty_entry) in
      tighters
      |> TIMap.add (Interval (Strict, tightness n)) open_tighters
      |> TIMap.add (Interval (Nonstrict, tightness n)) closed_tighters
    else tighters in
  let left_opens =
    match left n with
    | Open _ ->
        let ivl = Interval.Interval (interval_left n) in
        TokMap.fold (fun tok _ map -> TokMap.add_to_list tok ivl map) (tree n) s.left_opens
    | Closed -> s.left_opens in
  { left_closeds; left_opens; tighters }
