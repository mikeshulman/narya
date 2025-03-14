open Util
open Core
open Reporter
open Notation
open User2
module TokMap = Map.Make (Token)
module Trie = Yuujinchou.Trie

(* A notation "situation" is the collection of all the notations currently available.  Unfortunately, good words like "state" and "context" and "scope" are taken for other things, so "situation" is the best I've been able to come up with to uniquely identify this object. *)

module EntryPair = struct
  type ('x, 'a) t = { strict : ('a, No.strict) entry; nonstrict : ('a, No.nonstrict) entry }
end

module EntryMap = No.Map.Make (EntryPair)

module PrintKey = struct
  type t = User.key

  let compare : t -> t -> int = compare
end

module PrintMap = Map.Make (PrintKey)

(* This module doesn't deal with the reasons why notations are turned on and off.  Instead we just provide a data structure that stores a "notation situation", which can be used for parsing, and let other modules manipulate those situations by adding notations to them.  (Because we store precomputed trees, removing a notation doesn't work as well; it's probably better to just pull out the set of all notations in a situation, remove some, and then create a new situation with just those.) *)
type t = {
  (* For each upper tightness interval, we store a pre-merged tree of all left-closed trees along with all left-open trees whose tightness lies in that interval.  In particular, for the empty interval (+ω,+ω] this contains only the left-closed trees, and for the entire interval [-ω,+ω] it contains all notation trees. *)
  tighters : unit EntryMap.t;
  (* We store a map associating to each starting token of a left-open notation its left-hand upper tightness interval.  If there is more than one left-open notation starting with the same token, we store the loosest such interval. *)
  left_opens : No.interval TokMap.t;
  (* For unparsing we also store backwards maps turning constants and constructors into notations.  Since the arguments of a notation can occur in a different order from those of the constant or constructor, we store lists of the argument names in the order they occur in the pattern and in the term value.  Note that these permutations are only used for printing; when parsing, the postprocessor function must ALSO incorporate the inverse permutation. *)
  unparse : User.notation PrintMap.t;
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
  let d = find n in
  let left, tightness, _ = fixprops (snd n) in
  let tighters =
    EntryMap.add_cut tightness
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
    match (left, d.tree) with
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
          tightness tighters
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
    match (left, d.tree) with
    | Open _, Open_entry tr ->
        let ivl = No.Interval (interval_left n) in
        TokMap.fold
          (fun tok _ map ->
            TokMap.update tok
              (function
                | None -> Some ivl
                | Some ivl2 -> Some (No.Interval.union ivl ivl2))
              map)
          tr s.left_opens
    | Closed, _ -> s.left_opens in
  (* We don't update the printing map since this is used for builtins that are printed specially. *)
  { s with tighters; left_opens }

(* Add a notation along with the information about how to unparse a constant or constructor into that notation. *)
let add_with_print : User.notation -> t -> t =
 fun notn sit ->
  let (Wrap n) = notn.notn in
  let sit = add n sit in
  { sit with unparse = sit.unparse |> PrintMap.add notn.key notn }

let add_user : User.prenotation -> t -> t * (User.notation * bool) =
 fun user sit ->
  let notn = make_user user in
  let shadow = PrintMap.mem notn.key sit.unparse in
  (add_with_print notn sit, (notn, shadow))

let add_users : t -> Scope.trie -> t =
 fun sit trie ->
  Seq.fold_left
    (fun state (_, ((data, _), _)) ->
      match data with
      | `Notation (user, _) -> fst (add_user user state)
      | _ -> state)
    sit
    (Trie.to_seq (Trie.find_subtree [ "notations" ] trie))

module S = State.Make (struct
  type nonrec t = t
end)

let () =
  S.register_printer (function
    | `Get -> Some "unhandled notation situation get effect"
    | `Set _ -> Some "unhandled notation situation set effect")

module Current = struct
  let add : type left tight right. (left, tight, right) notation -> unit =
   fun notn -> S.modify (add notn)

  let add_with_print : User.notation -> unit = fun notn -> S.modify (add_with_print notn)

  let add_user : User.prenotation -> User.notation * bool =
   fun user ->
    let sit = S.get () in
    let sit, (notn, shadow) = add_user user sit in
    S.set sit;
    (notn, shadow)

  let left_closeds : unit -> (No.plus_omega, No.strict) entry =
   fun () ->
    (EntryMap.find_opt No.plus_omega (S.get ()).tighters <|> Anomaly "missing left_closeds").strict

  let tighters : type strict tight. (tight, strict) No.iinterval -> (tight, strict) entry =
   fun { strictness; endpoint } ->
    let ep = EntryMap.find_opt endpoint (S.get ()).tighters <|> Anomaly "missing tighters" in
    match strictness with
    | Nonstrict -> ep.nonstrict
    | Strict -> ep.strict

  let left_opens : Token.t -> No.interval option =
   fun tok -> TokMap.find_opt tok (S.get ()).left_opens

  let unparse : PrintKey.t -> User.notation option = fun c -> PrintMap.find_opt c (S.get ()).unparse
end

let run_on init f = S.run ~init f
let try_with = S.try_with
