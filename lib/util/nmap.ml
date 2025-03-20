open Signatures
module Key = N

(* An intrinsically well-typed dependently-typed map whose domain is type-level nat, and whose codomain type can be parametrized by the key and by an extra parameter.  *)

module Make (F : Fam2) : MAP with module Key := N and module F := F = struct
  (* We represent such a map as the list of its possible values, with 0 coming first and then 1 and so on, stopping when there are no more entries.  To get things to be well-typed, the sub-lists must be parametrized by the distance into the map that we've already descended.  Later we will define "the" type of maps to be the ones parametrized by zero.  *)
  type ('b, 'n) map = Entry of ('b, 'n) F.t option * ('b, 'n N.suc) map | Empty

  (* Similarly, the operations are naturally defined on the generic version, and then specialized for the caller to the ones parametrized by zero. *)
  module Internal = struct
    let rec find_opt : type b m n mn. (m, n, mn) Fwn.bplus -> (b, m) map -> (b, mn) F.t option =
     fun mn map ->
      match map with
      | Empty -> None
      | Entry (x, xs) -> (
          match mn with
          | Zero -> x
          | Suc mn -> find_opt mn xs)

    let rec add : type b m n mn. (m, n, mn) Fwn.bplus -> (b, mn) F.t -> (b, m) map -> (b, m) map =
     fun mn x map ->
      match (mn, map) with
      | Zero, Empty -> Entry (Some x, Empty)
      | Zero, Entry (_, xs) -> Entry (Some x, xs)
      | Suc mn, Empty -> Entry (None, add mn x Empty)
      | Suc mn, Entry (y, xs) -> Entry (y, add mn x xs)

    let rec update : type b m n mn.
        (m, n, mn) Fwn.bplus ->
        ((b, mn) F.t option -> (b, mn) F.t option) ->
        (b, m) map ->
        (b, m) map =
     fun mn f map ->
      match (mn, map) with
      | Zero, Empty -> Entry (f None, Empty)
      | Zero, Entry (x, xs) -> Entry (f x, xs)
      | Suc mn, Empty -> Entry (None, update mn f Empty)
      | Suc mn, Entry (y, xs) -> Entry (y, update mn f xs)

    let rec remove : type b m n mn. (m, n, mn) Fwn.bplus -> (b, m) map -> (b, m) map =
     fun mn map ->
      match map with
      | Empty -> Empty
      | Entry (x, xs) -> (
          match mn with
          | Zero -> Entry (None, xs)
          | Suc mn -> Entry (x, remove mn xs))

    type 'a mapper = { map : 'g. 'g N.t -> ('a, 'g) F.t -> ('a, 'g) F.t }

    let rec map : type a m. a mapper -> m N.t -> (a, m) map -> (a, m) map =
     fun f m mp ->
      match mp with
      | Empty -> Empty
      | Entry (x, xs) -> Entry (Option.map (f.map m) x, map f (N.suc m) xs)

    type 'a iterator = { it : 'g. 'g N.t -> ('a, 'g) F.t -> unit }

    let rec iter : type a m. a iterator -> m N.t -> (a, m) map -> unit =
     fun f m map ->
      match map with
      | Empty -> ()
      | Entry (x, xs) ->
          Option.iter (f.it m) x;
          iter f (N.suc m) xs
  end

  let find_opt : type b n. n N.t -> (b, N.zero) map -> (b, n) F.t option =
   fun n map ->
    let (Of_bwn (_, mn)) = Fwn.of_bwn n in
    Internal.find_opt mn map

  let add : type b n. n N.t -> (b, n) F.t -> (b, N.zero) map -> (b, N.zero) map =
   fun n x map ->
    let (Of_bwn (_, mn)) = Fwn.of_bwn n in
    Internal.add mn x map

  let update : type b n.
      n N.t -> ((b, n) F.t option -> (b, n) F.t option) -> (b, N.zero) map -> (b, N.zero) map =
   fun n f map ->
    let (Of_bwn (_, mn)) = Fwn.of_bwn n in
    Internal.update mn f map

  let remove : type b n. n N.t -> (b, N.zero) map -> (b, N.zero) map =
   fun n map ->
    let (Of_bwn (_, mn)) = Fwn.of_bwn n in
    Internal.remove mn map

  type 'a mapper = { map : 'g. 'g N.t -> ('a, 'g) F.t -> ('a, 'g) F.t }

  let map : type b. b mapper -> (b, N.zero) map -> (b, N.zero) map =
   fun f mp -> Internal.map { map = f.map } N.zero mp

  type 'a iterator = { it : 'g. 'g N.t -> ('a, 'g) F.t -> unit }

  let iter : type b. b iterator -> (b, N.zero) map -> unit =
   fun f m -> Internal.iter { it = f.it } N.zero m

  type 'b t = ('b, N.zero) map

  let empty : type b. b t = Empty
end
