open Util
(* Partial bijections. *)

(* An element of ('a, 'ax, 'by, 'b) pbij is a partial bijection from 'ax to 'by, where 'a is the subset of 'ax that is omitted, and 'b is the subset of 'by that is omitted. *)
type (_, _, _, _) pbij =
  | Zero : ('a, 'a, D.zero, D.zero) pbij
  | Suc : ('a, 'ax, 'by, 'b) pbij * 'ax D.suc D.index -> ('a, 'ax D.suc, 'by D.suc, 'b) pbij
  | Skip : ('a, 'ax, 'by, 'b) pbij -> ('a, 'ax, 'by D.suc, 'b D.suc) pbij

let rec cozero : type b. b D.t -> (D.zero, D.zero, b, b) pbij = function
  | Nat Zero -> Zero
  | Nat (Suc b) -> Skip (cozero (Nat b))

type (_, _) any_pbij = Any : ('a, 'ax, 'by, 'b) pbij -> ('ax, 'by) any_pbij

(* List all the partial bijections from ax to by. *)
let rec pbijs : type ax by. ax D.t -> by D.t -> (ax, by) any_pbij list =
 fun ax by ->
  match (ax, by) with
  | _, Nat Zero -> [ Any Zero ]
  | Nat Zero, _ -> [ Any (cozero by) ]
  | Nat (Suc ax'), Nat (Suc by) ->
      let skips = pbijs ax (Nat by) in
      let sucs = pbijs (Nat ax') (Nat by) in
      List.map (fun (Any p) -> Any (Skip p)) skips
      @ List.flatten
          (List.map (fun (Any p) -> List.map (fun i -> Any (Suc (p, i))) (D.indices ax)) sucs)

(* A partial bijection is represented by a list (here a Bwv) of positive integers and strings, corresponding to the generating dimensions in 'ax.  Each integer specifies a generator to correspond to in 'by, the strings represent elements of 'ax that don't appear, while the elements of 'by that don't appear are unlisted. *)
module Pbij_strings = struct
  type t = [ `Int of int | `Deg ] list

  let empty : t = []
  let is_empty (xs : t) : bool = xs = []
  let compare : t -> t -> int = fun x y -> compare x y

  (* Unlike for degeneracies, the list representation has to be visible outside Dim, since it is the result of parsing, while we can't make it into a partial bijection until typechecking time since that's when we know 'by.  This operation only fails if there are invalid direction names.  In addition, if we were to allow concatenated representations like "123", there would be technical ambiguity (though, I think, almost never in practice) since that *could* be just a single number 123 with all the other directions missing.  Thus, we require the user to always separate them, and by periods in the field name, so the input to this function is already a list.  *)
  let of_strings : string list -> t option =
   fun strs ->
    let open Mlist.Monadic (Monad.Maybe) in
    mmapM
      (fun [ x ] ->
        match int_of_string_opt x with
        | Some i -> Some (`Int i)
        | None -> if x = Endpoints.refl_string then Some `Deg else None)
      [ strs ]

  let to_strings : t -> string list =
    List.map (function
      | `Int i -> string_of_int i
      | `Deg -> Endpoints.refl_string)
end

let pbij_of_strings : type ax by. Pbij_strings.t -> ax D.t -> by D.t -> (ax, by) any_pbij option =
 fun xs ax by ->
  let rec go : type ax by. ([ `Int of int | `Deg ], ax) Bwv.t -> by D.t -> (ax, by) any_pbij option
      =
   fun xs by ->
    (* If 'by is 0, then all the remaining generating dimensions must be degeneracies, and the partial bijection is a Zero. *)
    match by with
    | Nat Zero ->
        if Bwv.fold_right (fun x b -> x = `Deg && b) xs true then Some (Any Zero) else None
    | Nat (Suc by') -> (
        (* Otherwise, if 'ax is 0, the partial bijection consists of skips, i.e. it is a cozero. *)
        match xs with
        | Emp -> Some (Any (cozero by))
        | Snoc _ -> (
            (* If both 'ax and 'by are positive, we find where the last generating dimension of 'by occurs in the list and remove it, remembering its index to supply to Suc. *)
            match Bwv.find_remove (`Int (N.to_int by)) xs with
            | Some (xs, j) -> (
                (* Then what' left we can recurse into with a smaller expected codomain. *)
                match go xs (Nat by') with
                | None -> None
                | Some (Any s) -> Some (Any (Suc (s, j))))
            (* If it's missing, we skip that element of 'by. *)
            | None -> (
                match go xs (Nat by') with
                | None -> None
                | Some (Any s) -> Some (Any (Skip s))))) in
  match Bwv.of_list ax xs with
  | Some (xs, []) -> go xs by
  | _ -> None