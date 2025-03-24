open Util
open Tlist
open Signatures
open Deg
open Insertion
open Shuffle

(* A partial bijection is an insertion together with a shuffle.  Specifically, a partial bijection from a dimension 'evaluation to a dimension 'intrinsic consists of:
   - A dimension 'shared (the part of each that are bijective)
   - An insertion of 'shared into another dimension 'result to obtain 'evaluation.  This performs the permutation of 'shared.
   - A shuffle of 'shared into another dimension 'remaining to produce 'intrinsic.
   We currently parametrize a partial bijection by 'evaluation (the domain), 'intrinsic (the codomain), and 'remaining.  We haven't needed the others so far. *)

type (_, _, _) pbij =
  | Pbij :
      ('evaluation, 'result, 'shared) insertion * ('remaining, 'shared, 'intrinsic) shuffle
      -> ('evaluation, 'intrinsic, 'remaining) pbij

let dom_pbij : type e i r. (e, i, r) pbij -> e D.t = fun (Pbij (ins, _)) -> dom_ins ins
let cod_pbij : type e i r. (e, i, r) pbij -> i D.t = fun (Pbij (_, shuf)) -> out_shuffle shuf
let remaining : type e i r. (e, i, r) pbij -> r D.t = fun (Pbij (_, shuf)) -> left_shuffle shuf

(* An insertion is a partial bijection with zero 'remaining. *)
let pbij_of_ins : type a b c. (a, b, c) insertion -> (a, c, D.zero) pbij =
 fun ins -> Pbij (ins, zero_shuffle (cod_right_ins ins))

type _ pbij_of = Pbij_of : ('evaluation, 'intrinsic, 'remaining) pbij -> 'evaluation pbij_of

(* A partial bijection from a given 'evaluation dimension can be represented by a list of integers and direction strings.  The length of the list is the codomain 'intrinsic.  The integers in the list represent 'shared and the strings represent 'remaining, with their positions in the list giving the shuffle, and the values of the integers specifying where to insert them (into some dimension 'result) to produce 'evaluation. *)
let rec pbij_of_int_strings : type e.
    e D.t -> [ `Int of int | `Str of string ] list -> e pbij_of option =
 fun e strs ->
  match strs with
  | [] -> Some (Pbij_of (Pbij (ins_zero e, Zero)))
  | `Int n :: strs -> (
      match (e, N.index_of_int e (n + 1)) with
      | Nat (Suc e), Some ix -> (
          let e = N.Nat e in
          let strs =
            List.map
              (function
                | `Int i ->
                    if i < n then `Int i
                    else if i > n then `Int (i - 1)
                    else raise (Invalid_argument "pbij_of_int_strings")
                | `Str str -> `Str str)
              strs in
          match pbij_of_int_strings e strs with
          | Some (Pbij_of (Pbij (ins, shuf))) ->
              Some (Pbij_of (Pbij (Suc (ins, N.insert_of_index ix), Right shuf)))
          | None -> None)
      | Nat Zero, Some _ -> .
      | _, None -> None)
  | `Str str :: strs when str = Endpoints.refl_string () -> (
      match pbij_of_int_strings e strs with
      | Some (Pbij_of (Pbij (ins, shuf))) -> Some (Pbij_of (Pbij (ins, Left shuf)))
      | None -> None)
  | `Str _ :: _ -> None

let pbij_of_strings : type e. e D.t -> string list -> e pbij_of option =
 fun e strs ->
  pbij_of_int_strings e
    (List.map
       (fun x ->
         match int_of_string_opt x with
         | Some i -> `Int i
         | None -> `Str x)
       strs)

let rec int_strings_of_pbij : type n i r. (n, i, r) pbij -> [ `Int of int | `Str of string ] list =
 fun (Pbij (ins, shuf)) ->
  match shuf with
  | Zero -> []
  | Left shuf -> `Str (Endpoints.refl_string ()) :: int_strings_of_pbij (Pbij (ins, shuf))
  | Right shuf ->
      let (Suc (ins, ix)) = ins in
      let x = N.int_of_index (N.index_of_insert ix) + 1 in
      `Int x
      :: List.map
           (function
             | `Int i -> if i >= x then `Int (i + 1) else `Int i
             | `Str str -> `Str str)
           (int_strings_of_pbij (Pbij (ins, shuf)))

let strings_of_pbij : type n i r. (n, i, r) pbij -> string list =
 fun pbij ->
  List.map
    (function
      | `Str s -> s
      | `Int i -> string_of_int i)
    (int_strings_of_pbij pbij)

(* When representing that as a single string, we run all the integers and direction strings together with a single prefix . if the integers are all one-digit, otherwise we separate them by .s with a prefix .. *)
let string_of_pbij : type n i r. (n, i, r) pbij -> string =
 fun pbij ->
  let strs = strings_of_pbij pbij in
  if List.is_empty strs then ""
  else if List.fold_right (fun s m -> max (String.length s) m) strs 0 > 1 then
    ".." ^ String.concat "." strs
  else "." ^ String.concat "" strs

type (_, _) pbij_between =
  | Pbij_between :
      ('evaluation, 'intrinsic, 'remaining) pbij
      -> ('evaluation, 'intrinsic) pbij_between

(* Enumerate all the partial bijections from a given 'evaluation to a given 'intrinsic. *)
let all_pbij_between : type evaluation intrinsic.
    evaluation D.t -> intrinsic D.t -> (evaluation, intrinsic) pbij_between Seq.t =
 fun evaluation intrinsic ->
  let open Monad.Ops (Monad.Seq) in
  let* (Ins_of ins) = all_ins_of evaluation in
  let* (Of_right shuf) = all_shuffles_right (cod_right_ins ins) intrinsic in
  return (Pbij_between (Pbij (ins, shuf)))

(* A partial bijection can be composed with a degeneracy on the evaluation dimension to produce another partial bijection, with an induced degeneracy on the results.  Note that the first two outputs form a partial bijection. *)

type (_, _, _) deg_comp_ins =
  | Deg_comp_ins :
      ('evaluation, 'result, 'shared) insertion
      * ('remaining, 'shared, 'intrinsic) shuffle
      * ('old_result, 'result) deg
      -> ('evaluation, 'old_result, 'intrinsic) deg_comp_ins

let rec deg_comp_ins : type m n i res.
    (m, n) deg -> (m, res, i) insertion -> (n, res, i) deg_comp_ins =
 fun deg ins ->
  match ins with
  | Zero _ -> Deg_comp_ins (Zero (cod_deg deg), Zero, deg)
  | Suc (ins, i) -> (
      match deg_coresidual deg i with
      | Coresidual_zero deg ->
          let (Deg_comp_ins (ins, shuf, s)) = deg_comp_ins deg ins in
          Deg_comp_ins (ins, Left shuf, s)
      | Coresidual_suc (deg, j) ->
          let (Deg_comp_ins (ins, shuf, s)) = deg_comp_ins deg ins in
          Deg_comp_ins (Suc (ins, j), Right shuf, s))

(* A partial bijection can be composed with a degeneracy on the evaluation dimension to produce another partial bijection, with an induced degeneracy on the results. *)

type (_, _, _, _) deg_comp_pbij =
  | Deg_comp_pbij :
      ('evaluation, 'result, 'shared) insertion
      * ('remaining, 'shared, 'intrinsic) shuffle
      * ('old_result, 'result) deg
      * (('remaining, D.zero) Eq.t -> ('r, D.zero) Eq.t)
      -> ('evaluation, 'old_result, 'intrinsic, 'r) deg_comp_pbij

let rec deg_comp_pbij : type m n i res rem sh.
    (m, n) deg -> (m, res, sh) insertion -> (rem, sh, i) shuffle -> (n, res, i, rem) deg_comp_pbij =
 fun deg ins shuf ->
  match shuf with
  | Zero ->
      let (Zero _) = ins in
      Deg_comp_pbij (ins_zero (cod_deg deg), Zero, deg, fun _ -> Eq)
  | Left shuf ->
      let (Deg_comp_pbij (ins, shuf, s, _)) = deg_comp_pbij deg ins shuf in
      Deg_comp_pbij
        ( ins,
          Left shuf,
          s,
          function
          | _ -> . )
  | Right shuf -> (
      let (Suc (ins, i)) = ins in
      match deg_coresidual deg i with
      | Coresidual_zero deg ->
          let (Deg_comp_pbij (ins, shuf, s, _)) = deg_comp_pbij deg ins shuf in
          Deg_comp_pbij
            ( ins,
              Left shuf,
              s,
              function
              | _ -> . )
      | Coresidual_suc (deg, j) ->
          let (Deg_comp_pbij (ins, shuf, s, ifzero)) = deg_comp_pbij deg ins shuf in
          Deg_comp_pbij (Suc (ins, j), Right shuf, s, ifzero))

(* This is like deg_comp_pbij (for the insertion only, so far), but for adding a constant on the left rather than acting by an arbitrary degeneracy (for evaluation rather that acting).  This allows it to return more detailed information.  The dimension 'r (new remaining) is the piece of 'i (intrinsic) that lands in 'm (new added dimension on the left), while 'h (new shared) is the part that lands in 'n, and 't is the part of 'm that doesn't come from 'r.  Note that the first two outputs together form an ('n, 'i, 'r) pbij; that's why this is in this file, even though it doesn't refer explicitly to pbij.  *)

type (_, _, _, _) unplus_ins =
  | Unplus_ins :
      ('n, 's, 'h) insertion
      * ('r, 'h, 'i) shuffle
      * ('m, 't, 'r) insertion
      * ('t, 'n, 'tn) D.plus
      * ('tn, 'olds, 'h) insertion
      -> ('m, 'n, 'olds, 'i) unplus_ins

let rec unplus_ins : type m n mn s i.
    m D.t -> (m, n, mn) D.plus -> (mn, s, i) insertion -> (m, n, s, i) unplus_ins =
 fun m mn ins ->
  match ins with
  | Zero _ ->
      (* i=0, r=0, h=0, t=m, tn=mn, s=n *)
      Unplus_ins (Zero (D.plus_right mn), Zero, Zero m, mn, Zero (D.plus_out m mn))
  | Suc (ins', x) -> (
      match D.insert_in_plus mn x with
      | Left (x, mn') ->
          let (Unplus_ins (nsh, rhi, mtr, tn, tnsh)) = unplus_ins (D.insert_in m x) mn' ins' in
          (* right-increment i and r, middle-increment m, keep s and h the same *)
          Unplus_ins (nsh, Left rhi, Suc (mtr, x), tn, tnsh)
      | Right (x, mn') ->
          let (Unplus_ins (nsh, rhi, mtr, tn, tnsh)) = unplus_ins m mn' ins' in
          (* right-increment i and h and s, middle-increment n, keep m and r the same *)
          let (Plus tn') = D.plus (D.plus_right mn) in
          Unplus_ins (Suc (nsh, x), Right rhi, mtr, tn', Suc (tnsh, D.plus_insert tn tn' x)))

type (_, _, _, _, _, _) unplus_pbij =
  | Unplus_pbij :
      ('n, 'news, 'newh) insertion
      * ('r, 'newh, 'i) shuffle
      * ('oldr, 'newr, 'r) shuffle
      * ('m, 't, 'newr) insertion
      * ('t, 'n, 'tn) D.plus
      * ('tn, 'olds, 'newh) insertion
      -> ('m, 'n, 'olds, 'oldr, 'h, 'i) unplus_pbij

let unplus_pbij : type m n mn s i r h.
    m D.t ->
    (m, n, mn) D.plus ->
    (mn, s, h) insertion ->
    (r, h, i) shuffle ->
    (m, n, s, r, h, i) unplus_pbij =
 fun m mn ins shuf ->
  let (Unplus_ins (nsh, rhi, mtr, tn, tnsh)) = unplus_ins m mn ins in
  let (Comp_shuffle_right (rr, rhi)) = comp_shuffle_right rhi shuf in
  Unplus_pbij (nsh, rhi, rr, mtr, tn, tnsh)

(* Convert a pbij to an insertion by increasing the evaluation dimension on the left to include the remaining dimension. *)
let rec ins_plus_of_pbij : type n s h r i rn.
    (n, s, h) insertion -> (r, h, i) shuffle -> (r, n, rn) D.plus -> (rn, s, i) insertion =
 fun ins shuf rn ->
  match shuf with
  | Zero ->
      let Eq = D.plus_uniq rn (D.zero_plus (dom_ins ins)) in
      ins
  | Right shuf' ->
      let (Suc (ins', x)) = ins in
      let (Plus rn') = D.plus (D.insert_in (dom_ins ins) x) in
      Suc (ins_plus_of_pbij ins' shuf' rn', D.plus_insert rn' rn x)
  | Left shuf' ->
      let (Insert_plus (rn', x)) = D.insert_plus Now rn in
      Suc (ins_plus_of_pbij ins shuf' rn', x)

(* Intrinsically well-typed maps with partial bijections as keys.  Each map has a fixed 'evaluation dimension and 'intrinsic dimension, but the 'result, 'shared, and 'remaining dimensions vary with the keys and values.  The values are parametrized by the 'remaining dimension as well as by an extra parameter that the map depends on; hence the whole notion of map is a functor parametrized by a Fam2.

   The definition of the map type involves itself recursively inside a Tuple, so we need a recursive module to tie that knot.  Recursive functors are not really implemented (in general they give "unsafe" errors), but there seems to be an exception that allows them as long as the recursive module call is never named or opened, though it can occur inline in a type definition (but not a function definition, since inline functor applications cannot appear in code).  Thus, it works to first define a recursive functor for just the necessary types and modules, and then another (non-recursive) functor that includes it and defines the operations. *)

module rec Internal_Pbijmap : functor (F : Fam2) -> sig
  module Param : sig
    type (_, _) t =
      | Wrap :
          ('evaluation, 'intrinsic, 'r, 'v) Internal_Pbijmap(F).gt
          -> ('evaluation, ('intrinsic * 'r) * 'v) t
  end

  module Tup : module type of Tuple.Make (Param)

  type (_, _, _, _) gt =
    | Zero : ('r, 'v) F.t -> ('evaluation, D.zero, 'r, 'v) gt
    | Suc : {
        left : ('evaluation, 'intrinsic, 'r D.suc, 'v) gt;
        right : ('evaluation, ('intrinsic * 'r) * 'v) Tup.t;
      }
        -> ('evaluation, 'intrinsic D.suc, 'r, 'v) gt

  type ('evaluation, 'intrinsic, 'v) t = ('evaluation, 'intrinsic, D.zero, 'v) gt * 'evaluation D.t
end =
functor
  (F : Fam2)
  ->
  struct
    module Param = struct
      type (_, _) t =
        | Wrap :
            ('evaluation, 'intrinsic, 'r, 'v) Internal_Pbijmap(F).gt
            -> ('evaluation, ('intrinsic * 'r) * 'v) t
    end

    module Tup = Tuple.Make (Param)

    (* An element of ('evaluation, 'intrinsic, 'v) t is an intrinsically well-typed map that associates to every partial bijection between 'evaluation and 'intrinsic, with remaining dimension 'r, an element of ('r, 'v) F.t.  As with cubes, we define this in terms of a more general type ('evaluation, 'intrinsic, 's, 'v) gt which associates to every such partial bijection an element of ('r+'s, 'v) F.t. *)
    type (_, _, _, _) gt =
      (* The definition is by induction on the intrinsic dimension.  If that's zero, then we are at a leaf and we just store something of the appropriate type. *)
      | Zero : ('r, 'v) F.t -> ('evaluation, D.zero, 'r, 'v) gt
      (* If it's a successor, then the shuffle acting on that last element either sends it into the remaining dimensions or the shared ones.  Thus, we store one subtree with incremented remaining dimension, and a tuple of subtrees with the same remaining dimension, indexed by where the new shared element ends up in the evaluation dimension (and with the image removed from the evaluation dimension; the intrinsically well-typed map Tuple takes care of that). *)
      | Suc : {
          left : ('evaluation, 'intrinsic, 'r D.suc, 'v) gt;
          right : ('evaluation, ('intrinsic * 'r) * 'v) Tup.t;
        }
          -> ('evaluation, 'intrinsic D.suc, 'r, 'v) gt

    type ('evaluation, 'intrinsic, 'v) t =
      ('evaluation, 'intrinsic, D.zero, 'v) gt * 'evaluation D.t
  end

module Pbijmap (F : Fam2) = struct
  include Internal_Pbijmap (F)

  (* The intrinsic dimension is automatically a dimension. *)
  let rec gintrinsic : type evaluation intrinsic r v.
      (evaluation, intrinsic, r, v) gt -> intrinsic D.t = function
    | Zero _ -> D.zero
    | Suc { left; _ } -> D.suc (gintrinsic left)

  let intrinsic : type evaluation intrinsic v. (evaluation, intrinsic, v) t -> intrinsic D.t =
   fun (ms, _) -> gintrinsic ms

  type (_, _) wrapped = Wrap : ('evaluation, 'intrinsic, 'v) t -> ('evaluation, 'v) wrapped

  let rec gfind : type evaluation intrinsic r1 r2 r v.
      (evaluation, intrinsic, r2) pbij ->
      (evaluation, intrinsic, r1, v) gt ->
      (r1, r2, r) D.plus ->
      (r, v) F.t =
   fun p m r12 ->
    match (p, m) with
    | Pbij (Zero _, Zero), Zero v ->
        let Zero = r12 in
        v
    | Pbij (ins, Left shuf), Suc m -> gfind (Pbij (ins, shuf)) m.left (D.suc_plus r12)
    | Pbij (Suc (ins, i), Right shuf), Suc m ->
        let (Wrap m) = Tup.find i m.right in
        gfind (Pbij (ins, shuf)) m r12

  let find : type evaluation intrinsic remaining v.
      (evaluation, intrinsic, remaining) pbij -> (evaluation, intrinsic, v) t -> (remaining, v) F.t
      =
   fun p (m, _) -> gfind p m (D.zero_plus (remaining p))

  let rec gset : type evaluation intrinsic r1 r2 r v.
      (evaluation, intrinsic, r2) pbij ->
      (r, v) F.t ->
      (evaluation, intrinsic, r1, v) gt ->
      (r1, r2, r) D.plus ->
      (evaluation, intrinsic, r1, v) gt =
   fun p v m r12 ->
    match (p, m) with
    | Pbij (Zero _, Zero), Zero _ ->
        let Zero = r12 in
        Zero v
    | Pbij (ins, Left shuf), Suc m ->
        Suc { m with left = gset (Pbij (ins, shuf)) v m.left (D.suc_plus r12) }
    | Pbij (Suc (ins, i), Right shuf), Suc m ->
        Suc
          {
            m with
            right = Tup.update i (fun (Wrap m) -> Wrap (gset (Pbij (ins, shuf)) v m r12)) m.right;
          }

  let set : type evaluation intrinsic remaining v.
      (evaluation, intrinsic, remaining) pbij ->
      (remaining, v) F.t ->
      (evaluation, intrinsic, v) t ->
      (evaluation, intrinsic, v) t =
   fun p v (m, e) -> (gset p v m (D.zero_plus (remaining p)), e)

  let find_singleton : type evaluation intrinsic v.
      (evaluation, intrinsic, v) t -> (D.zero, v) F.t option = function
    | Zero v, _ -> Some v
    | Suc _, _ -> None

  type ('evaluation, 'intrinsic, 'r1, 'v) gbuilder = {
    remaining : 'r1 D.t;
    build : 'r2 'r. ('evaluation, 'intrinsic, 'r2) pbij -> ('r1, 'r2, 'r) D.plus -> ('r, 'v) F.t;
  }

  let rec gbuild : type evaluation intrinsic remaining v.
      evaluation D.t ->
      intrinsic D.t ->
      (evaluation, intrinsic, remaining, v) gbuilder ->
      (evaluation, intrinsic, remaining, v) gt =
   fun evaluation intrinsic f ->
    match intrinsic with
    | Nat Zero -> Zero (f.build (Pbij (ins_zero evaluation, Zero)) (D.plus_zero f.remaining))
    | Nat (Suc intrinsic) ->
        Suc
          {
            left =
              gbuild evaluation (Nat intrinsic)
                {
                  remaining = D.suc f.remaining;
                  build =
                    (fun (Pbij (ins, shuf)) r12 -> f.build (Pbij (ins, Left shuf)) (D.plus_suc r12));
                };
            right =
              Tup.build evaluation
                {
                  build =
                    (fun i ->
                      Wrap
                        (gbuild (D.insert_in evaluation i) (Nat intrinsic)
                           {
                             f with
                             build =
                               (fun (Pbij (ins, shuf)) r12 ->
                                 f.build (Pbij (Suc (ins, i), Right shuf)) r12);
                           }));
                };
          }

  type ('evaluation, 'intrinsic, 'v) builder = {
    build : 'r. ('evaluation, 'intrinsic, 'r) pbij -> ('r, 'v) F.t;
  }

  let gbuilder_of_builder : type evaluation intrinsic v r2 r.
      (evaluation, intrinsic, v) builder ->
      (evaluation, intrinsic, r2) pbij ->
      (D.zero, r2, r) D.plus ->
      (r, v) F.t =
   fun f p r12 ->
    let Eq = D.plus_uniq r12 (D.zero_plus (remaining p)) in
    f.build p

  let build : type evaluation intrinsic v.
      evaluation D.t ->
      intrinsic D.t ->
      (evaluation, intrinsic, v) builder ->
      (evaluation, intrinsic, v) t =
   fun evaluation intrinsic f ->
    ( gbuild evaluation intrinsic
        { remaining = D.zero; build = (fun p r12 -> gbuilder_of_builder f p r12) },
      evaluation )

  let singleton : type evaluation v. evaluation D.t -> (D.zero, v) F.t -> (evaluation, D.zero, v) t
      =
   fun e v -> (Zero v, e)

  (* Generic traversal *)

  module Times = struct
    type (_, _, _) t = Times : ('p, 'x, 'p * 'x) t
    type (_, _) exists = Exists : ('p, 'a, 'b) t -> ('p, 'a) exists

    let exists : ('p, 'a) exists = Exists Times
  end

  module MapTimes = Tlist.Map (Times)

  module Heter = struct
    type (_, _) hft =
      | [] : ('a, nil) hft
      | ( :: ) : ('a, 'v) F.t * ('a, 'vs) hft -> ('a, ('v, 'vs) cons) hft

    type (_, _, _, _) hgt =
      | [] : ('e, 'i, 'r, nil) hgt
      | ( :: ) : ('e, 'i, 'r, 'v) gt * ('e, 'i, 'r, 'vs) hgt -> ('e, 'i, 'r, ('v, 'vs) cons) hgt

    let rec zero : type r e vs. (r, vs) hft -> (e, D.zero, r, vs) hgt = function
      | [] -> []
      | v :: vs -> Zero v :: zero vs

    let rec suc : type e i r vs irvs.
        (e, i, r D.suc, vs) hgt ->
        (i * r, vs, irvs) MapTimes.t ->
        (e, Fwn.zero, irvs) Tup.Heter.hgt ->
        (e, i D.suc, r, vs) hgt =
     fun ls irvs rs ->
      match (ls, irvs, rs) with
      | [], [], [] -> []
      | left :: ls, Times :: irvs, right :: rs -> Suc { left; right } :: suc ls irvs rs

    let rec zeros : type e r vs. (e, D.zero, r, vs) hgt -> (r, vs) hft = function
      | [] -> []
      | Zero v :: ms -> v :: zeros ms

    let rec left : type e i r vs. (e, i D.suc, r, vs) hgt -> (e, i, r D.suc, vs) hgt = function
      | [] -> []
      | Suc { left = l; _ } :: ms -> l :: left ms

    let rec right : type e i r vs irvs.
        (e, i D.suc, r, vs) hgt -> (i * r, vs, irvs) MapTimes.t -> (e, Fwn.zero, irvs) Tup.Heter.hgt
        =
     fun ms irvs ->
      match (ms, irvs) with
      | [], [] -> []
      | Suc { right = r; _ } :: ms, Times :: irvs -> r :: right ms irvs

    let rec wrap : type e i r vs irvs.
        (e, i, r, vs) hgt -> (i * r, vs, irvs) MapTimes.t -> (e, irvs) Tup.Heter.hft =
     fun ms irvs ->
      match (ms, irvs) with
      | [], [] -> []
      | m :: ms, Times :: irvs -> Wrap m :: wrap ms irvs

    let rec unwrap : type e i r vs irvs.
        (e, irvs) Tup.Heter.hft -> (i * r, vs, irvs) MapTimes.t -> (e, i, r, vs) hgt =
     fun ms irvs ->
      match (ms, irvs) with
      | [], [] -> []
      | Wrap m :: ms, Times :: irvs -> m :: unwrap ms irvs

    let rec params : type e i r vs. (e, i, r, vs) hgt -> vs Tlist.t = function
      | [] -> Nil
      | _ :: vs -> Cons (params vs)

    type (_, _, _) ht =
      | [] : ('e, 'i, nil) ht
      | ( :: ) : ('e, 'i, 'v) t * ('e, 'i, 'vs) ht -> ('e, 'i, ('v, 'vs) cons) ht

    let rec hgt_of_ht : type e i vs. (e, i, vs) ht -> (e, i, D.zero, vs) hgt = function
      | [] -> []
      | (m, _) :: ms -> m :: hgt_of_ht ms

    let rec ht_of_hgt : type e i vs. (e, i, D.zero, vs) hgt -> e D.t -> (e, i, vs) ht =
     fun ms e ->
      match ms with
      | [] -> []
      | m :: ms -> (m, e) :: ht_of_hgt ms e
  end

  module Infix = struct
    let hnil : type n. (n, nil) Heter.hft = []

    let ( @: ) : type n x xs. (n, x) F.t -> (n, xs) Heter.hft -> (n, (x, xs) cons) Heter.hft =
     fun x xs -> x :: xs
  end

  open Infix

  module Applicatic (M : Applicative.Plain) = struct
    open Applicative.Ops (M)

    type ('evaluation, 'intrinsic, 'r1, 'vs, 'ws) gpmapperM = {
      remaining : 'r1 D.t;
      map :
        'r2 'r.
        ('evaluation, 'intrinsic, 'r2) pbij ->
        ('r1, 'r2, 'r) D.plus ->
        ('r, 'vs) Heter.hft ->
        ('r, 'ws) Heter.hft M.t;
    }

    let rec gpmapM : type evaluation intrinsic remaining v vs ws.
        evaluation D.t ->
        (evaluation, intrinsic, remaining, (v, vs) cons, ws) gpmapperM ->
        (evaluation, intrinsic, remaining, (v, vs) cons) Heter.hgt ->
        ws Tlist.t ->
        (evaluation, intrinsic, remaining, ws) Heter.hgt M.t =
     fun evaluation f ms ws ->
      match ms with
      | Zero _ :: _ ->
          let+ res =
            f.map (Pbij (ins_zero evaluation, Zero)) (D.plus_zero f.remaining) (Heter.zeros ms)
          in
          Heter.zero res
      | Suc _ :: _ ->
          let module T = Tup.Applicatic (M) in
          let (Exists_cons irvs) = MapTimes.exists_cons (Heter.params ms) in
          let (Exists irws) = MapTimes.exists ws in
          let+ lefts =
            gpmapM evaluation
              {
                remaining = D.suc f.remaining;
                map =
                  (fun (Pbij (ins, shuf)) r12 v -> f.map (Pbij (ins, Left shuf)) (D.plus_suc r12) v);
              }
              (Heter.left ms) ws
          and+ rights =
            T.pmapM
              {
                map =
                  (fun i x ->
                    let+ res =
                      gpmapM (D.insert_in evaluation i)
                        {
                          f with
                          map =
                            (fun (Pbij (ins, shuf)) r12 v ->
                              f.map (Pbij (Suc (ins, i), Right shuf)) r12 v);
                        }
                        (Heter.unwrap x irvs) ws in
                    Heter.wrap res irws);
              }
              (Heter.right ms irvs) (MapTimes.cod irws) in
          Heter.suc lefts irws rights

    type ('evaluation, 'intrinsic, 'vs, 'ws) pmapperM = {
      map : 'r. ('evaluation, 'intrinsic, 'r) pbij -> ('r, 'vs) Heter.hft -> ('r, 'ws) Heter.hft M.t;
    }

    let gpmapper_of_pmapper : type evaluation intrinsic vs ws r2 r.
        (evaluation, intrinsic, vs, ws) pmapperM ->
        (evaluation, intrinsic, r2) pbij ->
        (D.zero, r2, r) D.plus ->
        (r, vs) Heter.hft ->
        (r, ws) Heter.hft M.t =
     fun f p r12 ->
      let Eq = D.plus_uniq r12 (D.zero_plus (remaining p)) in
      f.map p

    let pmapM : type evaluation intrinsic v vs ws.
        (evaluation, intrinsic, (v, vs) cons, ws) pmapperM ->
        (evaluation, intrinsic, (v, vs) cons) Heter.ht ->
        ws Tlist.t ->
        (evaluation, intrinsic, ws) Heter.ht M.t =
     fun f ((_, e) :: _ as ms) ws ->
      let+ res =
        gpmapM e
          { remaining = D.zero; map = (fun p r12 -> gpmapper_of_pmapper f p r12) }
          (Heter.hgt_of_ht ms) ws in
      Heter.ht_of_hgt res e

    type ('evaluation, 'intrinsic, 'vs, 'w) mmapperM = {
      map : 'r. ('evaluation, 'intrinsic, 'r) pbij -> ('r, 'vs) Heter.hft -> ('r, 'w) F.t M.t;
    }

    let mmapM f xs =
      let+ [ ys ] =
        pmapM
          {
            map =
              (fun i x ->
                let+ y = f.map i x in
                y @: hnil);
          }
          xs (Cons Nil) in
      ys

    type ('evaluation, 'intrinsic, 'vs) miteratorM = {
      it : 'r. ('evaluation, 'intrinsic, 'r) pbij -> ('r, 'vs) Heter.hft -> unit M.t;
    }

    let miterM f xs =
      let+ [] =
        pmapM
          {
            map =
              (fun i x ->
                let+ () = f.it i x in
                hnil);
          }
          xs Nil in
      ()
  end

  module Monadic (M : Monad.Plain) = struct
    module A = Applicative.OfMonad (M)
    include Applicatic (A)
  end

  module IdM = Monadic (Monad.Identity)

  let pmap f xs qs = IdM.pmapM f xs qs
  let mmap f xs = IdM.mmapM f xs
  let miter f xs = IdM.miterM f xs
end

module PbijmapOf = Pbijmap (struct
  type ('a, 'b) t = 'b
end)
