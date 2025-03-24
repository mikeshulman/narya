open Util
open Tlist
open Signatures
open Sface
open Tface
open Deg
open Perm

(* An element of ('a, 'b, 'c) insertion is an insertion of 'c into 'b: a permutation from a to b+c that maintains the relative order of 'b.  *)
(* TODO: Should an insertion be parametrized by b+c as well? *)
type (_, _, _) insertion =
  | Zero : 'a D.t -> ('a, 'a, D.zero) insertion
  | Suc : ('a, 'b, 'c) insertion * ('a, 'asuc) D.insert -> ('asuc, 'b, 'c D.suc) insertion

let ins_zero : type a. a D.t -> (a, a, D.zero) insertion = fun a -> Zero a

let rec zero_ins : type a. a D.t -> (a, D.zero, a) insertion =
 fun a ->
  match a with
  | Nat Zero -> Zero a
  | Nat (Suc a) ->
      let ins = zero_ins (Nat a) in
      Suc (ins, Now)

let rec id_ins : type a b ab. a D.t -> (a, b, ab) D.plus -> (ab, a, b) insertion =
 fun a b ->
  match b with
  | Zero -> Zero a
  | Suc b ->
      let ins = id_ins a b in
      Suc (ins, Now)

let rec dom_ins : type a b c. (a, b, c) insertion -> a D.t = function
  | Zero a -> a
  | Suc (ins, i) -> N.insert_out (dom_ins ins) i

let rec cod_left_ins : type a b c. (a, b, c) insertion -> b D.t = function
  | Zero a -> a
  | Suc (ins, _) -> cod_left_ins ins

let rec cod_right_ins : type a b c. (a, b, c) insertion -> c D.t = function
  | Zero _ -> D.zero
  | Suc (ins, _) -> D.suc (cod_right_ins ins)

let rec equal_ins : type a1 b1 c1 a2 b2 c2.
    (a1, b1, c1) insertion -> (a2, b2, c2) insertion -> unit option =
 fun i1 i2 ->
  match (i1, i2) with
  | Zero a1, Zero a2 -> (
      match D.compare a1 a2 with
      | Eq -> Some ()
      | Neq -> None)
  | Suc (i1, x1), Suc (i2, x2) ->
      let open Monad.Ops (Monad.Maybe) in
      let* () = N.insert_equiv x1 x2 in
      equal_ins i1 i2
  | _ -> None

let rec plus_ins : type a b c d ab ac.
    a D.t -> (a, b, ab) D.plus -> (a, c, ac) D.plus -> (b, c, d) insertion -> (ab, ac, d) insertion
    =
 fun a ab ac ins ->
  match ins with
  | Zero _ ->
      let Eq = D.plus_uniq ab ac in
      Zero (D.plus_out a ab)
  | Suc (ins, i) ->
      let (Plus ab') = D.plus (D.insert_in (D.plus_right ab) i) in
      Suc (plus_ins a ab' ac ins, D.plus_insert ab' ab i)

(* If a+b=ab, then there is an identity permutation that inserts b on the right of a. *)
let rec ins_of_plus : type a b ab. a D.t -> (a, b, ab) D.plus -> (ab, a, b) insertion =
 fun a ab ->
  match ab with
  | Zero -> Zero a
  | Suc ab -> Suc (ins_of_plus a ab, Now)

(* An insertion induces a degeneracy, which is in fact a permutation. *)
let rec deg_of_ins_plus : type a b c bc. (a, b, c) insertion -> (b, c, bc) D.plus -> (a, bc) deg =
 fun i bc ->
  match (i, bc) with
  | Zero a, Zero -> id_deg a
  | Suc (i, e), Suc bc -> Suc (deg_of_ins_plus i bc, e)

let deg_of_ins : type a b c. (a, b, c) insertion -> a deg_to =
 fun ins ->
  let (Plus bc) = D.plus (cod_right_ins ins) in
  To (deg_of_ins_plus ins bc)

let rec perm_of_ins_plus : type a b c bc. (a, b, c) insertion -> (b, c, bc) D.plus -> (a, bc) perm =
 fun i bc ->
  match (i, bc) with
  | Zero a, Zero -> id_perm a
  | Suc (i, e), Suc bc -> Suc (perm_of_ins_plus i bc, e)

let perm_of_ins : type a b c. (a, b, c) insertion -> a perm_to =
 fun ins ->
  let (Plus bc) = D.plus (cod_right_ins ins) in
  Perm_to (perm_of_ins_plus ins bc)

let rec is_id_ins : type a b c. (a, b, c) insertion -> (b, c, a) D.plus option = function
  | Zero _ -> Some Zero
  | Suc (ins, Now) -> (
      match is_id_ins ins with
      | Some bc -> Some (Suc bc)
      | None -> None)
  | Suc (_, Later _) -> None

let deg_of_plus_of_ins : type a b c. (a, b, c) insertion -> b deg_of_plus =
 fun ins ->
  let (Plus bc) = D.plus (cod_right_ins ins) in
  Of (bc, deg_of_ins_plus ins bc)

(* Any degeneracy with a decomposition of its codomain factors as an insertion followed by a whiskered degeneracy.  The whiskered degeneracy does all the permutation of 'a and inserting degenerate dimensions into it, and then the insertion puts 'c back in the corresponding places. *)

type (_, _, _) insfact = Insfact : ('a, 'b) deg * ('ac, 'a, 'c) insertion -> ('ac, 'b, 'c) insfact

let rec insfact : type ac b c bc. (ac, bc) deg -> (b, c, bc) D.plus -> (ac, b, c) insfact =
 fun s bc ->
  match bc with
  | Zero -> Insfact (s, Zero (dom_deg s))
  | Suc bc ->
      let (Suc (s, e)) = s in
      let (Insfact (s, i)) = insfact s bc in
      Insfact (s, Suc (i, e))

(* In particular, since an insertion induces a degeneracy (a permutation) with a decomposition of its codomain, if we compose a degeneracy followed by an insertion, the result factors in the above way as an insertion followed by a whiskered degeneracy.  In the stated type of this operation, we also allow the given degeneracy to have any domain and codomain, and do the composition by extending both with identities as in comp_deg_extending. *)
type (_, _, _) insfact_comp =
  | Insfact_comp :
      ('m, 'n) deg * ('ml, 'm, 'l) insertion * ('k, 'j, 'l) D.plus * ('a, 'i, 'ml) D.plus
      -> ('n, 'k, 'a) insfact_comp

let insfact_comp : type n k nk a b. (nk, n, k) insertion -> (a, b) deg -> (n, k, a) insfact_comp =
 fun ins s ->
  let (Plus nk) = D.plus (cod_right_ins ins) in
  let s' = deg_of_ins_plus ins nk in
  let (DegExt (ai, nk_d, s's)) = comp_deg_extending s' s in
  let (Plus kd) = D.plus (D.plus_right nk_d) in
  let n_kd = D.plus_assocr nk kd nk_d in
  let (Insfact (fa, new_ins)) = insfact s's n_kd in
  Insfact_comp (fa, new_ins, kd, ai)

(* A degeneracy of the left codomain of an insertion can be extended to a degeneracy of its domain, completing a commutative square with a larger insertion. *)

type (_, _, _) deg_lift_ins =
  | Deg_lift_ins : ('mk, 'm, 'k) insertion * ('mk, 'nk) deg -> ('m, 'k, 'nk) deg_lift_ins

let rec deg_lift_ins : type n k nk m. (m, n) deg -> (nk, n, k) insertion -> (m, k, nk) deg_lift_ins
    =
 fun s0 ins0 ->
  match ins0 with
  | Zero _ -> Deg_lift_ins (Zero (dom_deg s0), s0)
  | Suc (ins1, i1) ->
      let (Deg_lift_ins (ins2, s1)) = deg_lift_ins s0 ins1 in
      let (Insert_deg (j2, s2)) = insert_deg s1 i1 in
      Deg_lift_ins (Suc (ins2, j2), s2)

(* And similarly for a strict face of the left codomain. *)

type (_, _, _) sface_lift_ins =
  | Sface_lift_ins : ('mk, 'm, 'k) insertion * ('mk, 'nk) sface -> ('m, 'k, 'nk) sface_lift_ins

let rec sface_lift_ins : type n k nk m.
    (m, n) sface -> (nk, n, k) insertion -> (m, k, nk) sface_lift_ins =
 fun fa0 ins0 ->
  match ins0 with
  | Zero _ -> Sface_lift_ins (Zero (dom_sface fa0), fa0)
  | Suc (ins1, i1) ->
      let (Sface_lift_ins (ins2, fa1)) = sface_lift_ins fa0 ins1 in
      let (Insert_sface (j2, fa2)) = insert_sface fa1 i1 in
      Sface_lift_ins (Suc (ins2, j2), fa2)

(* Or a proper face *)

type (_, _, _) pface_lift_ins =
  | Pface_lift_ins : ('mk, 'm, 'k) insertion * ('mk, 'nk) pface -> ('m, 'k, 'nk) pface_lift_ins

let rec pface_lift_ins : type n k nk m.
    (m, n) pface -> (nk, n, k) insertion -> (m, k, nk) pface_lift_ins =
 fun fa0 ins0 ->
  match ins0 with
  | Zero _ -> Pface_lift_ins (Zero (dom_tface fa0), fa0)
  | Suc (ins1, i1) ->
      let (Pface_lift_ins (ins2, fa1)) = pface_lift_ins fa0 ins1 in
      let (Insert_pface (j2, fa2)) = insert_pface fa1 i1 in
      Pface_lift_ins (Suc (ins2, j2), fa2)

(* Construct an insertion from a domain and a list of numbers. *)
type _ ins_of = Ins_of : ('ab, 'a, 'b) insertion -> 'ab ins_of

let rec ins_of_ints : type ab. ab D.t -> int list -> ab ins_of option =
 fun ab ns ->
  match ns with
  | [] -> Some (Ins_of (Zero ab))
  | n :: ns -> (
      match (ab, N.index_of_int ab (n - 1)) with
      | Nat (Suc ab), Some ix -> (
          let ab = N.Nat ab in
          try
            let ns =
              List.map
                (fun i ->
                  if i < n then i
                  else if i > n then i - 1
                  else raise (Invalid_argument "ins_of_ints"))
                ns in
            match ins_of_ints ab ns with
            | Some (Ins_of ins) -> Some (Ins_of (Suc (ins, N.insert_of_index ix)))
            | None -> None
          with Invalid_argument _ -> None)
      | Nat Zero, Some _ -> .
      | _, None -> None)

(* Conversely, display an insertion as a list of numbers. *)
let rec ints_of_ins : type ab a b. (ab, a, b) insertion -> int list = function
  | Zero _ -> []
  | Suc (ins, ix) ->
      let x = N.int_of_index (N.index_of_insert ix) + 1 in
      x :: List.map (fun i -> if i >= x then i + 1 else i) (ints_of_ins ins)

let string_of_ins_ints : int list -> string =
 fun ints ->
  let strs = List.map string_of_int ints in
  if List.is_empty strs then ""
  else if List.fold_right (fun s m -> max (String.length s) m) strs 0 > 1 then
    ".." ^ String.concat "." strs
  else "." ^ String.concat "" strs

let string_of_ins : type ab a b. (ab, a, b) insertion -> string =
 fun ins -> string_of_ins_ints (ints_of_ins ins)

type any_ins = Any_ins : ('a, 'b, 'c) insertion -> any_ins

(* List all the insertions with a given total dimension. *)
let rec all_ins_of : type ab. ab D.t -> ab ins_of Seq.t =
 fun ab ->
  let open Monad.Ops (Monad.Seq) in
  Seq.cons (Ins_of (Zero ab))
    (let* (Into ix) = D.all_inserts ab in
     let* (Ins_of ins) = all_ins_of (D.insert_in ab ix) in
     return (Ins_of (Suc (ins, ix))))

(* Intrinsically well-typed maps.  This is basically a simplified version of Pbijmap where the 'remaining is always equal to 0, and hence is not a parameter.  This means we don't actually need the functorial parametrization either, as the simple version InsmapOf is sufficient for all uses.  But we keep it in case later we want to parametrize the values by the 'shared as well.  We do still need a recursive module, since we are still doing a mutual recursion with the functor Tuple. *)

module rec Internal_Insmap : functor (F : Fam) -> sig
  module Param : sig
    type (_, _) t =
      | Wrap :
          ('evaluation, 'intrinsic, 'v) Internal_Insmap(F).t
          -> ('evaluation, 'intrinsic * 'v) t
  end

  module Tup : module type of Tuple.Make (Param)

  type (_, _, _) t =
    | Zero : 'v F.t -> ('evaluation, D.zero, 'v) t
    | Suc : ('evaluation, 'intrinsic * 'v) Tup.t -> ('evaluation, 'intrinsic D.suc, 'v) t
end =
functor
  (F : Fam)
  ->
  struct
    module Param = struct
      type (_, _) t =
        | Wrap :
            ('evaluation, 'intrinsic, 'v) Internal_Insmap(F).t
            -> ('evaluation, 'intrinsic * 'v) t
    end

    module Tup = Tuple.Make (Param)

    (* In the absence of the 'remaining parametrization, we don't need a "gt" version but can go right to the "t". *)
    type (_, _, _) t =
      | Zero : 'v F.t -> ('evaluation, D.zero, 'v) t
      | Suc : ('evaluation, 'intrinsic * 'v) Tup.t -> ('evaluation, 'intrinsic D.suc, 'v) t
  end

module Insmap (F : Fam) = struct
  include Internal_Insmap (F)

  type (_, _) wrapped = Wrap : ('evaluation, 'intrinsic, 'v) t -> ('evaluation, 'v) wrapped

  let rec find : type evaluation intrinsic shared v.
      (evaluation, shared, intrinsic) insertion -> (evaluation, intrinsic, v) t -> v F.t =
   fun p m ->
    match (p, m) with
    | Zero _, Zero v -> v
    | Suc (ins, i), Suc m ->
        let (Wrap m) = Tup.find i m in
        find ins m

  let rec set : type evaluation intrinsic shared v.
      (evaluation, shared, intrinsic) insertion ->
      v F.t ->
      (evaluation, intrinsic, v) t ->
      (evaluation, intrinsic, v) t =
   fun p v m ->
    match (p, m) with
    | Zero _, Zero _ -> Zero v
    | Suc (ins, i), Suc m -> Suc (Tup.update i (fun (Wrap m) -> Wrap (set ins v m)) m)

  let find_singleton : type evaluation intrinsic v. (evaluation, intrinsic, v) t -> v F.t option =
    function
    | Zero v -> Some v
    | Suc _ -> None

  type ('evaluation, 'intrinsic, 'v) builder = {
    build : 'shared. ('evaluation, 'shared, 'intrinsic) insertion -> 'v F.t;
  }

  let rec build : type evaluation intrinsic v.
      evaluation D.t ->
      intrinsic D.t ->
      (evaluation, intrinsic, v) builder ->
      (evaluation, intrinsic, v) t =
   fun evaluation intrinsic f ->
    match intrinsic with
    | Nat Zero -> Zero (f.build (ins_zero evaluation))
    | Nat (Suc intrinsic) ->
        Suc
          (Tup.build evaluation
             {
               build =
                 (fun i ->
                   Wrap
                     (build (D.insert_in evaluation i) (Nat intrinsic)
                        { build = (fun ins -> f.build (Suc (ins, i))) }));
             })

  let singleton : type evaluation v. v F.t -> (evaluation, D.zero, v) t = fun v -> Zero v

  (* Generic traversal *)

  module Times = struct
    type (_, _, _) t = Times : ('p, 'x, 'p * 'x) t
    type (_, _) exists = Exists : ('p, 'a, 'b) t -> ('p, 'a) exists

    let exists : ('p, 'a) exists = Exists Times
  end

  module MapTimes = Tlist.Map (Times)

  module Heter = struct
    type _ hft = [] : nil hft | ( :: ) : 'v F.t * 'vs hft -> ('v, 'vs) cons hft

    type (_, _, _) ht =
      | [] : ('e, 'i, nil) ht
      | ( :: ) : ('e, 'i, 'v) t * ('e, 'i, 'vs) ht -> ('e, 'i, ('v, 'vs) cons) ht

    let rec zero : type e vs. vs hft -> (e, D.zero, vs) ht = function
      | [] -> []
      | v :: vs -> Zero v :: zero vs

    let rec suc : type e i vs irvs.
        (i, vs, irvs) MapTimes.t -> (e, Fwn.zero, irvs) Tup.Heter.hgt -> (e, i D.suc, vs) ht =
     fun irvs rs ->
      match (irvs, rs) with
      | [], [] -> []
      | Times :: irvs, right :: rs -> Suc right :: suc irvs rs

    let rec zeros : type e vs. (e, D.zero, vs) ht -> vs hft = function
      | [] -> []
      | Zero v :: ms -> v :: zeros ms

    let rec right : type e i vs irvs.
        (e, i D.suc, vs) ht -> (i, vs, irvs) MapTimes.t -> (e, Fwn.zero, irvs) Tup.Heter.hgt =
     fun ms irvs ->
      match (ms, irvs) with
      | [], [] -> []
      | Suc r :: ms, Times :: irvs -> r :: right ms irvs

    let rec wrap : type e i vs irvs.
        (e, i, vs) ht -> (i, vs, irvs) MapTimes.t -> (e, irvs) Tup.Heter.hft =
     fun ms irvs ->
      match (ms, irvs) with
      | [], [] -> []
      | m :: ms, Times :: irvs -> Wrap m :: wrap ms irvs

    let rec unwrap : type e i vs irvs.
        (e, irvs) Tup.Heter.hft -> (i, vs, irvs) MapTimes.t -> (e, i, vs) ht =
     fun ms irvs ->
      match (ms, irvs) with
      | [], [] -> []
      | Wrap m :: ms, Times :: irvs -> m :: unwrap ms irvs

    let rec params : type e i vs. (e, i, vs) ht -> vs Tlist.t = function
      | [] -> Nil
      | _ :: vs -> Cons (params vs)
  end

  module Infix = struct
    let hnil : nil Heter.hft = []
    let ( @: ) : type x xs. x F.t -> xs Heter.hft -> (x, xs) cons Heter.hft = fun x xs -> x :: xs
  end

  open Infix

  module Applicatic (M : Applicative.Plain) = struct
    open Applicative.Ops (M)

    type ('evaluation, 'intrinsic, 'vs, 'ws) pmapperM = {
      map :
        'shared. ('evaluation, 'shared, 'intrinsic) insertion -> 'vs Heter.hft -> 'ws Heter.hft M.t;
    }

    let rec pmapM : type evaluation intrinsic v vs ws.
        evaluation D.t ->
        (evaluation, intrinsic, (v, vs) cons, ws) pmapperM ->
        (evaluation, intrinsic, (v, vs) cons) Heter.ht ->
        ws Tlist.t ->
        (evaluation, intrinsic, ws) Heter.ht M.t =
     fun evaluation f ms ws ->
      match ms with
      | Zero _ :: _ ->
          let+ res = f.map (ins_zero evaluation) (Heter.zeros ms) in
          Heter.zero res
      | Suc _ :: _ ->
          let module T = Tup.Applicatic (M) in
          let (Exists_cons irvs) = MapTimes.exists_cons (Heter.params ms) in
          let (Exists irws) = MapTimes.exists ws in
          let+ rights =
            T.pmapM
              {
                map =
                  (fun i x ->
                    let+ res =
                      pmapM (D.insert_in evaluation i)
                        { map = (fun ins v -> f.map (Suc (ins, i)) v) }
                        (Heter.unwrap x irvs) ws in
                    Heter.wrap res irws);
              }
              (Heter.right ms irvs) (MapTimes.cod irws) in
          Heter.suc irws rights

    type ('evaluation, 'intrinsic, 'vs, 'w) mmapperM = {
      map : 'shared. ('evaluation, 'shared, 'intrinsic) insertion -> 'vs Heter.hft -> 'w F.t M.t;
    }

    let mmapM e f xs =
      let+ [ ys ] =
        pmapM e
          {
            map =
              (fun i x ->
                let+ y = f.map i x in
                y @: hnil);
          }
          xs (Cons Nil) in
      ys

    type ('evaluation, 'intrinsic, 'vs) miteratorM = {
      it : 'shared. ('evaluation, 'shared, 'intrinsic) insertion -> 'vs Heter.hft -> unit M.t;
    }

    let miterM e f xs =
      let+ [] =
        pmapM e
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

module InsmapOf = Insmap (struct
  type 'b t = 'b
end)
