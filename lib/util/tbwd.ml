(* Type-level backwards lists *)

open Tlist

type emp = private Dummy_emp
type ('xs, 'x) snoc = private Dummy_ext

module Tbwd = struct
  type _ t = Emp : emp t | Snoc : 'xs t -> ('xs, 'x) snoc t

  (* ('a, 'b, 'n, 'ab) snocs means that 'a is a tbwd (although this isn't enforced -- it could be any type), 'b is a Fwn.t, and 'ab is the result of adding 'b copies of the type 'n at the end of 'a. *)
  type (_, _, _, _) snocs =
    | Zero : ('a, Fwn.zero, 'n, 'a) snocs
    | Suc : (('a, 'n) snoc, 'b, 'n, 'ab) snocs -> ('a, 'b Fwn.suc, 'n, 'ab) snocs

  let rec snoc_snocs_eq_snoc :
      type a b c n. (a, b, n, c) snocs -> ((a, n) snoc, b, n, (c, n) snoc) snocs = function
    | Zero -> Zero
    | Suc ab -> Suc (snoc_snocs_eq_snoc ab)

  let snoc_snocs : type a b c n. (a, b Fwn.suc, n, c) snocs -> ((a, n) snoc, b, n, c) snocs =
    function
    | Suc ab -> ab

  let snocs_suc_eq_snoc : type a b c n. (a, b, n, c) snocs -> (a, b Fwn.suc, n, (c, n) snoc) snocs =
   fun ab -> Suc (snoc_snocs_eq_snoc ab)

  let rec snocs_right : type a b c n. (a, b, n, c) snocs -> b Fwn.t = function
    | Zero -> Zero
    | Suc ab -> Suc (snocs_right ab)

  type (_, _, _) has_snocs = Snocs : ('a, 'b, 'n, 'ab) snocs -> ('a, 'b, 'n) has_snocs

  let rec snocs : type a b n. b Fwn.t -> (a, b, n) has_snocs =
   fun b ->
    match b with
    | Zero -> Snocs Zero
    | Suc b ->
        let (Snocs p) = snocs b in
        Snocs (Suc p)

  (* ('a, 'n, 'b) insert says that 'b is obtained by inserting a type 'n somewhere in 'a.  Or, put differently, 'a is obtained from 'b by deleting a type 'n in a specified location. *)
  type (_, _, _) insert =
    | Now : ('a, 'n, ('a, 'n) snoc) insert
    | Later : ('a, 'n, 'b) insert -> (('a, 'k) snoc, 'n, ('b, 'k) snoc) insert

  (* Two successive insertions can be performed in the other order. *)
  type (_, _, _, _) comp_insert =
    | Comp_insert : ('a, 'k, 'd) insert * ('d, 'n, 'c) insert -> ('a, 'n, 'k, 'c) comp_insert

  let rec comp_insert :
      type a n k b c. (a, n, b) insert -> (b, k, c) insert -> (a, n, k, c) comp_insert =
   fun ab bc ->
    match (ab, bc) with
    | Now, Now -> Comp_insert (Now, Later Now)
    | Now, Later bc -> Comp_insert (bc, Now)
    | Later ab, Now -> Comp_insert (Now, Later (Later ab))
    | Later ab, Later bc ->
        let (Comp_insert (ad, dc)) = comp_insert ab bc in
        Comp_insert (Later ad, Later dc)

  (* ('a, 'b) permute says that 'a is a permutation of 'b, both being backwards type lists. *)
  type (_, _) permute =
    | Id : ('a, 'a) permute
    | Insert : ('a, 'b) permute * ('b, 'n, 'c) insert -> (('a, 'n) snoc, 'c) permute

  let id_perm : type a. (a, a) permute = Id

  (* There is some redundancy in the above presentation of permutations: Insert (Id, Now) is the same permutation as Id (of a longer list).  We could probably set up the data structures to exclude that possibility statically, but for now we are content to provide a "smart constructor" version of Insert that refuses to create Insert (Id, Now), returning Id instead.  (The latter is preferred for efficiency reasons, because when computing with a permutation we can sometimes short-circuit the rest of the computation if we know the rest of the permutation is an identity.)  *)
  let insert : type a b n c. (a, b) permute -> (b, n, c) insert -> ((a, n) snoc, c) permute =
   fun perm ins ->
    match (perm, ins) with
    | Id, Now -> Id
    | _ -> Insert (perm, ins)

  (* Insertions can be transferred across a permutation, and when the image is removed produce a new permutation. *)
  type (_, _, _) permute_insert =
    | Permute_insert : ('d, 'n, 'c) insert * ('a, 'd) permute -> ('a, 'n, 'c) permute_insert

  let rec permute_insert :
      type a n b c. (a, n, b) insert -> (b, c) permute -> (a, n, c) permute_insert =
   fun ab bc ->
    match bc with
    | Id -> Permute_insert (ab, Id)
    | Insert (bc, ins) -> (
        match ab with
        | Now -> Permute_insert (ins, bc)
        | Later ab ->
            let (Permute_insert (res, p)) = permute_insert ab bc in
            let (Comp_insert (x, y)) = comp_insert res ins in
            Permute_insert (y, insert p x))

  (* Compose two permutations. *)
  let rec comp_permute : type a b c. (a, b) permute -> (b, c) permute -> (a, c) permute =
   fun ab bc ->
    match ab with
    | Id -> bc
    | Insert (ab, b) ->
        let (Permute_insert (c, bc)) = permute_insert b bc in
        insert (comp_permute ab bc) c

  let rec coinsert : type a b n c. (a, b) permute -> (a, n, c) insert -> (c, (b, n) snoc) permute =
   fun p i ->
    match i with
    | Now -> insert p Now
    | Later i -> (
        match p with
        | Insert (p, j) -> insert (coinsert p i) (Later j)
        | Id -> (
            match i with
            | Now -> insert (coinsert Id i) (Later Now)
            | Later _ -> insert (coinsert Id i) (Later Now)))

  let rec permute_inv : type a b. (a, b) permute -> (b, a) permute = function
    | Id -> Id
    | Insert (p, i) -> coinsert (permute_inv p) i

  (* As with lists and backwards lists, a forward type-list can naturally be appended to a backward one. *)

  type (_, _, _) append =
    | Append_nil : ('a, nil, 'a) append
    | Append_cons : (('a, 'x) snoc, 'b, 'c) append -> ('a, ('x, 'b) cons, 'c) append

  type (_, _) has_append = Append : ('a, 'b, 'c) append -> ('a, 'b) has_append

  let rec append : type a b. b Tlist.t -> (a, b) has_append = function
    | Nil -> Append Append_nil
    | Cons xs ->
        let (Append ab) = append xs in
        Append (Append_cons ab)

  (* Extend an insertion by the identity *)
  type (_, _) insert_into = Insert_into : ('a, 'n, 'b) insert -> ('n, 'b) insert_into

  let rec insert_append :
      type a n b c bc. (a, n, b) insert -> (b, c, bc) append -> (n, bc) insert_into =
   fun ins bc ->
    match bc with
    | Append_nil -> Insert_into ins
    | Append_cons bc -> insert_append (Later ins) bc

  (* Extend a permutation by the identity *)
  let rec permute_append :
      type a b c ac bc. (a, b) permute -> (a, c, ac) append -> (b, c, bc) append -> (ac, bc) permute
      =
   fun ab ac bc ->
    match (ac, bc) with
    | Append_nil, Append_nil -> ab
    | Append_cons ac, Append_cons bc -> permute_append (insert ab Now) ac bc

  (* Change a backwards type-list into a forwards one. *)

  type _ to_tlist = To_tlist : 'a Tlist.t * (emp, 'a, 'b) append -> 'b to_tlist

  let to_tlist : type c. c t -> c to_tlist =
   fun c ->
    let rec go : type a b c. a t -> b Tlist.t -> (a, b, c) append -> c to_tlist =
     fun a b abc ->
      match a with
      | Emp -> To_tlist (b, abc)
      | Snoc a -> go a (Cons b) (Append_cons abc) in
    go c Nil Append_nil

  (* When appending a forwards type-list to a backwards one, if we insert the same type on the left and on the right, the results are permuted. *)
  let rec ins_ins_permute :
      type a b n c d ad bc.
      (a, n, b) insert ->
      (c, n, d) Tlist.insert ->
      (b, c, bc) append ->
      (a, d, ad) append ->
      (bc, ad) permute =
   fun ab cd bc ad ->
    match cd with
    | Now ->
        let (Append_cons ad) = ad in
        permute_append (coinsert Id ab) bc ad
    | Later cd ->
        let Append_cons ad, Append_cons bc = (ad, bc) in
        ins_ins_permute (Later ab) cd bc ad

  (* ('a, 'b, 'c) append_permute says that the backwards 'c is obtained from the backwards 'a by appending a permutation of the forwards 'b.  In particular, (emp, 'b, 'c) says that the backwards 'c is a permutation of the forwards 'b. *)
  type (_, _, _) append_permute =
    | Ap_nil : ('a, nil, 'a) append_permute
    | Ap_insert :
        ('b, 'n, 'd) Tlist.insert * (('a, 'n) snoc, 'b, 'c) append_permute
        -> ('a, 'd, 'c) append_permute

  let rec append_permute_right : type a b c. (a, b, c) append_permute -> b Tlist.t = function
    | Ap_nil -> Nil
    | Ap_insert (ins, b) -> Tlist.inserted ins (append_permute_right b)

  (* If we append and also append_permute, the two results are related by a permutation. *)
  let rec append_append_permute :
      type a b c d. (a, b, d) append_permute -> (a, b, c) append -> (d, c) permute =
   fun d c ->
    match d with
    | Ap_nil ->
        let Append_nil = c in
        Id
    | Ap_insert (ins, d) ->
        let (Append a) = append (append_permute_right d) in
        let perm1 = append_append_permute d a in
        let perm2 = ins_ins_permute Now ins a c in
        comp_permute perm1 perm2

  (* Flatten a tbwd of (backward) nats into a single nat. *)
  type (_, _) flatten =
    | Flat_emp : (emp, N.zero) flatten
    | Flat_snoc : ('ns, 'm) flatten * ('m, 'n, 'mn) N.plus -> (('ns, 'n) snoc, 'mn) flatten

  (* This is a partial function. *)
  let rec flatten_uniq : type ns m n. (ns, m) flatten -> (ns, n) flatten -> (m, n) Eq.t =
   fun m n ->
    match (m, n) with
    | Flat_emp, Flat_emp -> Eq
    | Flat_snoc (m, x), Flat_snoc (n, y) ->
        let Eq = flatten_uniq m n in
        let Eq = N.plus_uniq x y in
        Eq

  (* Flattening maps appending to adding. *)
  type (_, _, _) bplus_flatten_append =
    | Bplus_flatten_append :
        ('ps, 'p) flatten * ('m, 'n, 'p) Fwn.bplus
        -> ('m, 'n, 'ps) bplus_flatten_append

  let rec bplus_flatten_append :
      type ms ns ps m n p.
      (ms, m) flatten ->
      (ns, n) Tlist.flatten ->
      (ms, ns, ps) append ->
      (m, n, ps) bplus_flatten_append =
   fun ms ns mnp ->
    match mnp with
    | Append_nil ->
        let Flat_nil = ns in
        Bplus_flatten_append (ms, Zero)
    | Append_cons mnp ->
        let (Flat_cons (n, ns)) = ns in
        let (Plus m) = N.plus (Fwn.fplus_left n) in
        let (Bplus_flatten_append (ps, mn)) = bplus_flatten_append (Flat_snoc (ms, m)) ns mnp in
        Bplus_flatten_append (ps, Fwn.bfplus_assocr m n mn)

  (* If we remove an entry from a flattenable list, the result is again flattenable, and the missing entry can be added to its flattening to obtain the original one.  (Note that the latter fact uses commutativity of addition for nat). *)
  type (_, _, _) flatten_uninsert =
    | Flatten_uninsert : ('bs, 'b) flatten * ('b, 'n, 'c) N.plus -> ('bs, 'n, 'c) flatten_uninsert

  let rec flatten_uninsert :
      type bs cs n c. (bs, n, cs) insert -> (cs, c) flatten -> (bs, n, c) flatten_uninsert =
   fun ins cs ->
    match (ins, cs) with
    | Now, Flat_snoc (cs, c) -> Flatten_uninsert (cs, c)
    | Later ins, Flat_snoc (cs, xy_z) ->
        let (Flatten_uninsert (bs, x_y)) = flatten_uninsert ins cs in
        let (Plus x_z) = N.plus (N.plus_right xy_z) in
        let (Plus y_z) = N.plus (N.plus_right xy_z) in
        let z_y = N.plus_comm (N.plus_right x_y) y_z in
        let x_yz = N.plus_assocr x_y y_z xy_z in
        let xz_y = N.plus_assocl x_z z_y x_yz in
        Flatten_uninsert (Flat_snoc (bs, x_z), xz_y)

  (* An insertion determines an index for inserting into the flattened version of the list inserted into. *)
  let rec index_of_flattened_insert :
      type xs n ys x. (xs, n, ys) insert -> (xs, x) flatten -> x N.suc N.index =
   fun i xs ->
    match i with
    | Now -> Top
    | Later i ->
        let (Flat_snoc (xs, x)) = xs in
        N.index_plus (index_of_flattened_insert i xs) (N.suc_plus_eq_suc x)

  (* A permutation of lists of nats inducse a ("block") permutation on flattenings. *)
  let rec permute_flatten :
      type ms m ns n. (ms, m) flatten -> (ns, n) flatten -> (ms, ns) permute -> (m, n) N.perm =
   fun ms ns p ->
    match p with
    | Id ->
        let Eq = flatten_uniq ms ns in
        Id
    | Insert (p, i) ->
        let (Flat_snoc (ms, m)) = ms in
        let (Flatten_uninsert (ns, n)) = flatten_uninsert i ns in
        let q = permute_flatten ms ns p in
        let j = index_of_flattened_insert i ns in
        N.insert_plus q j m n

  (* Tbwds of types satisfying a predicate. *)
  module type Predicate = sig
    type 'a t
  end

  module Of (P : Predicate) = struct
    type _ t = Of_emp : emp t | Of_snoc : 'xs t * 'x P.t -> ('xs, 'x) snoc t

    let rec insert : type a n b. (a, n, b) insert -> a t -> n P.t -> b t =
     fun i a n ->
      match i with
      | Now -> Of_snoc (a, n)
      | Later i ->
          let (Of_snoc (a, k)) = a in
          Of_snoc (insert i a n, k)

    let rec uninsert : type a n b. (a, n, b) insert -> b t -> a t =
     fun i b ->
      match i with
      | Now ->
          let (Of_snoc (b, _)) = b in
          b
      | Later i ->
          let (Of_snoc (b, n)) = b in
          Of_snoc (uninsert i b, n)

    let rec inserted : type a n b. (a, n, b) insert -> b t -> n P.t =
     fun i b ->
      match i with
      | Now ->
          let (Of_snoc (_, n)) = b in
          n
      | Later i ->
          let (Of_snoc (b, _)) = b in
          inserted i b

    let rec permute : type a b. (a, b) permute -> b t -> a t =
     fun p b ->
      match p with
      | Id -> b
      | Insert (p, i) -> Of_snoc (permute p (uninsert i b), inserted i b)
  end

  (* Map a type-level function. *)
  module type TFun = sig
    module Dom : Predicate
    module Cod : Predicate

    (* We add an extra parameter because we want to get out, in particular, a map of monoid addition parametrized by the thing being added, and once a type is wrapped in a module there's no way to get it out as a parameter. *)
    type 'p param
    type ('p, 'a, 'b) t
    type (_, _) exists = Exists : 'b Cod.t * ('p, 'a, 'b) t -> ('p, 'a) exists

    val exists : 'p param -> 'a Dom.t -> ('p, 'a) exists
    val out : 'p param -> 'a Dom.t -> ('p, 'a, 'b) t -> 'b Cod.t
    val uniq : ('p, 'a, 'b1) t -> ('p, 'a, 'b2) t -> ('b1, 'b2) Eq.t
  end

  module Map (F : TFun) = struct
    module OfDom = Of (F.Dom)
    module OfCod = Of (F.Cod)

    type (_, _, _) t =
      | Map_emp : ('p, emp, emp) t
      | Map_snoc : ('p, 'xs, 'ys) t * ('p, 'x, 'y) F.t -> ('p, ('xs, 'x) snoc, ('ys, 'y) snoc) t

    let rec out : type p xs ys. p F.param -> xs OfDom.t -> (p, xs, ys) t -> ys OfCod.t =
     fun p xs pxs ->
      match (xs, pxs) with
      | Of_emp, Map_emp -> Of_emp
      | Of_snoc (xs, x), Map_snoc (pxs, px) -> Of_snoc (out p xs pxs, F.out p x px)

    type (_, _) exists = Exists : 'ys OfCod.t * ('p, 'xs, 'ys) t -> ('p, 'xs) exists

    let rec exists : type p xs. p F.param -> xs OfDom.t -> (p, xs) exists =
     fun p -> function
      | Of_emp -> Exists (Of_emp, Map_emp)
      | Of_snoc (xs, x) ->
          let (Exists (ys, fxs)) = exists p xs in
          let (Exists (y, fx)) = F.exists p x in
          Exists (Of_snoc (ys, y), Map_snoc (fxs, fx))

    let rec uniq : type p xs ys zs. (p, xs, ys) t -> (p, xs, zs) t -> (ys, zs) Eq.t =
     fun fxs fxs' ->
      match (fxs, fxs') with
      | Map_emp, Map_emp -> Eq
      | Map_snoc (fxs, fx), Map_snoc (fxs', fx') ->
          let Eq = uniq fxs fxs' in
          let Eq = F.uniq fx fx' in
          Eq

    type (_, _, _, _) map_insert =
      | Map_insert : ('zs, 'fx, 'ws) insert * ('p, 'ys, 'ws) t -> ('p, 'fx, 'ys, 'zs) map_insert

    let rec insert :
        type p xs x z ys zs.
        (p, x, z) F.t -> (xs, x, ys) insert -> (p, xs, zs) t -> (p, z, ys, zs) map_insert =
     fun z i fxs ->
      match i with
      | Now -> Map_insert (Now, Map_snoc (fxs, z))
      | Later i ->
          let (Map_snoc (fxs, fx)) = fxs in
          let (Map_insert (fi, fxs)) = insert z i fxs in
          Map_insert (Later fi, Map_snoc (fxs, fx))

    type (_, _, _, _) unmap_insert =
      | Unmap_insert :
          ('p, 'x, 'z) F.t * ('xs, 'x, 'ys) insert * ('p, 'xs, 'zs) t
          -> ('p, 'z, 'ys, 'zs) unmap_insert

    let rec unmap_insert :
        type p ys z zs ws. (zs, z, ws) insert -> (p, ys, ws) t -> (p, z, ys, zs) unmap_insert =
     fun i fxs ->
      match i with
      | Now ->
          let (Map_snoc (fxs, fx)) = fxs in
          Unmap_insert (fx, Now, fxs)
      | Later i ->
          let (Map_snoc (fxs, fx)) = fxs in
          let (Unmap_insert (fx', fi, fxs)) = unmap_insert i fxs in
          Unmap_insert (fx', Later fi, Map_snoc (fxs, fx))

    type (_, _, _) map_permute =
      | Map_permute : ('p, 'zs, 'ws) t * ('ys, 'ws) permute -> ('p, 'zs, 'ys) map_permute

    let rec permute : type p xs ys zs. (p, xs, ys) t -> (xs, zs) permute -> (p, zs, ys) map_permute
        =
     fun fxs pp ->
      match pp with
      | Id -> Map_permute (fxs, Id)
      | Insert (pp, i) ->
          let (Map_snoc (fxs, fx)) = fxs in
          let (Map_permute (pfxs, qq)) = permute fxs pp in
          let (Map_insert (pi, ifx)) = insert fx i pfxs in
          Map_permute (ifx, Insert (qq, pi))
  end
end
