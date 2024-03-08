(* Type-level backwards lists *)

open Tlist

type emp = private Dummy_emp
type ('xs, 'x) snoc = private Dummy_ext

module Tbwd = struct
  type _ t = Emp : emp t | Snoc : 'xs t -> ('xs, 'x) snoc t

  (* ('a, 'b, 'n, 'ab) snocs means that 'a is a tbwd (although this isn't enforced -- it could be any type), 'b is a Fwn.t, and 'ab is the result of adding 'b copies of the dimension 'n at the end of 'a. *)
  type (_, _, _, _) snocs =
    | Zero : ('a, Fwn.zero, 'n, 'a) snocs
    | Suc : ('a, 'b, 'n, 'ab) snocs -> ('a, 'b Fwn.suc, 'n, ('ab, 'n) snoc) snocs

  let rec snocs_snoc : type a b c n. (a, b, n, c) snocs -> ((a, n) snoc, b, n, (c, n) snoc) snocs =
    function
    | Zero -> Zero
    | Suc ab -> Suc (snocs_snoc ab)

  let snocs_suc : type a b c n. (a, b Fwn.suc, n, c) snocs -> ((a, n) snoc, b, n, c) snocs =
    function
    | Suc ab -> snocs_snoc ab

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

  (* ('a, 'n, 'b) insert says that 'b is obtained by inserting a dimension 'n somewhere in 'a.  Or, put differently, 'a is obtained from 'b by deleting a dimension 'n from somewhere. *)
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
      (a, d, ad) append ->
      (b, c, bc) append ->
      (ad, bc) permute =
   fun ab cd ad bc ->
    match cd with
    | Now ->
        let (Append_cons ad) = ad in
        permute_append (insert Id ab) ad bc
    | Later cd ->
        let Append_cons ad, Append_cons bc = (ad, bc) in
        ins_ins_permute (Later ab) cd ad bc

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
      type a b c d. (a, b, c) append -> (a, b, d) append_permute -> (c, d) permute =
   fun c d ->
    match d with
    | Ap_nil ->
        let Append_nil = c in
        Id
    | Ap_insert (ins, d) ->
        let (Append a) = append (append_permute_right d) in
        let perm1 = append_append_permute a d in
        let perm2 = ins_ins_permute Now ins c a in
        comp_permute perm2 perm1
end
