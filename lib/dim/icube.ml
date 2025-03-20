open Util
open Signatures
open Sface
open Bwsface

(* This is a version of the cube data structure whose indices can "count" some type-level data that is accumulated by what is stored.  For instance, if each entry is parametrized by a type-level natural number, then the cube data structure is parametrized by the total of all these numbers.  In fact it is parametrized by the operation of addition of this number, or more precisely by both an input and result for this operation.

   Unfortunately I have not figured out a way to unify this with ordinary Cubes.  In particular, it seems unlikely that a generic traversal is possible for these indexed cubes, since different Icubes, even with the same input and output "counts", might distribute these counts differently to different entries, so that a generic traversal wouldn't know how to match up the types of its inputs or outputs. *)

(* An Icube is parametrized by a 4-variable family.  In ('left, 'm, 'b, 'right) F.t, the meanings of 'm and 'b are as for ('m, 'b) F.t in an ordinary Cube, while (intuitively, at least) 'right is obtained from 'left by "adding" the data specified by F. *)
module Icube (F : Fam4) = struct
  (* The basic definitions are mostly just like those of Cube, with extra parameters. *)
  type (_, _, _, _, _) gt =
    | Leaf : ('left, 'n, 'b, 'right) F.t -> ('left, D.zero, 'n, 'b, 'right) gt
    | Branch :
        'l Endpoints.len
        * ('left, 'l, 'm, 'n, 'b, 'middle) branches
        * ('middle, 'm, 'n D.suc, 'b, 'right) gt
        -> ('left, 'm D.suc, 'n D.suc, 'b, 'right) gt

  (* The exception is that instead of using a vanilla Bwv, to index the branches we use a custom kind of backwards list that tracks the change in the indices. *)
  and (_, _, _, _, _, _) branches =
    | Emp : ('left, N.zero, 'm, 'n, 'b, 'left) branches
    | Snoc :
        ('left, 'l, 'm, 'n, 'b, 'middle) branches * ('middle, 'm, 'n, 'b, 'right) gt
        -> ('left, 'l N.suc, 'm, 'n, 'b, 'right) branches

  type ('left, 'n, 'b, 'right) t = ('left, 'n, 'n, 'b, 'right) gt

  let rec gdim : type m n b left right. (left, m, n, b, right) gt -> m D.t = function
    | Leaf _ -> D.zero
    | Branch (_, _, br) -> D.suc (gdim br)

  let dim : type n b left right. (left, n, b, right) t -> n D.t = fun tr -> gdim tr

  (* While we can't have a truly generic traversal, we can define some special cases.  The simplest one is "map" which applies some function to each entry, preserving all the indices on the nose.  Like the traversal of Cube, but unlike the others below, it makes sense in any applicative functor. *)

  module Applicatic (M : Applicative.Plain) = struct
    open Applicative.Ops (M)

    (* ********** Map ********** *)

    type ('n, 'b, 'c) mapperM = {
      map :
        'left 'right 'm.
        ('m, 'n) sface -> ('left, 'm, 'b, 'right) F.t -> ('left, 'm, 'c, 'right) F.t M.t;
    }

    let rec gmapM : type k m km n b c l left right.
        (k, m, km) D.plus ->
        (l, m, n) D.plus ->
        (k, l) bwsface ->
        (n, b, c) mapperM ->
        (left, m, km, b, right) gt ->
        (left, m, km, c, right) gt M.t =
     fun km lm d g tr ->
      match tr with
      | Leaf x ->
          let Zero, Zero = (km, lm) in
          let+ x = g.map (sface_of_bw d) x in
          Leaf x
      | Branch (l, ends, mid) ->
          let (Suc km') = km in
          let+ newends = gmapM_branches km' (D.suc_plus lm) d g (Endpoints.indices l) ends
          and+ newmid = gmapM (D.suc_plus km) (D.suc_plus lm) (Mid d) g mid in
          Branch (l, newends, newmid)

    and gmapM_branches : type k m km n b c l len len' left right.
        (k, m, km) D.plus ->
        (l N.suc, m, n) D.plus ->
        (k, l) bwsface ->
        (n, b, c) mapperM ->
        (len Endpoints.t, len') Bwv.t ->
        (left, len', m, km, b, right) branches ->
        (left, len', m, km, c, right) branches M.t =
     fun km lm d g ixs brs ->
      match (brs, ixs) with
      | Emp, Emp -> return Emp
      | Snoc (brs, br), Snoc (ixs, e) ->
          let+ newbrs = gmapM_branches km lm d g ixs brs
          and+ newbr = gmapM km lm (End (e, d)) g br in
          Snoc (newbrs, newbr)

    let mapM : type n b c left right.
        (n, b, c) mapperM -> (left, n, b, right) t -> (left, n, c, right) t M.t =
     fun g x ->
      let n = dim x in
      gmapM (D.zero_plus n) (D.zero_plus n) Zero g x
  end

  module IdM = Applicatic (Applicative.OfMonad (Monad.Identity))

  let map : type n b c left right.
      (n, b, c) IdM.mapperM -> (left, n, b, right) t -> (left, n, c, right) t =
   fun g x -> IdM.mapM g x

  (* ********** Traversals with indexed state ********** *)

  (* The natural way to traverse or build an indexed cube is to maintain an accumulator that's indexed by the intermediate types.  Thus, for instance, from a plain cube regarded as one of these cubes, we can append all of its entries to some Bwv. *)

  module Traverse (Acc : Fam) = struct
    type ('n, 'b, 'c) left_folder = {
      foldmap :
        'left 'right 'm.
        ('m, 'n) sface ->
        'left Acc.t ->
        ('left, 'm, 'b, 'right) F.t ->
        ('left, 'm, 'c, 'right) F.t * 'right Acc.t;
    }

    let rec gfold_map_left : type k m km n b c l left right.
        (k, m, km) D.plus ->
        (l, m, n) D.plus ->
        (k, l) bwsface ->
        (n, b, c) left_folder ->
        left Acc.t ->
        (left, m, km, b, right) gt ->
        (left, m, km, c, right) gt * right Acc.t =
     fun km lm d g acc tr ->
      match tr with
      | Leaf x ->
          let Zero, Zero = (km, lm) in
          let x, acc = g.foldmap (sface_of_bw d) acc x in
          (Leaf x, acc)
      | Branch (l, ends, mid) ->
          let (Suc km') = km in
          let ends, acc =
            gfold_left_map_branches km' (D.suc_plus lm) d g (Endpoints.indices l) acc ends in
          let mid, acc = gfold_map_left (D.suc_plus km) (D.suc_plus lm) (Mid d) g acc mid in
          (Branch (l, ends, mid), acc)

    and gfold_left_map_branches : type k m km n b c l len len' left right.
        (k, m, km) D.plus ->
        (l N.suc, m, n) D.plus ->
        (k, l) bwsface ->
        (n, b, c) left_folder ->
        (len Endpoints.t, len') Bwv.t ->
        left Acc.t ->
        (left, len', m, km, b, right) branches ->
        (left, len', m, km, c, right) branches * right Acc.t =
     fun km lm d g ixs acc brs ->
      match (brs, ixs) with
      | Emp, Emp -> (Emp, acc)
      | Snoc (brs, br), Snoc (ixs, e) ->
          let brs, acc = gfold_left_map_branches km lm d g ixs acc brs in
          let br, acc = gfold_map_left km lm (End (e, d)) g acc br in
          (Snoc (brs, br), acc)

    let fold_map_left : type n b c left right.
        (n, b, c) left_folder ->
        left Acc.t ->
        (left, n, n, b, right) gt ->
        (left, n, n, c, right) gt * right Acc.t =
     fun g acc x ->
      let n = dim x in
      gfold_map_left (D.zero_plus n) (D.zero_plus n) Zero g acc x

    (* And dually on the right. *)

    type ('n, 'b, 'c) right_folder = {
      foldmap :
        'left 'right 'm.
        ('m, 'n) sface ->
        ('left, 'm, 'b, 'right) F.t ->
        'right Acc.t ->
        'left Acc.t * ('left, 'm, 'c, 'right) F.t;
    }

    let rec gfold_map_right : type k m km n b c l left right.
        (k, m, km) D.plus ->
        (l, m, n) D.plus ->
        (k, l) bwsface ->
        (n, b, c) right_folder ->
        (left, m, km, b, right) gt ->
        right Acc.t ->
        left Acc.t * (left, m, km, c, right) gt =
     fun km lm d g tr acc ->
      match tr with
      | Leaf x ->
          let Zero, Zero = (km, lm) in
          let acc, x = g.foldmap (sface_of_bw d) x acc in
          (acc, Leaf x)
      | Branch (l, ends, mid) ->
          let (Suc km') = km in
          let acc, mid = gfold_map_right (D.suc_plus km) (D.suc_plus lm) (Mid d) g mid acc in
          let acc, ends =
            gfold_right_map_branches km' (D.suc_plus lm) d g (Endpoints.indices l) ends acc in
          (acc, Branch (l, ends, mid))

    and gfold_right_map_branches : type k m km n b c l len len' left right.
        (k, m, km) D.plus ->
        (l N.suc, m, n) D.plus ->
        (k, l) bwsface ->
        (n, b, c) right_folder ->
        (len Endpoints.t, len') Bwv.t ->
        (left, len', m, km, b, right) branches ->
        right Acc.t ->
        left Acc.t * (left, len', m, km, c, right) branches =
     fun km lm d g ixs brs acc ->
      match (brs, ixs) with
      | Emp, Emp -> (acc, Emp)
      | Snoc (brs, br), Snoc (ixs, e) ->
          let acc, br = gfold_map_right km lm (End (e, d)) g br acc in
          let acc, brs = gfold_right_map_branches km lm d g ixs brs acc in
          (acc, Snoc (brs, br))

    let fold_map_right : type n b c left right.
        (n, b, c) right_folder ->
        (left, n, b, right) t ->
        right Acc.t ->
        left Acc.t * (left, n, c, right) t =
     fun g x acc ->
      let n = dim x in
      gfold_map_right (D.zero_plus n) (D.zero_plus n) Zero g x acc

    (* Similarly for building. *)

    type (_, _, _) fwrap_left =
      | Fwrap : ('left, 'm, 'b, 'right) F.t * 'right Acc.t -> ('left, 'm, 'b) fwrap_left

    type (_, _, _, _) gwrap_left =
      | Wrap : ('left, 'm, 'mk, 'b, 'right) gt * 'right Acc.t -> ('left, 'm, 'mk, 'b) gwrap_left

    type ('left, 'm, 'b) wrap_left = ('left, 'm, 'm, 'b) gwrap_left

    type (_, _, _, _, _) wrap_branches_left =
      | Wrap_branches :
          ('left, 'len, 'm, 'mk, 'b, 'right) branches * 'right Acc.t
          -> ('left, 'len, 'm, 'mk, 'b) wrap_branches_left

    type ('n, 'b) builder_leftM = {
      build : 'left 'm. ('m, 'n) sface -> 'left Acc.t -> ('left, 'm, 'b) fwrap_left;
    }

    let rec gbuild_left : type k m mk l ml b left.
        m D.t ->
        (m, k, mk) D.plus ->
        (m, l, ml) D.plus ->
        (k, l) bwsface ->
        (ml, b) builder_leftM ->
        left Acc.t ->
        (left, m, mk, b) gwrap_left =
     fun m mk ml d g acc ->
      match m with
      | Nat Zero ->
          let Eq = D.plus_uniq mk (D.zero_plus (dom_bwsface d)) in
          let Eq = D.plus_uniq ml (D.zero_plus (cod_bwsface d)) in
          let (Fwrap (x, acc)) = g.build (sface_of_bw d) acc in
          Wrap (Leaf x, acc)
      | Nat (Suc m) ->
          let (Suc mk') = D.plus_suc mk in
          let (Wrap l) = Endpoints.wrapped () in
          let (Wrap_branches (ends, acc)) =
            gbuild_left_branches (Nat m) mk' (D.plus_suc ml) d g (Endpoints.indices l) acc in
          let (Wrap (mid, acc)) =
            gbuild_left (Nat m) (D.plus_suc mk) (D.plus_suc ml) (Mid d) g acc in
          Wrap (Branch (l, ends, mid), acc)

    and gbuild_left_branches : type k m mk l ml b left len len'.
        m D.t ->
        (m, k, mk) D.plus ->
        (m, l N.suc, ml) D.plus ->
        (k, l) bwsface ->
        (ml, b) builder_leftM ->
        (len Endpoints.t, len') Bwv.t ->
        left Acc.t ->
        (left, len', m, mk, b) wrap_branches_left =
     fun m mk ml d g ixs acc ->
      match ixs with
      | Emp -> Wrap_branches (Emp, acc)
      | Snoc (ixs, e) ->
          let (Wrap_branches (newbrs, acc)) = gbuild_left_branches m mk ml d g ixs acc in
          let (Wrap (newbr, acc)) = gbuild_left m mk ml (End (e, d)) g acc in
          Wrap_branches (Snoc (newbrs, newbr), acc)

    let build_left : type n b left.
        n D.t -> (n, b) builder_leftM -> left Acc.t -> (left, n, b) wrap_left =
     fun n g acc -> gbuild_left n (D.plus_zero n) (D.plus_zero n) Zero g acc

    type (_, _, _) fwrap_right =
      | Fwrap : 'left Acc.t * ('left, 'm, 'b, 'right) F.t -> ('m, 'b, 'right) fwrap_right

    type (_, _, _, _) gwrap_right =
      | Wrap : 'left Acc.t * ('left, 'm, 'mk, 'b, 'right) gt -> ('m, 'mk, 'b, 'right) gwrap_right

    type ('m, 'b, 'right) wrap_right = ('m, 'm, 'b, 'right) gwrap_right

    type (_, _, _, _, _) wrap_branches_right =
      | Wrap_branches :
          'left Acc.t * ('left, 'len, 'm, 'mk, 'b, 'right) branches
          -> ('len, 'm, 'mk, 'b, 'right) wrap_branches_right

    type ('n, 'b) builder_rightM = {
      build : 'right 'm. ('m, 'n) sface -> 'right Acc.t -> ('m, 'b, 'right) fwrap_right;
    }

    let rec gbuild_right : type k m mk l ml b right.
        m D.t ->
        (m, k, mk) D.plus ->
        (m, l, ml) D.plus ->
        (k, l) bwsface ->
        (ml, b) builder_rightM ->
        right Acc.t ->
        (m, mk, b, right) gwrap_right =
     fun m mk ml d g acc ->
      match m with
      | Nat Zero ->
          let Eq = D.plus_uniq mk (D.zero_plus (dom_bwsface d)) in
          let Eq = D.plus_uniq ml (D.zero_plus (cod_bwsface d)) in
          let (Fwrap (acc, x)) = g.build (sface_of_bw d) acc in
          Wrap (acc, Leaf x)
      | Nat (Suc m) ->
          let (Suc mk') = D.plus_suc mk in
          let (Wrap l) = Endpoints.wrapped () in
          let (Wrap (acc, mid)) =
            gbuild_right (Nat m) (D.plus_suc mk) (D.plus_suc ml) (Mid d) g acc in
          let (Wrap_branches (acc, ends)) =
            gbuild_right_branches (Nat m) mk' (D.plus_suc ml) d g (Endpoints.indices l) acc in
          Wrap (acc, Branch (l, ends, mid))

    and gbuild_right_branches : type k m mk l ml b right len len'.
        m D.t ->
        (m, k, mk) D.plus ->
        (m, l N.suc, ml) D.plus ->
        (k, l) bwsface ->
        (ml, b) builder_rightM ->
        (len Endpoints.t, len') Bwv.t ->
        right Acc.t ->
        (len', m, mk, b, right) wrap_branches_right =
     fun m mk ml d g ixs acc ->
      match ixs with
      | Emp -> Wrap_branches (acc, Emp)
      | Snoc (ixs, e) ->
          let (Wrap (acc, newbr)) = gbuild_right m mk ml (End (e, d)) g acc in
          let (Wrap_branches (acc, newbrs)) = gbuild_right_branches m mk ml d g ixs acc in
          Wrap_branches (acc, Snoc (newbrs, newbr))

    let build_right : type n b right.
        n D.t -> (n, b) builder_rightM -> right Acc.t -> (n, b, right) wrap_right =
     fun n g acc -> gbuild_right n (D.plus_zero n) (D.plus_zero n) Zero g acc
  end

  (* Indexing *)

  type (_, _) fbiwrap = Fbiwrap : ('left, 'n, 'b, 'right) F.t -> ('n, 'b) fbiwrap

  let rec gfind : type m n k km nm b left right.
      (left, km, nm, b, right) gt ->
      (k, m, km) D.plus ->
      (n, m, nm) D.plus ->
      (k, km) sface ->
      (n, b) fbiwrap =
   fun tr km nm d ->
    match (tr, d) with
    | Leaf x, Zero ->
        let Zero = km in
        let Zero = nm in
        Fbiwrap x
    | Branch (l1, br, _), End (d, (l2, e)) ->
        let (Le km') = plus_of_sface d in
        let Eq = D.minus_uniq' (dom_sface d) (Suc km') km in
        let (Suc nm') = nm in
        let Eq = Endpoints.uniq l1 l2 in
        gfind_branches br km' nm' d e
    | Branch (_, _, br), Mid d ->
        let (Suc km) = N.plus_suc km in
        gfind br km nm d

  and gfind_branches : type m n k km nm b left right l.
      (left, l, km, nm, b, right) branches ->
      (k, m, km) D.plus ->
      (n, m, nm) D.plus ->
      (k, km) sface ->
      l N.index ->
      (n, b) fbiwrap =
   fun br km nm d e ->
    match (br, e) with
    | Emp, _ -> .
    | Snoc (_, tr), Top -> gfind tr km nm d
    | Snoc (br, _), Pop e -> gfind_branches br km nm d e

  let find : type n k b left right. (left, n, b, right) t -> (k, n) sface -> (k, b) fbiwrap =
   fun tr d ->
    let (Le km) = plus_of_sface d in
    gfind tr km km d

  let rec gfind_top : type k n b left right. (left, k, n, b, right) gt -> (n, b) fbiwrap = function
    | Leaf x -> Fbiwrap x
    | Branch (_, _, br) -> gfind_top br

  let find_top : type n b left right. (left, n, b, right) t -> (n, b) fbiwrap =
   fun tr -> gfind_top tr
end

(* The most important case of indexed cubes is when the indices are type-level natural numbers that simply count how many entries there are in the cube.  In fact, as of May 8, 2024 this is the only case we are using.  TODO: Would it be easier to implement this case directly rather than as a special case of the more general version above, and if so would it simplify other things?  E.g. require fewer type annotations in uses?  It might also allow generic traversals to work. *)

module NFamOf = struct
  type (_, _, _, _) t = NFamOf : 'b -> ('left, 'n, 'b, 'left N.suc) t
end

module NICubeOf = struct
  include Icube (NFamOf)

  let singleton : type left b. b -> (left, D.zero, b, left N.suc) t = fun x -> Leaf (NFamOf x)

  module NFold = Traverse (N)

  let nfold : type left m n b right.
      (m, n) sface ->
      left N.t ->
      (left, m, b, right) NFamOf.t ->
      (left, m, unit, right) NFamOf.t * right N.t =
   fun _ n (NFamOf _) -> (NFamOf (), N.suc n)

  let out : type left m b right. left N.t -> (left, m, b, right) t -> right N.t =
   fun l b -> snd (NFold.fold_map_left { foldmap = nfold } l b)

  let find : type n k b left right. (left, n, b, right) t -> (k, n) sface -> b =
   fun tr fa ->
    let (Fbiwrap (NFamOf x)) = find tr fa in
    x

  let find_top : type n b left right. (left, n, b, right) t -> b =
   fun tr ->
    let (Fbiwrap (NFamOf x)) = find_top tr in
    x
end
