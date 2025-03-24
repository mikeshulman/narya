open Bwd
open Util
open Signatures
open Tlist
open Hlist
open Singleton
open Cube
open Sface
open Bwsface
open Tface
open Bwtface

(* Tube data structures *)

module Tube (F : Fam2) = struct
  module C = Cube (F)
  open C.Infix

  (* An (n,k,n+k)-tube is like a (n+k)-cube but where the top k indices (the "instantiated" ones) are not all maximal.  Hence if k=0 it is empty, while if n=0 it contains everything except the top face.  A (m,k,m+k,n)-gtube is the height-(m+k) part of such a tube, with k dimensions left to be instantiated and m uninstantiated, m+k total dimensions left, and n the current face dimension. *)
  type (_, _, _, _, _) gt =
    | Leaf : 'n D.t -> ('n, D.zero, 'n, 'nk, 'b) gt
    | Branch :
        'l Endpoints.len * (('mk, 'n, 'b) C.gt, 'l) Bwv.t * ('m, 'k, 'mk, 'n D.suc, 'b) gt
        -> ('m, 'k D.suc, 'mk D.suc, 'n D.suc, 'b) gt

  (* This definition gives a cardinality F(k,m) for (m,k,m+k,n,b) gtube with recurrence relations

     F(0,m) = 0
     F(k+1,m) = 3^(m+k) * 2 + F(k,m)

     Therefore, we can compute examples like

     F(1,m) = 3^m * 2 + F(0,m) = 3^m * 2 + 0 = 3^m * 2 = 3^(m+1) - 3^m
     F(2,m) = 3^(m+1) * 2 + F(1,m) = (3^(m+1) + 3^m) * 2 = (3^(m+2) + 3^(m+1)) - (3^(m+1) + 3^m) = 3^(m+2) - 3^m

     and so on, in general

     F(k,m) = 3^(m+k) - 3^m
  *)

  type ('n, 'k, 'nk, 'b) t = ('n, 'k, 'nk, 'nk, 'b) gt

  (* In a tube we always have m + k = m+k. *)

  let rec gplus : type m k mk n b. (m, k, mk, n, b) gt -> (m, k, mk) D.plus = function
    | Leaf _ -> Zero
    | Branch (_, _, mid) -> Suc (gplus mid)

  let plus : type m k mk b. (m, k, mk, b) t -> (m, k, mk) D.plus = fun t -> gplus t

  (* The constituents of a tube are valid dimensions. *)

  let inst : type m k mk b. (m, k, mk, b) t -> k D.t = fun t -> Nat (plus t)

  let rec guninst : type m k mk n b. (m, k, mk, n, b) gt -> m D.t = function
    | Leaf m -> m
    | Branch (_, _, mid) -> guninst mid

  let uninst : type m k mk b. (m, k, mk, b) t -> m D.t = fun t -> guninst t
  let out : type m k mk b. (m, k, mk, b) t -> mk D.t = fun t -> D.plus_out (uninst t) (plus t)

  (* The empty tube, with nothing instantiated *)

  let empty : type n b. n D.t -> (n, D.zero, n, b) t = fun n -> Leaf n

  (* Looking up with a tface *)

  let rec gfind : type m n k nk p q pq b.
      (n, k, nk, pq, b) gt ->
      (m, q, nk) D.plus ->
      (p, q, pq) D.plus ->
      (m, n, k, nk) tface ->
      (p, b) F.t =
   fun tr mq pq d ->
    match d with
    | End (d, _, (l1, e)) ->
        (* End (d,e) : (m,n,k+1,nk+1) tface *)
        (* d : (m,nk) sface *)
        (* tr : (n,k+1,nk+1,pq+1,b) gt *)
        let (Branch (l2, ends, _)) = tr in
        (* ends : bwv of (nk,pq,b) C.gt  *)
        let (Le km') = plus_of_sface d in
        (* km' : m + q = nk *)
        (* Suc km' : m + (q+1) = nk+1 *)
        (* mq : m + q+1 = nk+1 *)
        let Eq = D.minus_uniq' (dom_sface d) (Suc km') mq in
        (* q + 1 = q+1 *)
        (* pq : p + q+1 = pq+1 *)
        let (Suc pq') = pq in
        (* pq' : p + q = pq *)
        let Eq = Endpoints.uniq l1 l2 in
        C.gfind (Bwv.nth e ends) km' pq' d
    | Mid d ->
        let (Branch (_, _, mid)) = tr in
        let (Suc mq) = N.plus_suc mq in
        gfind mid mq pq d

  let find : type m n k nk b. (n, k, nk, b) t -> (m, n, k, nk) tface -> (m, b) F.t =
   fun tr d ->
    let (Le km) = plus_of_tface d in
    gfind tr km km d

  (* The boundary of a cube is a maximal tube. *)

  let rec gboundary : type m n b. (m, n, b) C.gt -> (D.zero, m, m, n, b) gt = function
    | Leaf _ -> Leaf D.zero
    | Branch (l, ends, mid) -> Branch (l, ends, gboundary mid)

  let boundary : type n b. (n, b) C.t -> (D.zero, n, n, b) t = fun tr -> gboundary tr

  (* We can also pick out a less-instantiated part of a tube *)

  let rec gpboundary : type m k mk l kl mkl n b.
      (m, k, mk) D.plus -> (k, l, kl) D.plus -> (m, kl, mkl, n, b) gt -> (mk, l, mkl, n, b) gt =
   fun mk kl tr ->
    match (kl, tr) with
    | Zero, _ ->
        let Eq = D.plus_uniq mk (gplus tr) in
        Leaf (D.plus_out (guninst tr) mk)
    | Suc kl, Branch (l, ends, mid) -> Branch (l, ends, gpboundary mk kl mid)

  let pboundary : type m k mk l kl mkl b.
      (m, k, mk) D.plus -> (k, l, kl) D.plus -> (m, kl, mkl, b) t -> (mk, l, mkl, b) t =
   fun mk kl tr -> gpboundary mk kl tr

  (* A tube that instantiates exactly one dimension is equivalently a Bwv of cubes. *)
  let of_cube_bwv : type n k nk b l.
      n D.t ->
      k is_singleton ->
      (n, k, nk) D.plus ->
      l Endpoints.len ->
      ((n, b) C.t, l) Bwv.t ->
      (n, k, nk, b) t =
   fun n k nk l cubes ->
    let One, Suc Zero = (k, nk) in
    Branch (l, cubes, Leaf n)

  let to_cube_bwv : type n k nk b l.
      k is_singleton ->
      (n, k, nk) D.plus ->
      l Endpoints.len ->
      (n, k, nk, b) t ->
      ((n, b) C.t, l) Bwv.t =
   fun k nk l tube ->
    let One, Suc Zero = (k, nk) in
    let (Branch (l', cubes, Leaf _)) = tube in
    let Eq = Endpoints.uniq l l' in
    cubes

  (* Heterogeneous lists and multimaps *)

  (* The structure of hlists for tubes is exactly parallel to that for cubes. *)
  module Heter = struct
    type (_, _, _, _, _) hgt =
      | [] : ('m, 'k, 'mk, 'nk, nil) hgt
      | ( :: ) :
          ('m, 'k, 'mk, 'nk, 'x) gt * ('m, 'k, 'mk, 'nk, 'xs) hgt
          -> ('m, 'k, 'mk, 'nk, ('x, 'xs) cons) hgt

    type (_, _, _) ends =
      | Ends :
          'l Endpoints.len * ('mk, 'n, 'bs, 'hs) C.Heter.hgts * ('hs, 'l) Bwv.Heter.ht
          -> ('mk, 'n, 'bs) ends

    let rec ends : type m k mk n bs. (m, k D.suc, mk D.suc, n D.suc, bs) hgt -> (mk, n, bs) ends =
     fun xss ->
      match xss with
      | [] ->
          let (Wrap l) = Endpoints.wrapped () in
          Ends (l, Nil, [])
      | Branch (l1, es, _) :: xs ->
          let (Ends (l2, hs, ess)) = ends xs in
          let Eq = Endpoints.uniq l1 l2 in
          Ends (l2, Cons hs, es :: ess)

    let rec mid : type m k mk n bs.
        (m, k D.suc, mk D.suc, n D.suc, bs) hgt -> (m, k, mk, n D.suc, bs) hgt = function
      | [] -> []
      | Branch (_, _, m) :: xs -> m :: mid xs

    let rec leaf : type n nk bs. n D.t -> bs Tlist.t -> (n, D.zero, n, nk, bs) hgt =
     fun n bs ->
      match bs with
      | Nil -> []
      | Cons bs -> Leaf n :: leaf n bs

    let rec branch : type m k mk n bs hs l.
        l Endpoints.len ->
        (mk, n, bs, hs) C.Heter.hgts ->
        (hs, l) Bwv.Heter.ht ->
        (m, k, mk, n D.suc, bs) hgt ->
        (m, k D.suc, mk D.suc, n D.suc, bs) hgt =
     fun l hs endss mids ->
      match (hs, endss, mids) with
      | Nil, [], [] -> []
      | Cons hs, ends :: endss, mid :: mids -> Branch (l, ends, mid) :: branch l hs endss mids
  end

  module Infix = C.Infix

  (* Now the generic traversal.  This appears to require *three* helper functions, corresponding to three stages of where we are in the instantiated or uninstantiated dimensions. *)

  module Applicatic (M : Applicative.Plain) = struct
    open Applicative.Ops (M)
    module BwvM = Bwv.Applicatic (M)

    type ('n, 'k, 'nk, 'bs, 'cs) pmapperM = {
      map : 'm. ('m, 'n, 'k, 'nk) tface -> ('m, 'bs) C.Heter.hft -> ('m, 'cs) C.Heter.hft M.t;
    }

    let rec gpmapM_ll : type k m mk l1 l2 l ml ml1 b bs cs.
        (m, k, mk) D.plus ->
        (m, l, ml) D.plus ->
        (m, l1, ml1) D.plus ->
        (k, l1, l2, l) bwtface ->
        (ml1, l2, ml, (b, bs) cons, cs) pmapperM ->
        (m, mk, (b, bs) cons) C.Heter.hgt ->
        cs Tlist.t ->
        (m, mk, cs) C.Heter.hgt M.t =
     fun mk ml ml1 d g trs cst ->
      match trs with
      | Leaf _ :: _ ->
          let Eq = D.plus_uniq mk (D.zero_plus (dom_bwtface d)) in
          let Eq = D.plus_uniq ml (D.zero_plus (cod_bwtface d)) in
          let Eq = D.plus_uniq ml1 (D.zero_plus (codl_bwtface d)) in
          let+ x = g.map (tface_of_bw d) (C.Heter.lab trs) in
          C.Heter.leaf x
      | Branch (_, _, _) :: _ ->
          let mk' = D.plus_suc mk in
          let (Suc mk'') = mk' in
          let ml' = D.plus_suc ml in
          let ml1' = D.plus_suc ml1 in
          let (Ends (l, hs, ends)) = C.Heter.ends trs in
          let mid = C.Heter.mid trs in
          let (Hgts newhs) = C.Heter.hgts_of_tlist cst in
          let+ newends =
            BwvM.pmapM
              (fun (e :: brs) ->
                let+ xs =
                  gpmapM_ll mk'' ml' ml1' (LEnd (e, d)) g (C.Heter.hgt_of_hlist hs brs) cst in
                C.Heter.hlist_of_hgt newhs xs)
              (Endpoints.indices l :: ends) (C.Heter.tlist_hgts newhs cst)
          and+ newmid = gpmapM_ll mk' ml' ml1' (LMid d) g mid cst in
          C.Heter.branch l newhs newends newmid

    let rec gpmapM_l : type k m mk l ml b bs cs m1 m2 m2l.
        (m, k, mk) D.plus ->
        (m, l, ml) D.plus ->
        (m1, m2, m) D.plus ->
        (m2, l, m2l) D.plus ->
        (k, D.zero, l, l) bwtface ->
        (m1, m2l, ml, (b, bs) cons, cs) pmapperM ->
        (m, mk, (b, bs) cons) C.Heter.hgt ->
        cs Tlist.t ->
        (m, mk, cs) C.Heter.hgt M.t =
     fun mk ml m12 m2l d g trs cst ->
      match (m12, trs) with
      | Zero, _ ->
          let Eq = D.plus_uniq m2l (D.zero_plus (D.plus_right ml)) in
          gpmapM_ll mk ml Zero d g trs cst
      | Suc m12, Branch (_, _, _) :: _ ->
          let mk' = D.plus_suc mk in
          let (Suc mk'') = mk' in
          let ml' = D.plus_suc ml in
          let m2l' = D.plus_suc m2l in
          let (Ends (l, hs, ends)) = C.Heter.ends trs in
          let mid = C.Heter.mid trs in
          let (Hgts newhs) = C.Heter.hgts_of_tlist cst in
          let+ newends =
            BwvM.pmapM
              (fun (e :: brs) ->
                let+ xs =
                  gpmapM_l mk'' ml' m12 m2l' (bwtface_rend e d) g (C.Heter.hgt_of_hlist hs brs) cst
                in
                C.Heter.hlist_of_hgt newhs xs)
              (Endpoints.indices l :: ends) (C.Heter.tlist_hgts newhs cst)
          and+ newmid = gpmapM_l mk' ml' m12 m2l' (RMid d) g mid cst in
          C.Heter.branch l newhs newends newmid

    let rec gpmapM_r : type n k1 k2 l2 kl nk1 nkl nk b bs cs.
        (n, k1, nk1) D.plus ->
        (k1, l2, kl) D.plus ->
        (nk1, k2, nk) D.plus ->
        (nk1, l2, nkl) D.plus ->
        (k2, l2) bwsface ->
        (n, kl, nkl, (b, bs) cons, cs) pmapperM ->
        (n, k1, nk1, nk, (b, bs) cons) Heter.hgt ->
        cs Tlist.t ->
        (n, k1, nk1, nk, cs) Heter.hgt M.t =
     fun nk1 kl nk12 nkl d g trs cst ->
      match (nk1, trs) with
      | Zero, Leaf n :: _ -> return (Heter.leaf n cst)
      | Suc nk1, Branch (_, _, _) :: _ ->
          let nk12' = D.plus_suc nk12 in
          let (Suc nk12'') = nk12' in
          let (Ends (l, hs, ends)) = Heter.ends trs in
          let mid = Heter.mid trs in
          let (Hgts newhs) = C.Heter.hgts_of_tlist cst in
          let+ newends =
            BwvM.pmapM
              (fun (e :: brs) ->
                let+ xs =
                  gpmapM_l nk12'' (D.plus_suc nkl) nk1 (D.plus_suc kl)
                    (REnd (e, d))
                    g (C.Heter.hgt_of_hlist hs brs) cst in
                C.Heter.hlist_of_hgt newhs xs)
              (Endpoints.indices l :: ends) (C.Heter.tlist_hgts newhs cst)
          and+ newmid = gpmapM_r nk1 (N.plus_suc kl) nk12' (D.plus_suc nkl) (Mid d) g mid cst in
          Heter.branch l newhs newends newmid

    let pmapM : type n k nk b bs cs.
        (n, k, nk, (b, bs) cons, cs) pmapperM ->
        (n, k, nk, nk, (b, bs) cons) Heter.hgt ->
        cs Tlist.t ->
        (n, k, nk, nk, cs) Heter.hgt M.t =
     fun g trs cst ->
      let (tr :: _) = trs in
      let n = uninst tr in
      let k = inst tr in
      let k0 = D.plus_zero k in
      let n_k = plus tr in
      let nk = D.plus_out n n_k in
      let nk0 = D.plus_zero nk in
      gpmapM_r n_k k0 nk0 nk0 Zero g trs cst

    (* And now the more specialized versions. *)

    type ('n, 'k, 'nk, 'bs, 'c) mmapperM = {
      map : 'm. ('m, 'n, 'k, 'nk) tface -> ('m, 'bs) C.Heter.hft -> ('m, 'c) F.t M.t;
    }

    let mmapM : type n k nk b bs c.
        (n, k, nk, (b, bs) cons, c) mmapperM ->
        (n, k, nk, nk, (b, bs) cons) Heter.hgt ->
        (n, k, nk, c) t M.t =
     fun g xs ->
      let+ [ ys ] =
        pmapM
          {
            map =
              (fun fa x ->
                let+ y = g.map fa x in
                y @: []);
          }
          xs (Cons Nil) in
      ys

    type ('n, 'k, 'nk, 'bs) miteratorM = {
      it : 'm. ('m, 'n, 'k, 'nk) tface -> ('m, 'bs) C.Heter.hft -> unit M.t;
    }

    let miterM : type n k nk b bs.
        (n, k, nk, (b, bs) cons) miteratorM -> (n, k, nk, nk, (b, bs) cons) Heter.hgt -> unit M.t =
     fun g xs ->
      let+ [] =
        pmapM
          {
            map =
              (fun fa x ->
                let+ () = g.it fa x in
                hnil);
          }
          xs Nil in
      ()

    (* We also have a monadic builder function *)

    type ('n, 'k, 'nk, 'b) builderM = { build : 'm. ('m, 'n, 'k, 'nk) tface -> ('m, 'b) F.t M.t }

    let rec gbuildM_ll : type k m mk l1 l2 l ml ml1 b.
        m D.t ->
        (m, k, mk) D.plus ->
        (m, l, ml) D.plus ->
        (m, l1, ml1) D.plus ->
        (k, l1, l2, l) bwtface ->
        (ml1, l2, ml, b) builderM ->
        (m, mk, b) C.gt M.t =
     fun m mk ml ml1 d g ->
      match m with
      | Nat Zero ->
          let Eq = D.plus_uniq mk (D.zero_plus (dom_bwtface d)) in
          let Eq = D.plus_uniq ml (D.zero_plus (cod_bwtface d)) in
          let Eq = D.plus_uniq ml1 (D.zero_plus (codl_bwtface d)) in
          let+ x = g.build (tface_of_bw d) in
          C.Leaf x
      | Nat (Suc m) ->
          let mk' = D.plus_suc mk in
          let (Suc mk'') = mk' in
          let ml' = D.plus_suc ml in
          let ml1' = D.plus_suc ml1 in
          let (Wrap l) = Endpoints.wrapped () in
          let+ ends =
            BwvM.mapM
              (fun e -> gbuildM_ll (Nat m) mk'' ml' ml1' (LEnd (e, d)) g)
              (Endpoints.indices l)
          and+ mid = gbuildM_ll (Nat m) mk' ml' ml1' (LMid d) g in
          C.Branch (l, ends, mid)

    let rec gbuildM_l : type k m mk l ml b m1 m2 m2l.
        m D.t ->
        (m, k, mk) D.plus ->
        (m, l, ml) D.plus ->
        (m1, m2, m) D.plus ->
        (m2, l, m2l) D.plus ->
        (k, D.zero, l, l) bwtface ->
        (m1, m2l, ml, b) builderM ->
        (m, mk, b) C.gt M.t =
     fun m mk ml m12 m2l d g ->
      match m12 with
      | Zero ->
          let Eq = D.plus_uniq m2l (D.zero_plus (D.plus_right ml)) in
          gbuildM_ll m mk ml Zero d g
      | Suc m12 ->
          let (Nat (Suc m)) = m in
          let mk' = D.plus_suc mk in
          let (Suc mk'') = mk' in
          let ml' = D.plus_suc ml in
          let m2l' = D.plus_suc m2l in
          let (Wrap l) = Endpoints.wrapped () in
          let+ ends =
            BwvM.mapM
              (fun e -> gbuildM_l (Nat m) mk'' ml' m12 m2l' (bwtface_rend e d) g)
              (Endpoints.indices l)
          and+ mid = gbuildM_l (Nat m) mk' ml' m12 m2l' (RMid d) g in
          C.Branch (l, ends, mid)

    let rec gbuildM_r : type n k1 k2 l2 kl nk1 nkl nk b.
        n D.t ->
        (n, k1, nk1) D.plus ->
        (k1, l2, kl) D.plus ->
        (nk1, k2, nk) D.plus ->
        (nk1, l2, nkl) D.plus ->
        (k2, l2) bwsface ->
        (n, kl, nkl, b) builderM ->
        (n, k1, nk1, nk, b) gt M.t =
     fun n nk1 kl nk12 nkl d g ->
      match nk1 with
      | Zero -> return (Leaf n)
      | Suc nk1 ->
          let nk12' = D.plus_suc nk12 in
          let (Suc nk12'') = nk12' in
          let (Wrap l) = Endpoints.wrapped () in
          let+ ends =
            BwvM.mapM
              (fun e ->
                gbuildM_l (D.plus_out n nk1) nk12'' (D.plus_suc nkl) nk1 (D.plus_suc kl)
                  (REnd (e, d))
                  g)
              (Endpoints.indices l)
          and+ mid = gbuildM_r n nk1 (N.plus_suc kl) nk12' (D.plus_suc nkl) (Mid d) g in
          Branch (l, ends, mid)

    let buildM : type n k nk b.
        n D.t -> (n, k, nk) D.plus -> (n, k, nk, b) builderM -> (n, k, nk, b) t M.t =
     fun n nk g ->
      gbuildM_r n nk
        (D.plus_zero (D.plus_right nk))
        (D.plus_zero (D.plus_out n nk))
        (D.plus_zero (D.plus_out n nk))
        Zero g
  end

  module Monadic (M : Monad.Plain) = struct
    module A = Applicative.OfMonad (M)
    include Applicatic (A)
  end

  (* Now we deduce the non-monadic versions *)

  module IdM = Monadic (Monad.Identity)

  let pmap : type n k nk b bs cs.
      (n, k, nk, (b, bs) cons, cs) IdM.pmapperM ->
      (n, k, nk, nk, (b, bs) cons) Heter.hgt ->
      cs Tlist.t ->
      (n, k, nk, nk, cs) Heter.hgt =
   fun g trs cst -> IdM.pmapM g trs cst

  let mmap : type n k nk b bs c.
      (n, k, nk, (b, bs) cons, c) IdM.mmapperM ->
      (n, k, nk, nk, (b, bs) cons) Heter.hgt ->
      (n, k, nk, c) t =
   fun g xs -> IdM.mmapM g xs

  let miter : type n k nk b bs.
      (n, k, nk, (b, bs) cons) IdM.miteratorM -> (n, k, nk, nk, (b, bs) cons) Heter.hgt -> unit =
   fun g xs -> IdM.miterM g xs

  let build : type n k nk b.
      n D.t -> (n, k, nk) D.plus -> (n, k, nk, b) IdM.builderM -> (n, k, nk, b) t =
   fun n nk g -> IdM.buildM n nk g
end

module TubeOf = struct
  include Tube (FamOf)

  (* We can lift and lower a tube too *)

  let rec glift : type m k mk n1 n2 n12 b.
      (n1, n2, n12) D.plus -> (m, k, mk, n1, b) gt -> (m, k, mk, n12, b) gt =
   fun n12 tr ->
    match tr with
    | Leaf m -> Leaf m
    | Branch (l, ends, mid) ->
        let (Suc n12') = N.plus_suc n12 in
        Branch (l, Bwv.map (fun t -> CubeOf.lift n12' t) ends, glift n12 mid)

  let rec glower : type m k mk n1 n2 n12 l b.
      (mk, l, n1) D.plus -> (n1, n2, n12) D.plus -> (m, k, mk, n12, b) gt -> (m, k, mk, n1, b) gt =
   fun mk n12 tr ->
    match (tr, n12) with
    | Leaf m, _ -> Leaf m
    | _, Zero -> tr
    | Branch (l, ends, mid), Suc n12' ->
        let mk' = N.plus_suc mk in
        let (Suc mk'') = mk' in
        Branch (l, Bwv.map (fun t -> CubeOf.lower mk'' (N.plus_suc n12') t) ends, glower mk' n12 mid)

  (* We can fill in the missing pieces of a tube with a cube, yielding a cube. *)

  let rec gplus_gcube : type n m l ml b. (m, l, ml, n, b) gt -> (m, n, b) C.gt -> (ml, n, b) C.gt =
   fun tl tm ->
    match tl with
    | Leaf _ -> tm
    | Branch (l, ends, mid) -> Branch (l, ends, gplus_gcube mid tm)

  let plus_cube : type m l ml b. (m, l, ml, b) t -> (m, b) C.t -> (ml, b) C.t =
   fun tl tm ->
    let ml = gplus tl in
    gplus_gcube tl (CubeOf.lift ml tm)

  (* Or we can fill in some of those missing pieces with a tube instead, yielding another tube. *)

  let rec gplus_gtube : type n m k mk l kl mkl b.
      (k, l, kl) D.plus -> (mk, l, mkl, n, b) gt -> (m, k, mk, n, b) gt -> (m, kl, mkl, n, b) gt =
   fun kl tl tk ->
    match (kl, tl) with
    | Zero, Leaf _ -> tk
    | Suc kl, Branch (l, ends, mid) -> Branch (l, ends, gplus_gtube kl mid tk)

  let plus_tube : type m k mk l kl mkl b.
      (k, l, kl) D.plus -> (mk, l, mkl, b) t -> (m, k, mk, b) t -> (m, kl, mkl, b) t =
   fun kl tl tk ->
    let mk_l = gplus tl in
    gplus_gtube kl tl (glift mk_l tk)

  (* We can also pick out a lower-dimensional part around the middle of a tube. *)

  let rec gmiddle : type m k mk l kl mkl n b.
      (m, k, mk) D.plus -> (k, l, kl) D.plus -> (m, kl, mkl, n, b) gt -> (m, k, mk, n, b) gt =
   fun mk kl tr ->
    match (kl, tr) with
    | Zero, _ ->
        let Eq = D.plus_uniq mk (gplus tr) in
        tr
    | Suc kl, Branch (_, _, mid) -> gmiddle mk kl mid

  let middle : type m k mk l kl mkl b.
      (m, k, mk) D.plus -> (k, l, kl) D.plus -> (m, kl, mkl, b) t -> (m, k, mk, b) t =
   fun mk kl tr ->
    let mk_l = D.plus_assocl mk kl (plus tr) in
    glower Zero mk_l (gmiddle mk kl tr)

  (* Append the elements of a tube, in order, to a given Bwd.t. *)

  let append_bwd : type a m n mn. a Bwd.t -> (m, n, mn, a) t -> a Bwd.t =
   fun start xs ->
    let module S = struct
      type t = a Bwd.t
    end in
    let module M = Monad.State (S) in
    let open Monadic (M) in
    let (), xs = miterM { it = (fun _ [ x ] xs -> ((), Snoc (xs, x))) } [ xs ] start in
    xs
end
