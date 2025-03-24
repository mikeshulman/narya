open Signatures
open Tlist

(* A "tuple" is an intrinsically well-typed *total* map whose keys are insertions into some (backwards) nat, and whose values are parametrized by the result of removing that inserted element. *)

module Make (F : Fam2) : sig
  type ('a, 'b, 'p) gt
  type ('a, 'p) t = ('a, Fwn.zero, 'p) gt

  val empty : (N.zero, 'p) t
  val find : ('a, 'asuc) N.insert -> ('asuc, 'p) t -> ('a, 'p) F.t
  val set : ('a, 'asuc) N.insert -> ('a, 'p) F.t -> ('asuc, 'p) t -> ('asuc, 'p) t

  val update :
    ('a, 'asuc) N.insert -> (('a, 'p) F.t -> ('a, 'p) F.t) -> ('asuc, 'p) t -> ('asuc, 'p) t

  type ('asuc, 'p) builder = { build : 'a. ('a, 'asuc) N.insert -> ('a, 'p) F.t }

  val build : 'a N.t -> ('a, 'p) builder -> ('a, 'p) t

  module Heter : sig
    type (_, _) hft =
      | [] : ('a, nil) hft
      | ( :: ) : ('a, 'p) F.t * ('a, 'ps) hft -> ('a, ('p, 'ps) cons) hft

    type (_, _, _) hgt =
      | [] : ('a, 'b, nil) hgt
      | ( :: ) : ('a, 'b, 'p) gt * ('a, 'b, 'ps) hgt -> ('a, 'b, ('p, 'ps) cons) hgt
  end

  module Applicatic (M : Applicative.Plain) : sig
    type ('asuc, 'ps, 'qs) pmapperM = {
      map : 'a. ('a, 'asuc) N.insert -> ('a, 'ps) Heter.hft -> ('a, 'qs) Heter.hft M.t;
    }

    val pmapM :
      ('a, ('p, 'ps) cons, 'qs) pmapperM ->
      ('a, Fwn.zero, ('p, 'ps) cons) Heter.hgt ->
      'qs Tlist.t ->
      ('a, Fwn.zero, 'qs) Heter.hgt M.t

    type ('asuc, 'ps, 'q) mmapperM = {
      map : 'a. ('a, 'asuc) N.insert -> ('a, 'ps) Heter.hft -> ('a, 'q) F.t M.t;
    }

    val mmapM :
      ('a, ('p, 'ps) cons, 'q) mmapperM ->
      ('a, Fwn.zero, ('p, 'ps) cons) Heter.hgt ->
      ('a, Fwn.zero, 'q) gt M.t

    type ('asuc, 'ps) miteratorM = {
      it : 'a. ('a, 'asuc) N.insert -> ('a, 'ps) Heter.hft -> unit M.t;
    }

    val miterM :
      ('a, ('p, 'ps) cons) miteratorM -> ('a, Fwn.zero, ('p, 'ps) cons) Heter.hgt -> unit M.t
  end

  module Monadic (M : Monad.Plain) : sig
    module A : module type of Applicative.OfMonad (M)
    include module type of Applicatic (A)
  end

  module IdM : module type of Monadic (Monad.Identity)

  val pmap :
    ('a, ('p, 'ps) cons, 'qs) IdM.pmapperM ->
    ('a, Fwn.zero, ('p, 'ps) cons) Heter.hgt ->
    'qs Tlist.t ->
    ('a, Fwn.zero, 'qs) Heter.hgt

  val mmap :
    ('a, ('p, 'ps) cons, 'q) IdM.mmapperM ->
    ('a, Fwn.zero, ('p, 'ps) cons) Heter.hgt ->
    ('a, Fwn.zero, 'q) gt

  val miter :
    ('a, ('p, 'ps) cons) IdM.miteratorM -> ('a, Fwn.zero, ('p, 'ps) cons) Heter.hgt -> unit
end = struct
  (* The intermediate pieces of such a map are additionally parametrized by a forwards nat 'b that is to be added on the right to produce the true "outer" parameter. *)
  type (_, _, _) gt =
    | Emp : (N.zero, 'b, 'p) gt
    | Map : {
        now : ('a, 'b, 'ab) Fwn.bplus * ('ab, 'p) F.t;
        later : ('a, 'b Fwn.suc, 'p) gt;
      }
        -> ('a N.suc, 'b, 'p) gt

  type ('a, 'p) t = ('a, Fwn.zero, 'p) gt

  let empty : type b p. (N.zero, b, p) gt = Emp

  let rec gfind : type a asuc b ab p.
      (a, asuc) N.insert -> (asuc, b, p) gt -> (a, b, ab) Fwn.bplus -> (ab, p) F.t =
   fun i m ab ->
    match i with
    | Now ->
        let (Map { now = ab', v; _ }) = m in
        let Eq = Fwn.bplus_uniq ab ab' in
        v
    | Later i ->
        let (Map { later; _ }) = m in
        gfind i later (Suc ab)

  let find : type a asuc p. (a, asuc) N.insert -> (asuc, p) t -> (a, p) F.t =
   fun i m -> gfind i m Zero

  let rec gset : type a asuc b ab p.
      (a, asuc) N.insert ->
      (ab, p) F.t ->
      (asuc, b, p) gt ->
      (a, b, ab) Fwn.bplus ->
      (asuc, b, p) gt =
   fun i v m ab ->
    match i with
    | Now ->
        let (Map { now = ab', _; later }) = m in
        let Eq = Fwn.bplus_uniq ab ab' in
        Map { now = (ab', v); later }
    | Later i ->
        let (Map { later; now }) = m in
        Map { later = gset i v later (Suc ab); now }

  let set : type a asuc p. (a, asuc) N.insert -> (a, p) F.t -> (asuc, p) t -> (asuc, p) t =
   fun i v m -> gset i v m Zero

  let rec gupdate : type a asuc b ab p.
      (a, asuc) N.insert ->
      ((ab, p) F.t -> (ab, p) F.t) ->
      (asuc, b, p) gt ->
      (a, b, ab) Fwn.bplus ->
      (asuc, b, p) gt =
   fun i f m ab ->
    match i with
    | Now ->
        let (Map { now = ab', v; later }) = m in
        let Eq = Fwn.bplus_uniq ab ab' in
        Map { now = (ab', f v); later }
    | Later i ->
        let (Map { later; now }) = m in
        Map { later = gupdate i f later (Suc ab); now }

  let update : type a asuc p.
      (a, asuc) N.insert -> ((a, p) F.t -> (a, p) F.t) -> (asuc, p) t -> (asuc, p) t =
   fun i f m -> gupdate i f m Zero

  type ('asuc, 'p) builder = { build : 'a. ('a, 'asuc) N.insert -> ('a, 'p) F.t }

  let rec gbuild : type a b ab p. a N.t -> (a, b, ab) Fwn.bplus -> (ab, p) builder -> (a, b, p) gt =
   fun a ab builder ->
    match a with
    | Nat Zero -> Emp
    | Nat (Suc a) ->
        let (Bplus ab') = Fwn.bplus (Fwn.bplus_right ab) in
        Map
          {
            now = (ab', builder.build (Fwn.insert_bplus Now ab' ab));
            later = gbuild (Nat a) (Suc ab) builder;
          }

  let build : type a p. a N.t -> (a, p) builder -> (a, p) t = fun a builder -> gbuild a Zero builder

  (* Generic traversal *)

  module Heter = struct
    type (_, _) hft =
      | [] : ('a, nil) hft
      | ( :: ) : ('a, 'p) F.t * ('a, 'ps) hft -> ('a, ('p, 'ps) cons) hft

    type (_, _, _) hgt =
      | [] : ('a, 'b, nil) hgt
      | ( :: ) : ('a, 'b, 'p) gt * ('a, 'b, 'ps) hgt -> ('a, 'b, ('p, 'ps) cons) hgt

    let rec emp : type b ps. ps Tlist.t -> (N.zero, b, ps) hgt = function
      | Nil -> []
      | Cons ps -> Emp :: emp ps

    let rec map : type a b ab ps.
        (a, b, ab) Fwn.bplus -> (ab, ps) hft -> (a, b Fwn.suc, ps) hgt -> (a N.suc, b, ps) hgt =
     fun ab nows laters ->
      match (nows, laters) with
      | [], [] -> []
      | now :: nows, later :: laters -> Map { now = (ab, now); later } :: map ab nows laters

    let rec now : type a b ab ps. (a, b, ab) Fwn.bplus -> (a N.suc, b, ps) hgt -> (ab, ps) hft =
     fun ab m ->
      match m with
      | [] -> []
      | Map { now = ab', n; _ } :: ms ->
          let Eq = Fwn.bplus_uniq ab ab' in
          n :: now ab ms

    let rec later : type a b ps. (a N.suc, b, ps) hgt -> (a, b Fwn.suc, ps) hgt = function
      | [] -> []
      | Map { later = l; _ } :: ms -> l :: later ms
  end

  (* OCaml can't always tell from context what [x ; xs] should be; in particular it often fails to notice hfts.  So we also give a different syntax that is unambiguous.  *)
  module Infix = struct
    let hnil : type n. (n, nil) Heter.hft = []

    let ( @: ) : type n x xs. (n, x) F.t -> (n, xs) Heter.hft -> (n, (x, xs) cons) Heter.hft =
     fun x xs -> x :: xs
  end

  open Infix

  module Applicatic (M : Applicative.Plain) = struct
    open Applicative.Ops (M)

    type ('asuc, 'ps, 'qs) pmapperM = {
      map : 'a. ('a, 'asuc) N.insert -> ('a, 'ps) Heter.hft -> ('a, 'qs) Heter.hft M.t;
    }

    let rec gpmapM : type a b ab p ps qs.
        (a, b, ab) Fwn.bplus ->
        (ab, (p, ps) cons, qs) pmapperM ->
        (a, b, (p, ps) cons) Heter.hgt ->
        qs Tlist.t ->
        (a, b, qs) Heter.hgt M.t =
     fun ab f mss qs ->
      match mss with
      | Emp :: _ -> return (Heter.emp qs)
      | Map { now = ab', v; later } :: mss ->
          let+ fnow = f.map (Fwn.insert_bplus Now ab' ab) (v :: Heter.now ab' mss)
          and+ flater = gpmapM (Suc ab) f (later :: Heter.later mss) qs in
          Heter.map ab' fnow flater

    let pmapM : type a p ps qs.
        (a, (p, ps) cons, qs) pmapperM ->
        (a, Fwn.zero, (p, ps) cons) Heter.hgt ->
        qs Tlist.t ->
        (a, Fwn.zero, qs) Heter.hgt M.t =
     fun f mss qs -> gpmapM Zero f mss qs

    type ('asuc, 'ps, 'q) mmapperM = {
      map : 'a. ('a, 'asuc) N.insert -> ('a, 'ps) Heter.hft -> ('a, 'q) F.t M.t;
    }

    let mmapM : type a p ps q.
        (a, (p, ps) cons, q) mmapperM ->
        (a, Fwn.zero, (p, ps) cons) Heter.hgt ->
        (a, Fwn.zero, q) gt M.t =
     fun f xs ->
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

    type ('asuc, 'ps) miteratorM = {
      it : 'a. ('a, 'asuc) N.insert -> ('a, 'ps) Heter.hft -> unit M.t;
    }

    let miterM : type a p ps.
        (a, (p, ps) cons) miteratorM -> (a, Fwn.zero, (p, ps) cons) Heter.hgt -> unit M.t =
     fun f xs ->
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
