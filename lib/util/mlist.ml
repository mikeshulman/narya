(* This is just a demonstration, in the simple case of lists, of a technique for unifying tranversals of data structures.  We use it later in more complicated cases of Bwvs, Cubes, and Tubes. *)

open Tlist
open Hlist

module Heter = struct
  (* An hlist of lists *)
  type _ ht = [] : nil ht | ( :: ) : 'x list * 'xs ht -> ('x, 'xs) cons ht

  (* The hlist consisting of all empty lists  *)
  let rec empty : type xs. xs Tlist.t -> xs ht = function
    | Nil -> []
    | Cons xs -> [] :: empty xs

  (* Add an element to the front of each one of an hlist of lists *)
  let rec cons : type xs. xs hlist -> xs ht -> xs ht =
   fun x xs ->
    match (x, xs) with
    | [], [] -> []
    | x :: xs, y :: ys -> (x :: y) :: cons xs ys

  (* Extract the head and tail of element of every one of an hlist of lists *)

  let rec hd : type xs. xs ht -> xs hlist = function
    | [] -> []
    | x :: xs -> List.hd x :: hd xs

  let rec tl : type xs. xs ht -> xs ht = function
    | [] -> []
    | x :: xs -> List.tl x :: tl xs

  (* Every hlist of lists has a valid type *)
  let rec tlist : type xs. xs ht -> xs Tlist.t = function
    | [] -> Nil
    | _ :: xs -> Cons (tlist xs)
end

(* Now we define a single traversal function which encapsulates map, map2, map3, ..., iter, iter2, ... mapM, mapM2, ..., iterM, iterM2, ... and also multiple-output versions and left and right folds.  It takes a nonempty hlist of lists as input and produces an hlist of lists in some applicative functor as output, where the traversal function acts on hlists of elements.  Applicative functors are the natural level of generality for this, and are needed for some esoteric applications like right-fold with simultaneous map, but later we specialize it to monads which include most examples.  *)

module Applicatic (M : Applicative.Plain) = struct
  open Applicative.Ops (M)

  let rec pmapM : type x xs ys.
      ((x, xs) cons hlist -> ys hlist M.t) -> (x, xs) cons Heter.ht -> ys Tlist.t -> ys Heter.ht M.t
      =
   fun f xss ys ->
    match xss with
    | [] :: _ -> return (Heter.empty ys)
    | (x :: xs) :: xss ->
        let+ fx = f (x :: Heter.hd xss) and+ fxs = pmapM f (xs :: Heter.tl xss) ys in
        Heter.cons fx fxs

  (* Since "nil hlist" is isomorphic to unit, this includes iterations, but it's more convenient to write those actually using unit. *)
  let miterM : type x xs. ((x, xs) cons hlist -> unit M.t) -> (x, xs) cons Heter.ht -> unit M.t =
   fun f xss ->
    let+ [] =
      pmapM
        (fun x ->
          let+ () = f x in
          [])
        xss Nil in
    ()

  (* It's also convenient to separate out the multi-input single-output version. *)
  let mmapM : type x xs y. ((x, xs) cons hlist -> y M.t) -> (x, xs) cons Heter.ht -> y list M.t =
   fun f xs ->
    let+ [ ys ] =
      pmapM
        (fun x ->
          let+ y = f x in
          [ y ])
        xs (Cons Nil) in
    ys
end

module Monadic (M : Monad.Plain) = struct
  module A = Applicative.OfMonad (M)
  include Applicatic (A)
end

(* The non-monadic versions just specialize to the identity. *)
let pmap : type x xs ys.
    ((x, xs) cons hlist -> ys hlist) -> (x, xs) cons Heter.ht -> ys Tlist.t -> ys Heter.ht =
 fun f xss ys ->
  let open Monadic (Monad.Identity) in
  pmapM f xss ys

let miter : type x xs. ((x, xs) cons hlist -> unit) -> (x, xs) cons Heter.ht -> unit =
 fun f xss ->
  let open Monadic (Monad.Identity) in
  miterM f xss

let mmap : type x xs y. ((x, xs) cons hlist -> y) -> (x, xs) cons Heter.ht -> y list =
 fun f xs ->
  let open Monadic (Monad.Identity) in
  mmapM f xs

(* Ordinary ones of fixed arity are then obtained by specializing to different kinds of hlists.  Note that with hlists, the type determines how many elements it has, so a match against a list of fixed length is exhaustive.  Note that the definitions of these are so simple that the user can easily write them directly, and the same is true for the monadic versions mapM, mapM2, etc.  In practice, I actually prefer that, so the user has a standard syntax. *)

module Examples = struct
  let map : type x y. (x -> y) -> x list -> y list = fun f xs -> mmap (fun [ x ] -> f x) [ xs ]

  let map2 : type x y z. (x -> y -> z) -> x list -> y list -> z list =
   fun f xs ys -> mmap (fun [ x; y ] -> f x y) [ xs; ys ]

  let iter : type x. (x -> unit) -> x list -> unit = fun f xs -> miter (fun [ x ] -> f x) [ xs ]

  let iter2 : type x y. (x -> y -> unit) -> x list -> y list -> unit =
   fun f xs ys -> miter (fun [ x; y ] -> f x y) [ xs; ys ]

  (* Not only does this save copy-and-pasting, especially for data structures whose traversal is complicated to code, it also allows the user to instantiate higher-arity versions as needed by calling mmap directly.  It also includes multiple-output versions that are less commonly mentioned, with a bit of mediation between hlists and tuples: *)

  let map1_2 : type x y z. (x -> y * z) -> x list -> y list * z list =
   fun f xs ->
    let [ ys; zs ] =
      pmap
        (fun [ x ] ->
          let y, z = f x in
          [ y; z ])
        [ xs ] (Cons (Cons Nil)) in
    (ys, zs)

  (* The same is true for the monadic versions.  Moreover, the monadic iteration also incorporates left and right folds, by instantiating to a state monad for left folds, and a reverse state applicative functor (or a continuation monad) for right folds.  Again, in practice this is unnecessary; the user can just instantiate to the appropriate monad directly. *)

  let mfold_left : type x xs acc.
      (acc -> (x, xs) cons hlist -> acc) -> acc -> (x, xs) cons Heter.ht -> acc =
   fun f acc xss ->
    let open Monadic (Monad.State (struct
      type t = acc
    end)) in
    snd (miterM (fun xs s -> ((), f s xs)) xss acc)

  let fold_left : type x acc. (acc -> x -> acc) -> acc -> x list -> acc =
   fun f acc xs -> mfold_left (fun acc [ x ] -> f acc x) acc [ xs ]

  let fold_left2 : type x y acc. (acc -> x -> y -> acc) -> acc -> x list -> y list -> acc =
   fun f acc xs ys -> mfold_left (fun acc [ x; y ] -> f acc x y) acc [ xs; ys ]

  let mfold_right : type x xs acc.
      ((x, xs) cons hlist -> acc -> acc) -> (x, xs) cons Heter.ht -> acc -> acc =
   fun f xss acc ->
    let open Applicatic (Applicative.RevState (struct
      type t = acc
    end)) in
    snd (miterM (fun xs s -> ((), f xs s)) xss acc)

  let mfold_right' : type x xs acc.
      ((x, xs) cons hlist -> acc -> acc) -> (x, xs) cons Heter.ht -> acc -> acc =
   fun f xss acc ->
    let open Monadic (Monad.Cont (struct
      type t = acc
    end)) in
    miterM (fun xs cont -> f xs (cont ())) xss (fun () -> acc)

  let fold_right : type x acc. (x -> acc -> acc) -> x list -> acc -> acc =
   fun f xs acc -> mfold_right (fun [ x ] acc -> f x acc) [ xs ] acc

  let fold_right2 : type x y acc. (x -> y -> acc -> acc) -> x list -> y list -> acc -> acc =
   fun f xs ys acc -> mfold_right (fun [ x; y ] acc -> f x y acc) [ xs; ys ] acc

  (* The reverse-state version of this has the additional advantage that, like the forwards state version, it can be combined with a simultaneous map.  Thus, the generic traversal parametrized over an applicative functor allows the caller to specify the *direction* of traversal. *)
  let fold_right_map : type x y acc. (x -> acc -> y * acc) -> x list -> acc -> y list * acc =
   fun f xss acc ->
    let open Applicatic (Applicative.RevState (struct
      type t = acc
    end)) in
    mmapM (fun [ xs ] s -> f xs s) [ xss ] acc
end
