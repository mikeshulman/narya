(* This module is not meant to be opened; its sub-modules should be used qualified. *)

(* open Bwd *)

(* Plain monads *)

module type Plain = sig
  type 'a t

  val return : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
end

module Ops (M : Plain) = struct
  let return = M.return
  let ( let* ) = M.bind
  let ( >> ) x y = M.bind x (fun _ -> y)

  let liftM (f : 'a -> 'b) (mx : 'a M.t) : 'b M.t =
    let* x = mx in
    return (f x)

  let rec mapM (f : 'a -> 'b M.t) (xs : 'a list) : 'b list M.t =
    match xs with
    | [] -> return []
    | x :: xs ->
        let* fx = f x in
        let* frest = mapM f xs in
        return (fx :: frest)

  let rec bwv_mapM : type a b n. (a -> b M.t) -> (a, n) Bwv.t -> (b, n) Bwv.t M.t =
   fun f xs ->
    match xs with
    | Emp -> return Bwv.Emp
    | Snoc (xs, x) ->
        let* frest = bwv_mapM f xs in
        let* fx = f x in
        return (Bwv.Snoc (frest, fx))

  let option_mapM (f : 'a -> 'b M.t) : 'a option -> 'b option M.t = function
    | Some x ->
        let* fx = f x in
        return (Some fx)
    | None -> return None

  let rec list_fold_leftM (f : 'a -> 'b -> 'a M.t) (start : 'a M.t) (xs : 'b list) : 'a M.t =
    match xs with
    | [] -> start
    | x :: xs ->
        let* s = start in
        list_fold_leftM f (f s x) xs

  let rec list_fold_rightM (f : 'a -> 'b -> 'b M.t) (xs : 'a list) (start : 'b M.t) : 'b M.t =
    match xs with
    | [] -> start
    | x :: xs ->
        let* rest = list_fold_rightM f xs start in
        f x rest

  (* let queue_fold_leftM (f : 'a -> 'b -> 'a M.t) (start : 'a M.t) ((qout, qin) : 'b Queue.t) : 'a M.t = *)
  (*   list_fold_rightM (fun x y -> f y x) qin (list_fold_leftM f start qout) *)

  (* let queue_fold_right (f : 'a -> 'b -> 'b M.t) ((qout, qin) : 'a Queue.t) (start : 'b M.t) : 'b M.t = *)
  (*   list_fold_rightM f qout (list_fold_leftM (fun x y -> f y x) start qin) *)

  let rec mapM2 (f : 'a -> 'b -> 'c M.t) (xs : 'a list) (ys : 'b list) : 'c list M.t =
    match (xs, ys) with
    | [], [] -> return []
    | x :: xs, y :: ys ->
        let* fxy = f x y in
        let* frest = mapM2 f xs ys in
        return (fxy :: frest)
    | _, _ -> raise (Invalid_argument "mapM2: lists are of different lengths")

  let rec bwv_mapM2 :
      type a b c n. (a -> b -> c M.t) -> (a, n) Bwv.t -> (b, n) Bwv.t -> (c, n) Bwv.t M.t =
   fun f xs ys ->
    match (xs, ys) with
    | Bwv.Emp, Bwv.Emp -> return Bwv.Emp
    | Snoc (xs, x), Snoc (ys, y) ->
        let* frest = bwv_mapM2 f xs ys in
        let* fxy = f x y in
        return (Bwv.Snoc (frest, fxy))

  let rec bwv_mapM3 :
      type a b c d n.
      (a -> b -> c -> d M.t) -> (a, n) Bwv.t -> (b, n) Bwv.t -> (c, n) Bwv.t -> (d, n) Bwv.t M.t =
   fun f xs ys zs ->
    match (xs, ys, zs) with
    | Bwv.Emp, Bwv.Emp, Bwv.Emp -> return Bwv.Emp
    | Snoc (xs, x), Snoc (ys, y), Snoc (zs, z) ->
        let* frest = bwv_mapM3 f xs ys zs in
        let* fxy = f x y z in
        return (Bwv.Snoc (frest, fxy))

  let rec bwv_mapM3_2 :
      type a b c d e n.
      (a -> b -> c -> (d * e) M.t) ->
      (a, n) Bwv.t ->
      (b, n) Bwv.t ->
      (c, n) Bwv.t ->
      ((d, n) Bwv.t * (e, n) Bwv.t) M.t =
   fun f xs ys zs ->
    match (xs, ys, zs) with
    | Bwv.Emp, Bwv.Emp, Bwv.Emp -> return (Bwv.Emp, Bwv.Emp)
    | Snoc (xs, x), Snoc (ys, y), Snoc (zs, z) ->
        let* frest1, frest2 = bwv_mapM3_2 f xs ys zs in
        let* fxy1, fxy2 = f x y z in
        return (Bwv.Snoc (frest1, fxy1), Bwv.Snoc (frest2, fxy2))

  let rec bwv_mapM3_plus :
      type a b c d m n mn.
      (m, n, mn) N.plus ->
      (a -> b -> c -> d M.t) ->
      (a, mn) Bwv.t ->
      (b, mn) Bwv.t ->
      (c, m) Bwv.t ->
      (d, m) Bwv.t M.t =
   fun mn f xs ys zs ->
    match mn with
    | Zero -> bwv_mapM3 f xs ys zs
    | Suc mn -> (
        match (xs, ys) with
        | Snoc (xs, _), Snoc (ys, _) -> bwv_mapM3_plus mn f xs ys zs)

  let rec bwv_mapM3_2_plus :
      type a b c d e m n mn.
      (m, n, mn) N.plus ->
      (a -> b -> c -> (d * e) M.t) ->
      (a, mn) Bwv.t ->
      (b, mn) Bwv.t ->
      (c, m) Bwv.t ->
      ((d, m) Bwv.t * (e, m) Bwv.t) M.t =
   fun mn f xs ys zs ->
    match mn with
    | Zero -> bwv_mapM3_2 f xs ys zs
    | Suc mn -> (
        match (xs, ys) with
        | Snoc (xs, _), Snoc (ys, _) -> bwv_mapM3_2_plus mn f xs ys zs)

  let rec iterM (f : 'a -> unit M.t) (xs : 'a list) : unit M.t =
    match xs with
    | [] -> return ()
    | x :: xs ->
        let* _ = f x in
        iterM f xs

  let rec bwv_iterM : type a n. (a -> unit M.t) -> (a, n) Bwv.t -> unit M.t =
   fun f xs ->
    match xs with
    | Emp -> return ()
    | Snoc (xs, x) ->
        let* () = bwv_iterM f xs in
        f x

  let rec iterM2 (f : 'a -> 'b -> unit M.t) (xs : 'a list) (ys : 'b list) : unit M.t =
    match (xs, ys) with
    | [], [] -> return ()
    | x :: xs, y :: ys ->
        let* _ = f x y in
        iterM2 f xs ys
    | _, _ -> raise (Invalid_argument "iterM2: lists are of different lengths")

  let rec bwv_iterM2 : type a b n. (a -> b -> unit M.t) -> (a, n) Bwv.t -> (b, n) Bwv.t -> unit M.t
      =
   fun f xs ys ->
    match (xs, ys) with
    | Emp, Emp -> return ()
    | Snoc (xs, x), Snoc (ys, y) ->
        let* () = bwv_iterM2 f xs ys in
        f x y

  let rec bwv_iterM2_plus :
      type a b m n mn.
      (m, n, mn) N.plus -> (a -> b -> unit M.t) -> (a, mn) Bwv.t -> (b, m) Bwv.t -> unit M.t =
   fun mn f xs ys ->
    match mn with
    | Zero -> bwv_iterM2 f xs ys
    | Suc mn -> (
        match xs with
        | Snoc (xs, _) -> bwv_iterM2_plus mn f xs ys)

  let rec iterM3 (f : 'a -> 'b -> 'c -> unit M.t) (xs : 'a list) (ys : 'b list) (zs : 'c list) :
      unit M.t =
    match (xs, ys, zs) with
    | [], [], [] -> return ()
    | x :: xs, y :: ys, z :: zs ->
        let* _ = f x y z in
        iterM3 f xs ys zs
    | _, _, _ -> raise (Invalid_argument "iterM3: lists are of different lengths")

  let rec bwv_iterM3 :
      type a b c n.
      (a -> b -> c -> unit M.t) -> (a, n) Bwv.t -> (b, n) Bwv.t -> (c, n) Bwv.t -> unit M.t =
   fun f xs ys zs ->
    match (xs, ys, zs) with
    | Emp, Emp, Emp -> return ()
    | Snoc (xs, x), Snoc (ys, y), Snoc (zs, z) ->
        let* () = bwv_iterM3 f xs ys zs in
        f x y z

  let rec bwv_iterM3_plus :
      type a b c m n mn.
      (m, n, mn) N.plus ->
      (a -> b -> c -> unit M.t) ->
      (a, mn) Bwv.t ->
      (b, mn) Bwv.t ->
      (c, m) Bwv.t ->
      unit M.t =
   fun mn f xs ys zs ->
    match mn with
    | Zero -> bwv_iterM3 f xs ys zs
    | Suc mn -> (
        match (xs, ys) with
        | Snoc (xs, _), Snoc (ys, _) -> bwv_iterM3_plus mn f xs ys zs)
end

(* The state monad *)

module type State_type = sig
  type t
end

module State (S : State_type) = struct
  type 'a t = S.t -> 'a * S.t

  let return (x : 'a) : 'a t = fun s -> (x, s)

  let bind (a : 'a t) (f : 'a -> 'b t) : 'b t =
   fun s ->
    let b, s = a s in
    f b s

  let run (f : 'a t) (s : S.t) : 'a = fst (f s)
  let get : S.t t = fun s -> (s, s)
  let put (s : S.t) : unit t = fun _ -> ((), s)
  let save (f : 'a t) : 'a t = fun s -> (fst (f s), s)
end

module type Zero = sig
  include Plain

  val mzero : 'a t
end

module ZeroOps (M : Zero) = struct
  include Ops (M)

  let fail = M.mzero
  let guard b = if b then return () else M.mzero
end

(* The Maybe monad *)

module Maybe = struct
  type 'a t = 'a option

  let return x = Some x
  let bind = Option.bind
  let mzero = None
end

(* Nondeterministic choice monads *)

module type Plus = sig
  include Plain

  val mzero : 'a t
  val mplus : 'a t -> 'a t -> 'a t
end

module PlusOps (M : Plus) = struct
  include Ops (M)

  let fail = M.mzero
  let ( <|> ) = M.mplus
  let guard b = if b then return () else M.mzero

  let rec choose_from = function
    | [] -> fail
    | x :: xs -> return x <|> choose_from xs
end

(* List and Seq monads *)

module List = struct
  type 'a t = 'a list

  let return x = [ x ]
  let bind o f = List.flatten (List.map f o)
  let mzero = []
  let mplus xs ys = xs @ ys
  let force (x : 'a t) : 'a list = x
end

(*
module Bwd = struct
  type 'a t = 'a Bwd.t

  let return x = Snoc (Emp, x)
  let bind o f = Bwd.fold_left (Bwd.fold_left Bwd.snoc) Emp (Bwd.map f o)
end
*)

module Seq = struct
  type 'a t = 'a Seq.t

  let return = Seq.return
  let bind o f = Seq.flat_map f o
  let mzero = Seq.empty
  let mplus = Seq.append
  let force (x : 'a t) : 'a Seq.node = x ()
end

(* A stream is a lazy list, like a Seq but using a Lazy.t rather than a closure.  I'm told this is slower by a constant factor, but it has the advantage of not being recomputed every time it's accessed.  Thus it's good for backtracking computations that can be memoized. *)
module Stream = struct
  type 'a t = 'a node Lazy.t
  and 'a node = Nil | Cons of 'a * 'a t

  let return x = Lazy.from_val (Cons (x, Lazy.from_val Nil))
  let mzero = Lazy.from_val Nil

  let rec mplus xs ys =
    lazy
      (match Lazy.force xs with
      | Nil -> Lazy.force ys
      | Cons (x, xs) -> Cons (x, mplus xs ys))

  let rec bind o f =
    lazy
      (match Lazy.force o with
      | Nil -> Nil
      | Cons (x, xs) -> Lazy.force (mplus (f x) (bind xs f)))

  let force = Lazy.force
end
