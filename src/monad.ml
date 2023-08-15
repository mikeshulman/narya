(* This module is not meant to be opened; its sub-modules should be used qualified. *)

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

  let rec mapM2 (f : 'a -> 'b -> 'c M.t) (xs : 'a list) (ys : 'b list) : 'c list M.t =
    match (xs, ys) with
    | [], [] -> return []
    | x :: xs, y :: ys ->
        let* fxy = f x y in
        let* frest = mapM2 f xs ys in
        return (fxy :: frest)
    | _, _ -> raise (Invalid_argument "mapM2: lists are of different lengths")

  let rec iterM (f : 'a -> unit M.t) (xs : 'a list) : unit M.t =
    match xs with
    | [] -> return ()
    | x :: xs ->
        let* _ = f x in
        iterM f xs

  let rec iterM2 (f : 'a -> 'b -> unit M.t) (xs : 'a list) (ys : 'b list) : unit M.t =
    match (xs, ys) with
    | [], [] -> return ()
    | x :: xs, y :: ys ->
        let* _ = f x y in
        iterM2 f xs ys
    | _, _ -> raise (Invalid_argument "iterM2: lists are of different lengths")

  let rec iterM3 (f : 'a -> 'b -> 'c -> unit M.t) (xs : 'a list) (ys : 'b list) (zs : 'c list) :
      unit M.t =
    match (xs, ys, zs) with
    | [], [], [] -> return ()
    | x :: xs, y :: ys, z :: zs ->
        let* _ = f x y z in
        iterM3 f xs ys zs
    | _, _, _ -> raise (Invalid_argument "iterM3: lists are of different lengths")
end

(* The identity monad *)

module Identity = struct
  type 'a t = 'a

  let return (x : 'a) : 'a t = x
  let bind (a : 'a t) (f : 'a -> 'b t) = f a
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

(* The state monad transformer *)

module StateT (M : Plain) (S : State_type) = struct
  type 'a t = S.t -> ('a * S.t) M.t

  let return (x : 'a) : 'a t = fun s -> M.return (x, s)
  let bind (a : 'a t) (f : 'a -> 'b t) : 'b t = fun s -> M.bind (a s) (fun (b, s) -> f b s)
  let stateless (x : 'a M.t) : 'a t = fun s -> M.bind x (fun x -> M.return (x, s))
  let run (f : 'a t) (s : S.t) : 'a M.t = M.bind (f s) (fun x -> M.return (fst x))
  let get : S.t t = fun s -> M.return (s, s)
  let put (s : S.t) : unit t = fun _ -> M.return ((), s)
  let save (f : 'a t) : 'a t = fun s -> M.bind (f s) (fun (x, _) -> M.return (x, s))
end

(* The continuation-passing monad *)

module type Result_type = sig
  type t
end

module Cont (R : Result_type) = struct
  type 'a t = ('a -> R.t) -> R.t

  let return (x : 'a) : 'a t = fun cont -> cont x
  let bind (a : 'a t) (f : 'a -> 'b t) : 'b t = fun cont -> a (fun x -> f x cont)
end

(* Monads with zero *)

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
open Bwd

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
