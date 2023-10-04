(* This module is not meant to be opened; its sub-modules should be used qualified. *)
module GList = List

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

(* The error monad *)

module type Error_type = sig
  type t
end

module Error (E : Error_type) = struct
  type 'a t = ('a, E.t) result

  let return = Result.ok
  let bind = Result.bind
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
  include Zero

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

(* StateT inherits plus *)

module StateTPlus (M : Plus) (S : State_type) = struct
  include StateT (M) (S)

  let mzero : 'a t = fun _ -> M.mzero
  let mplus : 'a t -> 'a t -> 'a t = fun x y s -> M.mplus (x s) (y s)
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

(* The free monad with choice.  This is just for fun; it's way too slow to do anything with. *)
module FreeChoice = struct
  type 'a t = From : 'a t list -> 'a t | Return : 'a -> 'a t | Mult : 'a t t -> 'a t

  let return : type a. a -> a t = fun x -> Return x
  let mzero : type a. a t = From []
  let mplus : type a. a t -> a t -> a t = fun xs ys -> From [ xs; ys ]

  let rec map : type a b. (a -> b) -> a t -> b t =
   fun f -> function
    | From xs -> From (GList.map (map f) xs)
    | Return x -> Return (f x)
    | Mult xs -> Mult (map (map f) xs)

  let bind : type a b. a t -> (a -> b t) -> b t = fun xs f -> Mult (map f xs)

  let rec find_map : type a b. (a -> b option) -> a t -> b option =
   fun f -> function
    | From xs -> GList.find_map (find_map f) xs
    | Return x -> f x
    | Mult xs -> find_map (find_map f) xs

  let rec first : type a. a t -> a option = function
    | From xs -> GList.find_map first xs
    | Return x -> Some x
    | Mult xs -> find_map first xs
end
