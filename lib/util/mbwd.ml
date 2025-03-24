(* Here we instantiate the general traversal technique of Mlist to act on Bwds.  This is more or less a direct transcription.  Note, though, that in contrast to the supplied traversals such as Bwd.map and Bwd.iter, here we traverse a Bwd from LEFT TO RIGHT, following the TEXTUAL ORDER rather than the direction for adding and removing elements. *)

open Bwd
open Tlist
open Hlist

module Heter = struct
  type _ ht = [] : nil ht | ( :: ) : 'x Bwd.t * 'xs ht -> ('x, 'xs) cons ht

  let rec empty : type xs. xs Tlist.t -> xs ht = function
    | Nil -> []
    | Cons xs -> Emp :: empty xs

  let rec snoc : type xs. xs ht -> xs Hlist.t -> xs ht =
   fun xs x ->
    match (xs, x) with
    | [], [] -> []
    | x :: xs, y :: ys -> Snoc (x, y) :: snoc xs ys

  let rec tail : type xs. xs ht -> xs Hlist.t = function
    | [] -> []
    | Snoc (_, x) :: xs -> x :: tail xs
    | Emp :: _ -> raise (Failure "Empty tail")

  let rec head : type xs. xs ht -> xs ht = function
    | [] -> []
    | Snoc (x, _) :: xs -> x :: head xs
    | Emp :: _ -> raise (Failure "Empty head")

  let rec tlist : type xs. xs ht -> xs Tlist.t = function
    | [] -> Nil
    | _ :: xs -> Cons (tlist xs)
end

module Applicatic (M : Applicative.Plain) = struct
  open Applicative.Ops (M)

  let rec pmapM : type x xs ys.
      ((x, xs) cons Hlist.t -> ys Hlist.t M.t) ->
      (x, xs) cons Heter.ht ->
      ys Tlist.t ->
      ys Heter.ht M.t =
   fun f xss ys ->
    match xss with
    | Emp :: _ -> return (Heter.empty ys)
    | Snoc (xs, x) :: xss ->
        let+ fxs = pmapM f (xs :: Heter.head xss) ys and+ fx = f (x :: Heter.tail xss) in
        Heter.snoc fxs fx

  let miterM : type x xs. ((x, xs) cons Hlist.t -> unit M.t) -> (x, xs) cons Heter.ht -> unit M.t =
   fun f xss ->
    let+ [] =
      pmapM
        (fun x ->
          let+ () = f x in
          [])
        xss Nil in
    ()

  let mmapM : type x xs y. ((x, xs) cons Hlist.t -> y M.t) -> (x, xs) cons Heter.ht -> y Bwd.t M.t =
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

let pmap : type x xs ys.
    ((x, xs) cons Hlist.t -> ys Hlist.t) -> (x, xs) cons Heter.ht -> ys Tlist.t -> ys Heter.ht =
 fun f xss ys ->
  let open Monadic (Monad.Identity) in
  pmapM f xss ys

let miter : type x xs. ((x, xs) cons Hlist.t -> unit) -> (x, xs) cons Heter.ht -> unit =
 fun f xss ->
  let open Monadic (Monad.Identity) in
  miterM f xss

let mmap : type x xs y. ((x, xs) cons Hlist.t -> y) -> (x, xs) cons Heter.ht -> y Bwd.t =
 fun f xs ->
  let open Monadic (Monad.Identity) in
  mmapM f xs

let map : type x y. (x -> y) -> x Bwd.t -> y Bwd.t = fun f xs -> mmap (fun [ x ] -> f x) [ xs ]

let fwd_nth_opt : type a. a Bwd.t -> int -> a option =
 fun xs i ->
  let rec go xs i =
    match xs with
    | Emp -> Error i
    | Snoc (xs, x) -> (
        match go xs i with
        | Ok y -> Ok y
        | Error i -> if i = 0 then Ok x else Error (i - 1)) in
  Result.to_option (go xs i)
