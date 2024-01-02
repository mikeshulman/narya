(* Here we instantiate the general traversal technique of Mlist to act on Bwds.  This is more or less a direct transcription.  Note, though, that in contrast to the supplied traversals such as Bwd.map and Bwd.iter, here we traverse a Bwd from LEFT TO RIGHT, following the TEXTUAL ORDER rather than the direction for adding and removing elements. *)

open Bwd
open Hlist

module Heter = struct
  type _ ht = [] : nil ht | ( :: ) : 'x Bwd.t * 'xs ht -> ('x, 'xs) cons ht

  let rec empty : type xs. xs tlist -> xs ht = function
    | Nil -> []
    | Cons xs -> Emp :: empty xs

  let rec snoc : type xs. xs ht -> xs hlist -> xs ht =
   fun xs x ->
    match (xs, x) with
    | [], [] -> []
    | x :: xs, y :: ys -> Snoc (x, y) :: snoc xs ys

  let rec tail : type xs. xs ht -> xs hlist = function
    | [] -> []
    | Snoc (_, x) :: xs -> x :: tail xs
    | Emp :: _ -> raise (Failure "Empty tail")

  let rec head : type xs. xs ht -> xs ht = function
    | [] -> []
    | Snoc (x, _) :: xs -> x :: head xs
    | Emp :: _ -> raise (Failure "Empty head")

  let rec tlist : type xs. xs ht -> xs tlist = function
    | [] -> Nil
    | _ :: xs -> Cons (tlist xs)
end

module Monadic (M : Monad.Plain) = struct
  open Monad.Ops (M)

  let rec pmapM :
      type x xs ys.
      ((x, xs) cons hlist -> ys hlist M.t) -> (x, xs) cons Heter.ht -> ys tlist -> ys Heter.ht M.t =
   fun f xss ys ->
    match xss with
    | Emp :: _ -> return (Heter.empty ys)
    | Snoc (xs, x) :: xss ->
        let* fxs = pmapM f (xs :: Heter.head xss) ys in
        let* fx = f (x :: Heter.tail xss) in
        return (Heter.snoc fxs fx)

  let miterM : type x xs. ((x, xs) cons hlist -> unit M.t) -> (x, xs) cons Heter.ht -> unit M.t =
   fun f xss ->
    let* [] =
      pmapM
        (fun x ->
          let* () = f x in
          return [])
        xss Nil in
    return ()

  let mmapM : type x xs y. ((x, xs) cons hlist -> y M.t) -> (x, xs) cons Heter.ht -> y Bwd.t M.t =
   fun f xs ->
    let* [ ys ] =
      pmapM
        (fun x ->
          let* y = f x in
          return [ y ])
        xs (Cons Nil) in
    return ys
end

let pmap :
    type x xs ys.
    ((x, xs) cons hlist -> ys hlist) -> (x, xs) cons Heter.ht -> ys tlist -> ys Heter.ht =
 fun f xss ys ->
  let open Monadic (Monad.Identity) in
  pmapM f xss ys

let miter : type x xs. ((x, xs) cons hlist -> unit) -> (x, xs) cons Heter.ht -> unit =
 fun f xss ->
  let open Monadic (Monad.Identity) in
  miterM f xss

let mmap : type x xs y. ((x, xs) cons hlist -> y) -> (x, xs) cons Heter.ht -> y Bwd.t =
 fun f xs ->
  let open Monadic (Monad.Identity) in
  mmapM f xs
