(* Heterogeneous lists *)

open Tlist

(* We define this outside the module so that its constructors are globally visible once this file is opened. *)
type _ hlist = [] : nil hlist | ( :: ) : 'x * 'xs hlist -> ('x, 'xs) cons hlist

module Hlist = struct
  (* A heterogeneous list of elements of some type-level list *)
  type 'a t = 'a hlist

  let nil : nil t = []
  let cons : type x xs. x -> xs t -> (x, xs) cons t = fun x xs -> x :: xs

  (* Every hlist has a valid type-level list.  *)
  let rec to_tlist : type xs. xs t -> xs Tlist.t = function
    | [] -> Nil
    | _ :: xs -> Cons (to_tlist xs)
end
