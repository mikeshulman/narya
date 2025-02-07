(* Type-level forwards lists *)

(* The constructors of type-level forwards lists *)
type nil = private Dummy_nil
type ('x, 'xs) cons = private Dummy_cons

module Tlist = struct
  (* A predicate for "being a type-level list" *)
  type _ t = Nil : nil t | Cons : 'xs t -> ('x, 'xs) cons t

  (* ('a, 'n, 'b) insert says that the tlist 'b is obtained from the tlist 'a by inserting a type 'n somewhere specified.  Or, equivalently, 'a is obtained from 'b by removing a type 'n from somewhere specified. *)
  type (_, _, _) insert =
    | Now : ('a, 'n, ('n, 'a) cons) insert
    | Later : ('a, 'n, 'b) insert -> (('k, 'a) cons, 'n, ('k, 'b) cons) insert

  (* Inserting something into a tlist produces another tlist. *)
  let rec inserted : type a n b. (a, n, b) insert -> a t -> b t =
   fun ins a ->
    match ins with
    | Now -> Cons a
    | Later ins ->
        let (Cons a) = a in
        Cons (inserted ins a)

  (* Flatten a tlist of backward nats into a single forwards nat by "adding them up". *)
  type (_, _) flatten =
    | Flat_nil : (nil, Fwn.zero) flatten
    | Flat_cons : ('n, 'm, 'nm) Fwn.fplus * ('ns, 'm) flatten -> (('n, 'ns) cons, 'nm) flatten

  let rec flatten_in : type ns n. (ns, n) flatten -> ns t = function
    | Flat_nil -> Nil
    | Flat_cons (_, ns) -> Cons (flatten_in ns)

  (* Mapping a simple type-level function *)

  module type TFun = sig
    type ('p, 'a, 'b) t
    type (_, _) exists = Exists : ('p, 'a, 'b) t -> ('p, 'a) exists

    val exists : ('p, 'a) exists
  end

  module Map (F : TFun) = struct
    type 'xs tlist = 'xs t

    type (_, _, _) t =
      | [] : ('p, nil, nil) t
      | ( :: ) : ('p, 'x, 'y) F.t * ('p, 'xs, 'ys) t -> ('p, ('x, 'xs) cons, ('y, 'ys) cons) t

    type (_, _) exists = Exists : ('p, 'xs, 'ys) t -> ('p, 'xs) exists

    let rec exists : type p xs. xs tlist -> (p, xs) exists = function
      | Nil -> Exists []
      | Cons xs ->
          let Exists y, Exists ys = (F.exists, exists xs) in
          Exists (y :: ys)

    type (_, _, _) exists_cons =
      | Exists_cons : ('p, ('x, 'xs) cons, ('y, 'ys) cons) t -> ('p, 'x, 'xs) exists_cons

    let exists_cons : type p x xs. (x, xs) cons tlist -> (p, x, xs) exists_cons = function
      | Cons xs ->
          let Exists y, Exists ys = (F.exists, exists xs) in
          Exists_cons (y :: ys)

    let rec cod : type p xs ys. (p, xs, ys) t -> ys tlist = function
      | [] -> Nil
      | _ :: xs -> Cons (cod xs)
  end
end
