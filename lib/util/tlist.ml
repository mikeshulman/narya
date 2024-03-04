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
end
