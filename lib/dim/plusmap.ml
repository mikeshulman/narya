open Util

(* Add the same dimension on the left of everything in a tbwd of dimensions. *)

module Anyplus = struct
  module Dom = D
  module Cod = D

  type 'p param = 'p D.t
  type ('p, 'a, 'b) t = ('p, 'a, 'b) D.plus
  type (_, _) exists = Exists : 'b Cod.t * ('p, 'a, 'b) t -> ('p, 'a) exists

  let exists : type p a. p param -> a Dom.t -> (p, a) exists =
   fun p a ->
    let (Plus ab) = D.plus a in
    Exists (D.plus_out p ab, ab)

  let out : type p a b. p param -> a Dom.t -> (p, a, b) t -> b Cod.t = fun p _ pa -> D.plus_out p pa
  let uniq : type p a b1 b2. (p, a, b1) t -> (p, a, b2) t -> (b1, b2) Eq.t = D.plus_uniq
end

include Tbwdmap.Make (Anyplus)

let rec assocl : type a b ab cs bcs abcs.
    (a, b, ab) D.plus -> (b, cs, bcs) t -> (a, bcs, abcs) t -> (ab, cs, abcs) t =
 fun ab bcs abcs ->
  match (bcs, abcs) with
  | Map_emp, Map_emp -> Map_emp
  | Map_snoc (bcs, bc), Map_snoc (abcs, a_bc) ->
      let ab_c = D.plus_assocl ab bc a_bc in
      Map_snoc (assocl ab bcs abcs, ab_c)

let rec zerol : type bs. bs OfDom.t -> (D.zero, bs, bs) t = function
  | Word Zero -> Map_emp
  | Word (Suc (bs, b)) -> Map_snoc (zerol (Word bs), D.zero_plus b)
