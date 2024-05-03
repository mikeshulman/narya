open Util

(* Since dimensions are epimorphisms, given n and nk there is at most one k such that (n,k,nk) D.plus.  This function finds it if it exists. *)

type (_, _) factor = Factor : ('n, 'k, 'nk) D.plus -> ('nk, 'n) factor

let rec factor : type nk n. nk D.t -> n D.t -> (nk, n) factor option =
 fun nk n ->
  let open Monad.Ops (Monad.Maybe) in
  match N.compare nk n with
  | Eq -> Some (Factor Zero)
  | Neq -> (
      match nk with
      | Nat Zero -> None
      | Nat (Suc nk) ->
          let* (Factor n_k) = factor (Nat nk) n in
          return (Factor (Suc n_k)))

(* Compute the pushout of a span of dimensions, if it exists.  In practice we only need pushouts of spans that can be completed to some commutative square (equivalently, pushouts in slice categories), but in our primary examples all pushouts exist, so we don't bother putting an option on it yet. *)

type (_, _) pushout = Pushout : ('a, 'c, 'p) D.plus * ('b, 'd, 'p) D.plus -> ('a, 'b) pushout

let pushout : type a b. a D.t -> b D.t -> (a, b) pushout =
 fun a b ->
  match D.trichotomy a b with
  | Eq -> Pushout (Zero, Zero)
  | Lt ab -> Pushout (ab, Zero)
  | Gt ba -> Pushout (Zero, ba)
