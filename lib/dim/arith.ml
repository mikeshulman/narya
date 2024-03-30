open Util

(* We consider the addition in D to represent composition in the delooping of the dimension category, in diagrammatic order. *)

let compare : type m n. m D.t -> n D.t -> (m, n) Monoid.compare =
 fun m n ->
  match N.compare m n with
  | Eq -> Eq
  | _ -> Neq

(* Since dimensions are epimorphisms, given n and nk there is at most one k such that (n,k,nk) D.plus.  This function finds it if it exists. *)

type (_, _) factor = Factor : ('n, 'k, 'nk) D.plus -> ('nk, 'n) factor

let rec factor : type nk n. nk D.t -> n D.t -> (nk, n) factor option =
 fun nk n ->
  let open Monad.Ops (Monad.Maybe) in
  match compare nk n with
  | Eq -> Some (Factor Zero)
  | Neq -> (
      match nk with
      | Nat Zero -> None
      | Nat (Suc nk) ->
          let* (Factor n_k) = factor (Nat nk) n in
          return (Factor (Suc n_k)))

(* And we prove that it is unique. *)
let rec zero_uniq : type m z. m D.t -> (m, z, m) D.plus -> (z, D.zero) Monoid.eq =
 fun m mz ->
  match m with
  | Nat Zero ->
      let Zero = mz in
      Eq
  | Nat (Suc m) ->
      let (Suc mz) = D.plus_suc mz in
      let Eq = zero_uniq (Nat m) mz in
      Eq

let rec epi : type m n k l. k D.t -> (k, m, l) D.plus -> (k, n, l) D.plus -> (m, n) Monoid.eq =
 fun k km kn ->
  match (km, kn) with
  | Zero, _ ->
      let Eq = zero_uniq k kn in
      Eq
  | _, Zero ->
      let Eq = zero_uniq k km in
      Eq
  | Suc km, Suc kn ->
      let Eq = epi k km kn in
      Eq

(* Compute the pushout of a span of dimensions, if it exists.  In practice we only need pushouts of spans that can be completed to some commutative square (equivalently, pushouts in slice categories), but in our primary examples all pushouts exist, so we don't bother putting an option on it yet. *)

type (_, _) pushout = Pushout : ('a, 'c, 'p) D.plus * ('b, 'd, 'p) D.plus -> ('a, 'b) pushout

let pushout : type a b. a D.t -> b D.t -> (a, b) pushout =
 fun a b ->
  match D.compare a b with
  | Eq -> Pushout (Zero, Zero)
  | Lt ab -> Pushout (ab, Zero)
  | Gt ba -> Pushout (Zero, ba)
