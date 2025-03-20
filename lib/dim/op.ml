open Util
open Deg
open Sface
open Face

(* If m and n are dimensions, (m,n) op is the type of dimensional operators m => n, which act on types and terms contravariantly.  We define these in an intrinsically correct way, using a strict factorization system consisting of degeneracies and strict faces.  *)

type (_, _) op = Op : ('n, 'k) sface * ('m, 'n) deg -> ('m, 'k) op

let id_op : type n. n D.t -> (n, n) op = fun n -> Op (id_sface n, id_deg n)

(* To compose operators, we use another distributive law. *)

let rec deg_sface : type m n k. (n, k) deg -> (m, n) sface -> (m, k) op =
 fun a b ->
  match a with
  | Zero _ ->
      let m = dom_sface b in
      Op (Zero, Zero m)
  | Suc (p, k) -> (
      match sface_residual b k with
      | End (f, e) ->
          let (Op (f', p')) = deg_sface p f in
          Op (End (f', e), p')
      | Mid (f, l) ->
          let (Op (f', p')) = deg_sface p f in
          Op (Mid f', Suc (p', l)))

let comp_op : type m n k. (n, k) op -> (m, n) op -> (m, k) op =
 fun (Op (a, b)) (Op (c, d)) ->
  let (Op (c', b')) = deg_sface b c in
  Op (comp_sface a c', comp_deg b' d)

let dom_op : type m n. (m, n) op -> m D.t = function
  | Op (_, s) -> dom_deg s

let cod_op : type m n. (m, n) op -> n D.t = function
  | Op (f, _) -> cod_sface f

let is_id_op : type m n. (m, n) op -> (m, n) Eq.t option =
 fun (Op (a, b)) ->
  match (is_id_sface a, is_id_deg b) with
  | Some Eq, Some Eq -> Some Eq
  | _ -> None

let op_of_deg : type m n. (m, n) deg -> (m, n) op = fun s -> Op (id_sface (cod_deg s), s)
let op_of_sface : type m n. (m, n) sface -> (m, n) op = fun f -> Op (f, id_deg (dom_sface f))

let op_plus_op : type m n mn k l kl.
    (k, m) op -> (m, n, mn) D.plus -> (k, l, kl) D.plus -> (l, n) op -> (kl, mn) op =
 fun (Op (d1, s1)) mn kl (Op (d2, s2)) ->
  let (Plus middle) = D.plus (dom_sface d2) in
  Op (sface_plus_sface d1 mn middle d2, deg_plus_deg s1 middle kl s2)

let plus_op : type m n mn l ml.
    m D.t -> (m, n, mn) D.plus -> (m, l, ml) D.plus -> (l, n) op -> (ml, mn) op =
 fun m mn ml op -> op_plus_op (id_op m) mn ml op

let op_plus : type m n mn k kn. (k, m) op -> (m, n, mn) D.plus -> (k, n, kn) D.plus -> (kn, mn) op =
 fun op mn kn -> op_plus_op op mn kn (id_op (D.plus_right mn))

type _ op_of = Of : ('m, 'n) op -> 'n op_of
type _ op_of_plus = Of : ('m, 'n) sface * 'm deg_of_plus -> 'n op_of_plus

let comp_op_of : type m n. (m, n) op -> m op_of -> n op_of = fun op (Of op') -> Of (comp_op op op')

let comp_op_deg_of_plus : type m n. (m, n) op -> m deg_of_plus -> n op_of_plus =
 fun (Op (f, s2)) s1 -> Of (f, comp_deg_of_plus s2 s1)
