open Sface

(* "Backwards strict faces" contain the same data as ordinary strict faces, but are inductive on the other side, like lists and backward lists. *)

type (_, _) bwsface =
  | Zero : (D.zero, D.zero) bwsface
  | End : 'l Endpoints.t * ('m, 'n) bwsface -> ('m, 'n D.suc) bwsface
  | Mid : ('m, 'n) bwsface -> ('m D.suc, 'n D.suc) bwsface

let rec dom_bwsface : type m n. (m, n) bwsface -> m D.t = function
  | Zero -> Nat Zero
  | End (_, f) ->
      let (Nat s) = dom_bwsface f in
      Nat s
  | Mid f ->
      let (Nat s) = dom_bwsface f in
      Nat (Suc s)

let rec cod_bwsface : type m n. (m, n) bwsface -> n D.t = function
  | Zero -> Nat Zero
  | End (_, f) ->
      let (Nat s) = cod_bwsface f in
      Nat (Suc s)
  | Mid f ->
      let (Nat s) = cod_bwsface f in
      Nat (Suc s)

let sface_of_bw : type m n. (m, n) bwsface -> (m, n) sface =
 fun bf ->
  let rec sface_of_bw_onto : type k l m n km ln.
      (k, m, km) D.plus -> (l, n, ln) D.plus -> (k, l) sface -> (m, n) bwsface -> (km, ln) sface =
   fun km ln f bf ->
    match bf with
    | Zero ->
        let Zero, Zero = (km, ln) in
        f
    | End (e, bf) -> sface_of_bw_onto km (D.suc_plus ln) (End (f, e)) bf
    | Mid bf -> sface_of_bw_onto (D.suc_plus km) (D.suc_plus ln) (Mid f) bf in
  sface_of_bw_onto
    (D.zero_plus (dom_bwsface bf))
    (D.zero_plus (cod_bwsface bf))
    (id_sface D.zero) bf
