open Util
open Singleton
open Sface

(* "Tube faces" are strict faces that are constrained to lie in a particular tube. *)

type (_, _, _, _) tface =
  | End :
      ('m, 'nk) sface * ('n, 'k, 'nk) D.plus * 'l Endpoints.t
      -> ('m, 'n, 'k D.suc, 'nk D.suc) tface
  | Mid : ('m, 'n, 'k, 'nk) tface -> ('m D.suc, 'n, 'k D.suc, 'nk D.suc) tface

let rec sface_of_tface : type m n k nk. (m, n, k, nk) tface -> (m, nk) sface = function
  | End (d, _, e) -> End (d, e)
  | Mid d -> Mid (sface_of_tface d)

let rec plus_of_tface : type m n k nk. (m, n, k, nk) tface -> (m, nk) d_le = function
  | End (d, _, _) ->
      let (Le mn) = plus_of_sface d in
      Le (Suc mn)
  | Mid d ->
      let (Le mn) = plus_of_tface d in
      Le (N.suc_plus_eq_suc mn)

let rec cod_plus_of_tface : type m n k nk. (m, n, k, nk) tface -> (n, k, nk) D.plus = function
  | End (_, p, _) -> Suc p
  | Mid d -> Suc (cod_plus_of_tface d)

let rec dom_tface : type m n k nk. (m, n, k, nk) tface -> m D.t = function
  | End (d, _, _) -> dom_sface d
  | Mid d -> D.suc (dom_tface d)

let rec codl_tface : type m n k nk. (m, n, k, nk) tface -> n D.t = function
  | End (d, p, _) -> D.minus (cod_sface d) p
  | Mid d -> codl_tface d

let rec codr_tface : type m n k nk. (m, n, k, nk) tface -> k D.t = function
  | End (_, nk, _) -> D.suc (D.plus_right nk)
  | Mid d -> D.suc (codr_tface d)

let cod_tface : type m n k nk. (m, n, k, nk) tface -> nk D.t =
 fun d -> D.plus_out (codl_tface d) (cod_plus_of_tface d)

let tface_end : type l m n k nk.
    (m, n, k, nk) tface -> l Endpoints.t -> (m, n, k D.suc, nk D.suc) tface =
 fun d e -> End (sface_of_tface d, cod_plus_of_tface d, e)

let rec tface_plus : type m n k nk l ml kl nkl.
    (m, n, k, nk) tface ->
    (k, l, kl) D.plus ->
    (nk, l, nkl) D.plus ->
    (m, l, ml) D.plus ->
    (ml, n, kl, nkl) tface =
 fun d kl nkl ml ->
  match (kl, nkl, ml) with
  | Zero, Zero, Zero -> d
  | Suc kl, Suc nkl, Suc ml -> Mid (tface_plus d kl nkl ml)

(* A "proper face" is a fully instantiated tube face. *)

type ('m, 'n) pface = ('m, D.zero, 'n, 'n) tface

(* Any strict face is either a proper face or the top face. *)
let rec pface_of_sface : type m n. (m, n) sface -> [ `Proper of (m, n) pface | `Id of (m, n) Eq.t ]
    = function
  | Zero -> `Id Eq
  | End (fa, e) -> `Proper (End (fa, D.zero_plus (cod_sface fa), e))
  | Mid fa -> (
      match pface_of_sface fa with
      | `Proper fb -> `Proper (Mid fb)
      | `Id Eq -> `Id Eq)

(* Like insert_sface but for pfaces instead.  (It should be possible to do this for general tfaces too, but trickier, and all we need is pfaces.) *)

type (_, _) insert_pface =
  | Insert_pface : ('m, 'msuc) D.insert * ('msuc, 'nsuc) pface -> ('m, 'nsuc) insert_pface

let rec insert_pface : type m n nsuc. (m, n) pface -> (n, nsuc) D.insert -> (m, nsuc) insert_pface =
 fun f i ->
  match i with
  | Now -> Insert_pface (Now, Mid f)
  | Later i -> (
      match f with
      | End (f, _, e) ->
          let (Insert_sface (i, f)) = insert_sface f i in
          Insert_pface (i, End (f, D.zero_plus (cod_sface f), e))
      | Mid f ->
          let (Insert_pface (i, f)) = insert_pface f i in
          Insert_pface (Later i, Mid f))

let pface_plus : type m n mn k kn.
    (k, m) pface -> (m, n, mn) D.plus -> (k, n, kn) D.plus -> (kn, mn) pface =
 fun d mn kn -> tface_plus d mn mn kn

(* Any strict face can be added to a tube face on the left to get another tube face. *)

let rec sface_plus_tface : type m n mn l nl mnl k p kp.
    (k, m) sface ->
    (m, n, mn) D.plus ->
    (m, nl, mnl) D.plus ->
    (k, p, kp) D.plus ->
    (p, n, l, nl) tface ->
    (kp, mn, l, mnl) tface =
 fun fkm mn m_nl kp fpnl ->
  match (fpnl, m_nl, kp) with
  | End (fpn, nl, e), Suc m_nl, kp ->
      let mn_l = D.plus_assocl mn nl m_nl in
      End (sface_plus_sface fkm m_nl kp fpn, mn_l, e)
  | Mid fpn, Suc m_nl, Suc kp -> Mid (sface_plus_tface fkm mn m_nl kp fpn)

let sface_plus_pface : type m n mn k p kp.
    (k, m) sface -> (m, n, mn) D.plus -> (k, p, kp) D.plus -> (p, n) pface -> (kp, m, n, mn) tface =
 fun fkm mn kp fpn -> sface_plus_tface fkm Zero mn kp fpn

(* Conversely, every tube face decomposes as an ordinary strict face added to a tube face along a decomposition of its uninstantiated dimensions. *)

type (_, _, _, _) tface_of_plus =
  | TFace_of_plus :
      ('p, 'q, 'pq) D.plus * ('p, 'n) sface * ('q, 'k, 'l, 'kl) tface
      -> ('pq, 'n, 'k, 'l) tface_of_plus

let rec tface_of_plus : type m n k nk l nkl.
    (n, k, nk) D.plus -> (m, nk, l, nkl) tface -> (m, n, k, l) tface_of_plus =
 fun nk d ->
  match d with
  | End (d, nk_l, e) ->
      let (Plus kl) = D.plus (D.plus_right nk_l) in
      let n_kl = D.plus_assocr nk kl nk_l in
      let (SFace_of_plus (pq, d1, d2)) = sface_of_plus n_kl d in
      TFace_of_plus (pq, d1, End (d2, kl, e))
  | Mid d ->
      let (TFace_of_plus (pq, d1, d2)) = tface_of_plus nk d in
      TFace_of_plus (Suc pq, d1, Mid d2)

(* In particular, any tube face decomposes as a strict face plus a proper face. *)

type (_, _, _) pface_of_plus =
  | PFace_of_plus :
      ('p, 'q, 'pq) D.plus * ('p, 'n) sface * ('q, 'k) pface
      -> ('pq, 'n, 'k) pface_of_plus

let pface_of_plus : type m n k nk. (m, n, k, nk) tface -> (m, n, k) pface_of_plus =
 fun d ->
  let (TFace_of_plus (pq, s, d)) = tface_of_plus Zero d in
  let Eq = D.plus_uniq (cod_plus_of_tface d) (D.zero_plus (codr_tface d)) in
  PFace_of_plus (pq, s, d)

(* A tube face with exactly one instantiated dimension can be decomposed into an endpoint and a strict face. *)

let singleton_tface : type m n k nk l.
    (m, n, k, nk) tface -> k is_singleton -> l Endpoints.len -> (m, n) sface * l N.index =
 fun d k l ->
  let One = k in
  match d with
  | End (s, n0, (l', i)) ->
      let Zero = n0 in
      let Eq = Endpoints.uniq l l' in
      (s, i)

(* A tface is codimension-1 if it has exactly one endpoint. *)

let rec is_codim1 : type m n k nk. (m, n, k, nk) tface -> unit option = function
  | End (fa, _, _) -> Option.map (fun _ -> ()) (is_id_sface fa)
  | Mid s -> is_codim1 s

type (_, _, _) tface_of = Tface_of : ('m, 'n, 'k, 'nk) tface -> ('n, 'k, 'nk) tface_of

(* Every tface belongs to a unique codimension-1 tface. *)
let rec codim1_envelope : type m n k nk. (m, n, k, nk) tface -> (n, k, nk) tface_of = function
  | End (fa, nk, l) -> Tface_of (End (id_sface (cod_sface fa), nk, l))
  | Mid s ->
      let (Tface_of s1) = codim1_envelope s in
      Tface_of (Mid s1)
