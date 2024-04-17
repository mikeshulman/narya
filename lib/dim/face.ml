open Deg
open Sface

(* A face is a permutation followed by a strict face, hence a map as for a strict face that need not be order-preserving. *)

type (_, _) face = Face : ('m, 'n) sface * 'm perm -> ('m, 'n) face

let id_face : type n. n D.t -> (n, n) face = fun n -> Face (id_sface n, id_perm n)

(* Faces are closed under composition, by way of a distributive law between permutations and strict faces.  To define this we need a similar sort of "residual" of a strict face and an index, which picks out the image of that index and the strict face with that index and its image (if any) removed. *)

type (_, _) sface_residual =
  | End : ('m, 'n) sface * 'l Endpoints.t -> ('m, 'n D.suc) sface_residual
  | Mid : ('m, 'n) sface * 'm D.suc D.index -> ('m D.suc, 'n D.suc) sface_residual

let rec sface_residual : type m n. (m, n) sface -> n D.index -> (m, n) sface_residual =
 fun f k ->
  match (k, f) with
  | Top, End (f', e) -> End (f', e)
  | Top, Mid f' -> Mid (f', Top)
  | Pop k', End (f', e) -> (
      match sface_residual f' k' with
      | End (f'', e') -> End (End (f'', e), e')
      | Mid (f'', l) -> Mid (End (f'', e), l))
  | Pop k', Mid f' -> (
      match sface_residual f' k' with
      | End (f'', e') -> End (Mid f'', e')
      | Mid (f'', l) -> Mid (Mid f'', Pop l))

let rec perm_sface : type m n. n perm -> (m, n) sface -> (m, n) face =
 fun a b ->
  match a with
  | Zero _ -> Face (b, id_perm (dom_sface b))
  | Suc (p, k) -> (
      match sface_residual b k with
      | End (f, e) ->
          let (Face (f', p')) = perm_sface p f in
          Face (End (f', e), p')
      | Mid (f, l) ->
          let (Face (f', p')) = perm_sface p f in
          Face (Mid f', Suc (p', l)))

let comp_face : type m n k. (n, k) face -> (m, n) face -> (m, k) face =
 fun (Face (a, b)) (Face (c, d)) ->
  let (Face (c', b')) = perm_sface b c in
  Face (comp_sface a c', comp_perm b' d)

let dom_face : type m n. (m, n) face -> m D.t = function
  | Face (_, p) -> dim_perm p

let cod_face : type m n. (m, n) face -> n D.t = function
  | Face (f, _) -> cod_sface f

let face_of_sface : type m n. (m, n) sface -> (m, n) face = fun f -> Face (f, id_perm (dom_sface f))
let face_of_perm : type m. m perm -> (m, m) face = fun p -> Face (id_sface (dim_perm p), p)

(* Concatenate two faces left-to-right. *)
let face_plus_face :
    type m n mn k l kl.
    (k, m) face -> (m, n, mn) D.plus -> (k, l, kl) D.plus -> (l, n) face -> (kl, mn) face =
 fun (Face (fkm, pk)) mn kl (Face (fln, pl)) ->
  Face (sface_plus_sface fkm mn kl fln, perm_plus_perm pk kl pl)

type _ face_of = Face_of : ('m, 'n) face -> 'n face_of
