open Testutil.Mcp

let () = Types.List.install ()
let uu, _ = synth "Type"
let aa = assume "A" uu
let a = assume "a" aa
let la, _ = synth "List A"
let a0 = check "nil." la
let a1 = check "cons. a nil." la
let a2 = check "cons. a (cons. a nil.)" la
let a3 = check "cons. a (cons. a (cons. a nil.))" la
let id00, _ = synth "Id (List A) nil. nil."
let eq00 = check "nil." id00
let id11, _ = synth "Id (List A) (cons. a nil.) (cons. a nil.)"
let eq11 = check "cons. (refl a) nil." id11
let id22, _ = synth "Id (List A) (cons. a (cons. a nil.)) (cons. a (cons. a nil.))"
let eq22 = check "cons. (refl a) (cons. (refl a) nil.)" id22

(* Check that the induction principle has the right type *)
let _, indty = synth "List_ind"

let indty', _ =
  synth
    "(A:Type) (C : List A → Type) → C nil. → ((x:A) (xs: List A) → C xs → C (cons. x xs)) → (xs : List A) → C xs"

let () = equal indty indty'

(* We can define concatenation by induction *)
let rconcat_ty = "(A:Type) → List A → List A → List A"
let concat_ty, _ = synth rconcat_ty
let rconcat = "A xs ys ↦ List_ind A (_ ↦ List A) ys (x _ xs_ys ↦ cons. x xs_ys) xs"
let concat = check rconcat concat_ty
let a0 = assume "a0" aa
let a1 = assume "a1" aa
let a2 = assume "a2" aa
let a3 = assume "a3" aa
let a4 = assume "a4" aa
let ra01 = "cons. a0 (cons. a1 nil.)"
let a01 = check ra01 la
let ra234 = "cons. a2 (cons. a3 (cons. a4 nil.))"
let a234 = check ra234 la
let a01_234 = check (Printf.sprintf "((%s) : %s) A (%s) (%s)" rconcat rconcat_ty ra01 ra234) la
let a01234 = check "cons. a0 (cons. a1 (cons. a2 (cons. a3 (cons. a4 nil.))))" la
let () = equal_at a01_234 a01234 la

(* And prove that it is unital and associative *)
let cc = Printf.sprintf "((%s) : %s)" rconcat rconcat_ty

let concatlu_ty, _ =
  synth (Printf.sprintf "(A:Type) (xs : List A) → Id (List A) (%s A nil. xs) xs" cc)

let concatlu = check "A xs ↦ refl xs" concatlu_ty

let concatru_ty, _ =
  synth (Printf.sprintf "(A:Type) (xs : List A) → Id (List A) (%s A xs nil.) xs" cc)

let concatru =
  check
    (Printf.sprintf
       "A xs ↦ List_ind A (ys ↦ Id (List A) (%s A ys nil.) ys) (refl (nil. : List A)) (y ys ysnil ↦ cons. (refl y) ysnil) xs"
       cc)
    concatru_ty

let concatassoc_ty, _ =
  synth
    (Printf.sprintf
       "(A:Type) (xs ys zs : List A) → Id (List A) (%s A (%s A xs ys) zs) (%s A xs (%s A ys zs))" cc
       cc cc cc)

let concatassoc =
  check
    (Printf.sprintf
       "A xs ys zs ↦ List_ind A (xs ↦ Id (List A) (%s A (%s A xs ys) zs) (%s A xs (%s A ys zs))) (refl (%s A ys zs)) (x xs IH ↦ cons. (refl x) IH) xs"
       cc cc cc cc cc)
    concatassoc_ty
