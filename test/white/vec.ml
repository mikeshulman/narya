open Testutil.Mcp

let () = Types.Vec.install ()
let uu, _ = synth "Type"
let aa = assume "A" uu
let a = assume "a" aa
let va0, _ = synth "Vec A 0."
let a0 = check "nil." va0
let va1, _ = synth "Vec A (1. 0.)"
let a1 = check "cons. 0. a nil." va1
let va2, _ = synth "Vec A (1. (1. 0.))"
let a2 = check "cons. (1. 0.) a (cons. 0. a nil.)" va2
let va3, _ = synth "Vec A 3"
let a3 = check "cons. 2 a (cons. 1 a (cons. 0 a nil.))" va3

(* Identity types *)
let id00, _ = synth "Id (Vec A 0) nil. nil."
let eq00 = check "nil." id00
let id11, _ = synth "Id (Vec A 1) (cons. 0 a nil.) (cons. 0 a nil.)"

(* Since numerals check rather than synthesizing, we have to ascribe them to apply refl. *)
let eq11 = check "cons. (refl (0:N)) (refl a) nil." id11
let id22, _ = synth "Id (Vec A 2) (cons. 1 a (cons. 0 a nil.)) (cons. 1 a (cons. 0 a nil.))"
let eq22 = check "cons. (refl (1:N)) (refl a) (cons. (refl (0:N)) (refl a) nil.)" id22

(* Check that the induction principle has the right type *)
let _, indty = synth "Vec_ind"

let indty', _ =
  synth
    "(A:Type) (C : (n:N) (xs : Vec A n) → Type) → C 0 nil. → ((n:N) (x:A) (xs: Vec A n) → C n xs → C (1. n) (cons. n x xs)) → (n:N) (xs : Vec A n) → C n xs"

let () = equal indty indty'

(* We can define concatenation by induction.  But it works better with a left-recursive version of nat addition. *)
let rntonton = "N → N → N"
let ntonton, _ = synth rntonton
let rlplus = "m n ↦ N_ind (_ ↦ N) n (_ IH ↦ 1. IH) m"
let lplus = check rlplus ntonton
let lp = Printf.sprintf "((%s) : %s)" rlplus rntonton

(* And we prove that addition is associative *)
let rlpassoc_ty = Printf.sprintf "(m n k : N) → Id N (%s (%s m n) k) (%s m (%s n k))" lp lp lp lp
let lpassoc_ty = check rlpassoc_ty uu

let rlpassoc =
  Printf.sprintf
    "m n k ↦ N_ind (m ↦ Id N (%s (%s m n) k) (%s m (%s n k))) (refl (%s n k)) (_ IH ↦ 1. IH) m" lp
    lp lp lp lp

let lpassoc = check rlpassoc lpassoc_ty
let lpa = Printf.sprintf "((%s) : %s)" rlpassoc rlpassoc_ty

(* And right unital *)
let rlpru_ty = Printf.sprintf "(m:N) → Id N (%s m 0) m" lp
let lpru_ty = check rlpru_ty uu
let rlpru = Printf.sprintf "m ↦ N_ind (m ↦ Id N (%s m 0) m) (refl (0:N)) (_ IH ↦ 1. IH) m" lp
let lpru = check rlpru lpru_ty
let lpr = Printf.sprintf "((%s) : %s)" rlpru rlpru_ty

(* Now we can define concatenation *)
let rconcat_ty = Printf.sprintf "(A:Type) (m n : N) → Vec A m → Vec A n → Vec A (%s m n)" lp
let concat_ty, _ = synth rconcat_ty

let rconcat =
  Printf.sprintf
    "A m n xs ys ↦ Vec_ind A (m _ ↦ Vec A (%s m n)) ys (m x xs IH ↦ cons. (%s m n) x IH) m xs" lp lp

let concat = check rconcat concat_ty
let cc = Printf.sprintf "((%s) : %s)" rconcat rconcat_ty
let a0 = assume "a0" aa
let a1 = assume "a1" aa
let a2 = assume "a2" aa
let a3 = assume "a3" aa
let a4 = assume "a4" aa
let ra01 = "cons. 1 a0 (cons. 0 a1 nil.)"
let a01 = check ra01 (check "Vec A 2" uu)
let ra234 = "cons. 2 a2 (cons. 1 a3 (cons. 0 a4 nil.))"
let a234 = check ra234 (check "Vec A 3" uu)

let a01234 =
  check "cons. 4 a0 (cons. 3 a1 (cons. 2 a2 (cons. 1 a3 (cons. 0 a4 nil.))))" (check "Vec A 5" uu)

let a01_234 = check (Printf.sprintf "%s A 2 3 (%s) (%s)" cc ra01 ra234) (check "Vec A 5" uu)
let () = equal_at a01_234 a01234 (check "Vec A 5" uu)

(* We can prove that concatenation is associative, "over" associativity of addition. *)
let rconcatassoc_ty =
  Printf.sprintf
    "(A:Type) (m n k : N) (xs : Vec A m) (ys : Vec A n) (zs : Vec A k) → Id (Vec A) (%s (%s m n) k) (%s m (%s n k)) (%s m n k) (%s A (%s m n) k (%s A m n xs ys) zs) (%s A m (%s n k) xs (%s A n k ys zs))"
    lp lp lp lp lpa cc lp cc cc lp cc

let concatassoc_ty = check rconcatassoc_ty uu

let rconcatassoc =
  Printf.sprintf
    "A m n k xs ys zs ↦ Vec_ind A (m xs ↦ Id (Vec A) (%s (%s m n) k) (%s m (%s n k)) (%s m n k) (%s A (%s m n) k (%s A m n xs ys) zs) (%s A m (%s n k) xs (%s A n k ys zs))) (refl (%s A n k ys zs)) (m x xs IH ↦ cons. (%s m n k) (refl x) IH) m xs"
    lp lp lp lp lpa cc lp cc cc lp cc cc lpa

let concatassoc = check rconcatassoc concatassoc_ty

(* And similarly right unital. *)
let rconcatru_ty =
  Printf.sprintf
    "(A:Type) (m:N) (xs : Vec A m) → Id (Vec A) (%s m 0) m (%s m) (%s A m 0 xs nil.) xs" lp lpr cc

let concatru_ty = check rconcatru_ty uu

let rconcatru =
  Printf.sprintf
    "A m xs ↦ Vec_ind A (m xs ↦ Id (Vec A) (%s m 0) m (%s m) (%s A m 0 xs nil.) xs) nil. (m x xs IH ↦ cons. (%s m) (refl x) IH) m xs"
    lp lpr cc lpr

let concatru = check rconcatru concatru_ty
