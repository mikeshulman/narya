open Testutil.Mcp

let () =
  run @@ fun () ->
  Testutil.Repl.(
    def "ℕ" "Type" "data [ zero. | suc. (_ : ℕ) ]";
    def "Nat" "Type" "ℕ";
    def "Vec" "Type → ℕ → Type"
      "A ↦ data [ nil. : Vec A 0 | cons. : (n:ℕ) → A → Vec A n → Vec A (suc. n) ]";
    def "ℕ_ind" "(P : ℕ → Type) (z : P zero.) (s : (n:ℕ) → P n → P (suc. n)) (n : ℕ) → P n"
      "P z s n ↦ match n [
       | zero. ↦ z
       | suc. n ↦ s n (ℕ_ind P z s n)
     ]";
    def "Vec_ind"
      "(A:Type) (P : (n:ℕ) → Vec A n → Type) (pn : P zero. nil.) (pc : (n:ℕ) (a:A) (v:Vec A n) → P n v → P (suc. n) (cons. n a v)) (n:ℕ) (v:Vec A n) → P n v"
      "A P pn pc n v ↦ match v [
    | nil. ↦ pn
    | cons. n a v ↦ pc n a v (Vec_ind A P pn pc n v)
  ]");
  let uu, _ = synth "Type" in
  let aa = assume "A" uu in
  let a = assume "a" aa in
  let va0, _ = synth "Vec A zero." in
  let a0 = check "nil." va0 in
  let va1, _ = synth "Vec A (suc. zero.)" in
  let a1 = check "cons. zero. a nil." va1 in
  let va2, _ = synth "Vec A (suc. (suc. zero.))" in
  let a2 = check "cons. (suc. zero.) a (cons. zero. a nil.)" va2 in
  let va3, _ = synth "Vec A 3" in
  let a3 = check "cons. 2 a (cons. 1 a (cons. 0 a nil.))" va3 in

  (* Identity types *)
  let id00, _ = synth "Id (Vec A 0) nil. nil." in
  let eq00 = check "nil." id00 in
  let id11, _ = synth "Id (Vec A 1) (cons. 0 a nil.) (cons. 0 a nil.)" in

  (* Since numerals check rather than synthesizing, we have to ascribe them to apply refl. *)
  let eq11 = check "cons. (refl (0:ℕ)) (refl a) nil." id11 in
  let id22, _ = synth "Id (Vec A 2) (cons. 1 a (cons. 0 a nil.)) (cons. 1 a (cons. 0 a nil.))" in
  let eq22 = check "cons. (refl (1:ℕ)) (refl a) (cons. (refl (0:ℕ)) (refl a) nil.)" id22 in

  (* Check that the induction principle has the right type *)
  let _, indty = synth "Vec_ind" in

  let indty', _ =
    synth
      "(A:Type) (C : (n:ℕ) (xs : Vec A n) → Type) → C 0 nil. → ((n:ℕ) (x:A) (xs: Vec A n) → C n xs → C (suc. n) (cons. n x xs)) → (n:ℕ) (xs : Vec A n) → C n xs"
  in

  let () = equal indty indty' in

  (* We can define concatenation by induction.  But it works better with a left-recursive version of nat addition. *)
  let rntonton = "ℕ → ℕ → ℕ" in
  let ntonton, _ = synth rntonton in
  let rlplus = "m n ↦ ℕ_ind (_ ↦ ℕ) n (_ IH ↦ suc. IH) m" in
  let lplus = check rlplus ntonton in
  let lp = Printf.sprintf "((%s) : %s)" rlplus rntonton in

  (* And we prove that addition is associative *)
  let rlpassoc_ty =
    Printf.sprintf "(m n k : ℕ) → Id ℕ (%s (%s m n) k) (%s m (%s n k))" lp lp lp lp in
  let lpassoc_ty = check rlpassoc_ty uu in

  let rlpassoc =
    Printf.sprintf
      "m n k ↦ ℕ_ind (m ↦ Id ℕ (%s (%s m n) k) (%s m (%s n k))) (refl (%s n k)) (_ IH ↦ suc. IH) m"
      lp lp lp lp lp in

  let lpassoc = check rlpassoc lpassoc_ty in
  let lpa = Printf.sprintf "((%s) : %s)" rlpassoc rlpassoc_ty in

  (* And right unital *)
  let rlpru_ty = Printf.sprintf "(m:ℕ) → Id ℕ (%s m 0) m" lp in
  let lpru_ty = check rlpru_ty uu in
  let rlpru = Printf.sprintf "m ↦ ℕ_ind (m ↦ Id ℕ (%s m 0) m) (refl (0:ℕ)) (_ IH ↦ suc. IH) m" lp in
  let lpru = check rlpru lpru_ty in
  let lpr = Printf.sprintf "((%s) : %s)" rlpru rlpru_ty in

  (* Now we can define concatenation *)
  let rconcat_ty = Printf.sprintf "(A:Type) (m n : ℕ) → Vec A m → Vec A n → Vec A (%s m n)" lp in
  let concat_ty, _ = synth rconcat_ty in

  let rconcat =
    Printf.sprintf
      "A m n xs ys ↦ Vec_ind A (m _ ↦ Vec A (%s m n)) ys (m x xs IH ↦ cons. (%s m n) x IH) m xs" lp
      lp in

  let concat = check rconcat concat_ty in
  let cc = Printf.sprintf "((%s) : %s)" rconcat rconcat_ty in
  let a0 = assume "a0" aa in
  let a1 = assume "a1" aa in
  let a2 = assume "a2" aa in
  let a3 = assume "a3" aa in
  let a4 = assume "a4" aa in
  let ra01 = "cons. 1 a0 (cons. 0 a1 nil.)" in
  let a01 = check ra01 (check "Vec A 2" uu) in
  let ra234 = "cons. 2 a2 (cons. 1 a3 (cons. 0 a4 nil.))" in
  let a234 = check ra234 (check "Vec A 3" uu) in

  let a01234 =
    check "cons. 4 a0 (cons. 3 a1 (cons. 2 a2 (cons. 1 a3 (cons. 0 a4 nil.))))" (check "Vec A 5" uu)
  in

  let a01_234 = check (Printf.sprintf "%s A 2 3 (%s) (%s)" cc ra01 ra234) (check "Vec A 5" uu) in
  let () =
    equal_at a01_234 a01234 (check "Vec A 5" uu)
    (* We can prove that concatenation is associative, "over" associativity of addition. *) in

  let rconcatassoc_ty =
    Printf.sprintf
      "(A:Type) (m n k : ℕ) (xs : Vec A m) (ys : Vec A n) (zs : Vec A k) → Id (Vec A) (%s (%s m n) k) (%s m (%s n k)) (%s m n k) (%s A (%s m n) k (%s A m n xs ys) zs) (%s A m (%s n k) xs (%s A n k ys zs))"
      lp lp lp lp lpa cc lp cc cc lp cc in

  let concatassoc_ty = check rconcatassoc_ty uu in

  let rconcatassoc =
    Printf.sprintf
      "A m n k xs ys zs ↦ Vec_ind A (m xs ↦ Id (Vec A) (%s (%s m n) k) (%s m (%s n k)) (%s m n k) (%s A (%s m n) k (%s A m n xs ys) zs) (%s A m (%s n k) xs (%s A n k ys zs))) (refl (%s A n k ys zs)) (m x xs IH ↦ cons. (%s m n k) (refl x) IH) m xs"
      lp lp lp lp lpa cc lp cc cc lp cc cc lpa in

  let concatassoc =
    check rconcatassoc concatassoc_ty
    (* And similarly right unital. *) in

  let rconcatru_ty =
    Printf.sprintf
      "(A:Type) (m:ℕ) (xs : Vec A m) → Id (Vec A) (%s m 0) m (%s m) (%s A m 0 xs nil.) xs" lp lpr cc
  in

  let concatru_ty = check rconcatru_ty uu in

  let rconcatru =
    Printf.sprintf
      "A m xs ↦ Vec_ind A (m xs ↦ Id (Vec A) (%s m 0) m (%s m) (%s A m 0 xs nil.) xs) nil. (m x xs IH ↦ cons. (%s m) (refl x) IH) m xs"
      lp lpr cc lpr in

  let concatru = check rconcatru concatru_ty in
  ()
