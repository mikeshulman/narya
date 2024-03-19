open Testutil.Pmp

let () =
  run @@ fun () ->
  Testutil.Repl.(
    def "ℕ" "Type" "data [ zero. | suc. (_ : ℕ) ]";
    def "O" "ℕ" "zero.";
    def "S" "ℕ → ℕ" "n ↦ suc. n";
    def "plus" "ℕ → ℕ → ℕ"
      "m n ↦ match n [
       | zero. ↦ m
       | suc. n ↦ suc. (plus m n)
     ]";
    def "times" "ℕ → ℕ → ℕ"
      "m n ↦ match n [
       | zero. ↦ zero.
       | suc. n ↦ plus (times m n) m
     ]";
    def "ℕ_ind" "(P : ℕ → Type) (z : P zero.) (s : (n:ℕ) → P n → P (suc. n)) (n : ℕ) → P n"
      "P z s n ↦ match n [
       | zero. ↦ z
       | suc. n ↦ s n (ℕ_ind P z s n)
     ]");
  let nat, _ = synth !~"ℕ" in
  let raw0 = !."zero" in
  let zero = check raw0 nat in
  let raw1 = !."suc" $ raw0 in
  let one = check raw1 nat in
  let raw2 = !."suc" $ raw1 in
  let two = check raw2 nat in
  let raw3 = !."suc" $ raw2 in
  let three = check raw3 nat in
  let raw4 = !."suc" $ raw3 in
  let four = check raw4 nat in

  (* Identity types *)
  let id00, _ = synth (id !~"ℕ" !."zero" !."zero") in
  let eq00 = check !."zero" id00 in
  let id01, _ = synth (id !~"ℕ" !."zero" (!."suc" $ !."zero")) in
  let () = uncheck !."zero" id01 in
  let id11, _ = synth (id !~"ℕ" raw1 raw1) in
  let eq11 = check (!."suc" $ !."zero") id11 in

  let congsuc_ty, _ =
    synth
      (("x", !~"ℕ")
      @=> ("y", !~"ℕ")
      @=> ("", id !~"ℕ" !!"x" !!"y")
      @=> id !~"ℕ" (!."suc" $ !!"x") (!."suc" $ !!"y")) in

  let congsuc = check ("x" @-> "y" @-> "p" @-> (!."suc" $ !!"p")) congsuc_ty in

  let cong2suc_ty, _ =
    synth
      (("x00", !~"ℕ")
      @=> ("x01", !~"ℕ")
      @=> ("x02", id !~"ℕ" !!"x00" !!"x01")
      @=> ("x10", !~"ℕ")
      @=> ("x11", !~"ℕ")
      @=> ("x12", id !~"ℕ" !!"x10" !!"x11")
      @=> ("x20", id !~"ℕ" !!"x00" !!"x10")
      @=> ("x21", id !~"ℕ" !!"x01" !!"x11")
      @=> ( "x22",
            refl (refl !~"ℕ")
            $ !!"x00"
            $ !!"x01"
            $ !!"x02"
            $ !!"x10"
            $ !!"x11"
            $ !!"x12"
            $ !!"x20"
            $ !!"x21" )
      @=> (refl (refl !~"ℕ")
          $ (!."suc" $ !!"x00")
          $ (!."suc" $ !!"x01")
          $ (!."suc" $ !!"x02")
          $ (!."suc" $ !!"x10")
          $ (!."suc" $ !!"x11")
          $ (!."suc" $ !!"x12")
          $ (!."suc" $ !!"x20")
          $ (!."suc" $ !!"x21"))) in

  let cong2suc =
    check
      ("x00"
      @-> "x01"
      @-> "x02"
      @-> "x10"
      @-> "x11"
      @-> "x12"
      @-> "x20"
      @-> "x21"
      @-> "x22"
      @-> (!."suc" $ !!"x22"))
      cong2suc_ty in

  (* Addition *)
  let one_plus_one, _ = synth (!~"plus" $ raw1 $ raw1) in
  let () = equal_at one_plus_one two nat in
  let () = unequal_at one_plus_one one nat in
  let () = unequal_at one_plus_one three nat in
  let one_plus_two, _ = synth (!~"plus" $ raw1 $ raw2) in
  let () = equal_at one_plus_two three nat in
  let () = unequal_at one_plus_two one nat in
  let two_plus_zero, _ = synth (!~"plus" $ raw2 $ raw0) in
  let () = equal_at two_plus_zero two nat in
  let zero_plus_zero, _ = synth (!~"plus" $ raw0 $ raw0) in
  let () = equal_at zero_plus_zero zero nat in
  let zero_plus_one, _ = synth (!~"plus" $ raw0 $ raw1) in
  let () = equal_at zero_plus_one one nat in
  let zero_plus_two, _ = synth (!~"plus" $ raw0 $ raw2) in
  let () = equal_at zero_plus_two two nat in

  (* Refl of a constant still computes *)
  let refl_zero_plus_zero, _ =
    synth (refl !~"plus" $ raw0 $ raw0 $ refl (raw0 <:> !~"ℕ") $ raw0 $ raw0 $ refl (raw0 <:> !~"ℕ"))
  in

  let refl_zero, _ = synth (refl (raw0 <:> !~"ℕ")) in
  let id_zero_zero, _ = synth (id !~"ℕ" !."zero" !."zero") in
  let () = equal_at refl_zero_plus_zero refl_zero id_zero_zero in

  let refl_one_plus_one, _ =
    synth (refl !~"plus" $ raw1 $ raw1 $ refl (raw1 <:> !~"ℕ") $ raw1 $ raw1 $ refl (raw1 <:> !~"ℕ"))
  in

  let refl_one, _ = synth (refl (raw1 <:> !~"ℕ")) in
  let refl_two, _ = synth (refl (raw2 <:> !~"ℕ")) in
  let id_two_two, _ =
    synth (id !~"ℕ" (!."suc" $ (!."suc" $ !."zero")) (!."suc" $ (!."suc" $ !."zero"))) in
  let () = equal_at refl_one_plus_one refl_two id_two_two in

  (* We can also define addition with the general recursor/inductor  *)
  let rop = ("", !~"ℕ") @=> ("", !~"ℕ") @=> !~"ℕ" in

  let rplus =
    "x" @-> "y" @-> (!~"ℕ_ind" $ "" @-> !~"ℕ" $ !!"x" $ "" @-> "x+y" @-> (!~"S" $ !!"x+y") $ !!"y")
    <:> rop in

  let plus, _ = synth rplus in
  let one_plus_one', _ = synth (rplus $ raw1 $ raw1) in
  let () = equal_at one_plus_one' two nat in
  let () = unequal_at one_plus_one' one nat in
  let () = unequal_at one_plus_one' three nat in
  let one_plus_two', _ = synth (rplus $ raw1 $ raw2) in
  let () = equal_at one_plus_two' three nat in
  let () = unequal_at one_plus_two' one nat in
  let two_plus_zero', _ = synth (rplus $ raw2 $ raw0) in
  let () = equal_at two_plus_zero' two nat in
  let zero_plus_zero', _ = synth (rplus $ raw0 $ raw0) in
  let () = equal_at zero_plus_zero' zero nat in
  let zero_plus_one', _ = synth (rplus $ raw0 $ raw1) in
  let () = equal_at zero_plus_one' one nat in
  let zero_plus_two', _ = synth (rplus $ raw0 $ raw2) in
  let () = equal_at zero_plus_two' two nat in

  (* And prove by induction that it equals the other one.  Note that this uses ap on suc. *)
  let plus_is_plus_ty, _ =
    synth
      (("x", !~"ℕ") @=> ("y", !~"ℕ") @=> id !~"ℕ" (!~"plus" $ !!"x" $ !!"y") (rplus $ !!"x" $ !!"y"))
  in

  let plus_is_plus =
    check
      ("x"
      @-> "y"
      @-> (!~"ℕ_ind"
          $ "u" @-> id !~"ℕ" (!~"plus" $ !!"x" $ !!"u") (rplus $ !!"x" $ !!"u")
          $ refl !!"x"
          $ "u"
            @-> "equ"
            @-> (refl !~"S" $ (!~"plus" $ !!"x" $ !!"u") $ (rplus $ !!"x" $ !!"u") $ !!"equ")
          $ !!"y"))
      plus_is_plus_ty in

  (* We also have multiplication *)
  let one_times_zero, _ = synth (!~"times" $ raw1 $ raw0) in
  let () = equal_at one_times_zero zero nat in
  let zero_times_one, _ = synth (!~"times" $ raw0 $ raw1) in
  let () = equal_at zero_times_one zero nat in
  let one_times_one, _ = synth (!~"times" $ raw1 $ raw1) in
  let () = equal_at one_times_one one nat in
  let two_times_two, _ = synth (!~"times" $ raw2 $ raw2) in
  let () = equal_at two_times_two four nat in
  ()
