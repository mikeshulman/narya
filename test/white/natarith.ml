open Testutil.Pmp

let () =
  run @@ fun () ->
  Types.Nat.install ();
  let nat, _ = synth !~"N" in
  let raw0 = !."0" in
  let zero = check raw0 nat in
  let raw1 = !."1" $ raw0 in
  let one = check raw1 nat in
  let raw2 = !."1" $ raw1 in
  let two = check raw2 nat in
  let raw3 = !."1" $ raw2 in
  let three = check raw3 nat in
  let raw4 = !."1" $ raw3 in
  let four = check raw4 nat in

  (* Identity types *)
  let id00, _ = synth (id !~"N" !."0" !."0") in
  let eq00 = check !."0" id00 in
  let id01, _ = synth (id !~"N" !."0" (!."1" $ !."0")) in
  let () = uncheck !."0" id01 in
  let id11, _ = synth (id !~"N" raw1 raw1) in
  let eq11 = check (!."1" $ !."0") id11 in

  let congsuc_ty, _ =
    synth
      (("x", !~"N")
      @=> ("y", !~"N")
      @=> ("", id !~"N" !!"x" !!"y")
      @=> id !~"N" (!."1" $ !!"x") (!."1" $ !!"y")) in

  let congsuc = check ("x" @-> "y" @-> "p" @-> (!."1" $ !!"p")) congsuc_ty in

  let cong2suc_ty, _ =
    synth
      (("x00", !~"N")
      @=> ("x01", !~"N")
      @=> ("x02", id !~"N" !!"x00" !!"x01")
      @=> ("x10", !~"N")
      @=> ("x11", !~"N")
      @=> ("x12", id !~"N" !!"x10" !!"x11")
      @=> ("x20", id !~"N" !!"x00" !!"x10")
      @=> ("x21", id !~"N" !!"x01" !!"x11")
      @=> ( "x22",
            refl (refl !~"N")
            $ !!"x00"
            $ !!"x01"
            $ !!"x02"
            $ !!"x10"
            $ !!"x11"
            $ !!"x12"
            $ !!"x20"
            $ !!"x21" )
      @=> (refl (refl !~"N")
          $ (!."1" $ !!"x00")
          $ (!."1" $ !!"x01")
          $ (!."1" $ !!"x02")
          $ (!."1" $ !!"x10")
          $ (!."1" $ !!"x11")
          $ (!."1" $ !!"x12")
          $ (!."1" $ !!"x20")
          $ (!."1" $ !!"x21"))) in

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
      @-> (!."1" $ !!"x22"))
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
    synth (refl !~"plus" $ raw0 $ raw0 $ refl (raw0 <:> !~"N") $ raw0 $ raw0 $ refl (raw0 <:> !~"N"))
  in

  let refl_zero, _ = synth (refl (raw0 <:> !~"N")) in
  let id_zero_zero, _ = synth (id !~"N" !."0" !."0") in
  let () = equal_at refl_zero_plus_zero refl_zero id_zero_zero in

  let refl_one_plus_one, _ =
    synth (refl !~"plus" $ raw1 $ raw1 $ refl (raw1 <:> !~"N") $ raw1 $ raw1 $ refl (raw1 <:> !~"N"))
  in

  let refl_one, _ = synth (refl (raw1 <:> !~"N")) in
  let refl_two, _ = synth (refl (raw2 <:> !~"N")) in
  let id_two_two, _ = synth (id !~"N" (!."1" $ (!."1" $ !."0")) (!."1" $ (!."1" $ !."0"))) in
  let () = equal_at refl_one_plus_one refl_two id_two_two in

  (* We can also define addition with the general recursor/inductor  *)
  let rop = ("", !~"N") @=> ("", !~"N") @=> !~"N" in

  let rplus =
    "x" @-> "y" @-> (!~"N_ind" $ "" @-> !~"N" $ !!"x" $ "" @-> "x+y" @-> (!~"S" $ !!"x+y") $ !!"y")
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
      (("x", !~"N") @=> ("y", !~"N") @=> id !~"N" (!~"plus" $ !!"x" $ !!"y") (rplus $ !!"x" $ !!"y"))
  in

  let plus_is_plus =
    check
      ("x"
      @-> "y"
      @-> (!~"N_ind"
          $ "u" @-> id !~"N" (!~"plus" $ !!"x" $ !!"u") (rplus $ !!"x" $ !!"u")
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
