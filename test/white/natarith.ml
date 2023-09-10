open Testutil.Pmp

let () = Types.Nat.install ()
let nat, _ = synth !~"N"
let raw0 = !."O"
let zero = check raw0 nat
let raw1 = !."S" $ raw0
let one = check raw1 nat
let raw2 = !."S" $ raw1
let two = check raw2 nat
let raw3 = !."S" $ raw2
let three = check raw3 nat
let raw4 = !."S" $ raw3
let four = check raw4 nat

(* Identity types *)
let id00, _ = synth (id !~"N" !."O" !."O")
let eq00 = check !."O" id00
let id01, _ = synth (id !~"N" !."O" (!."S" $ !."O"))
let () = uncheck !."O" id01
let id11, _ = synth (id !~"N" raw1 raw1)
let eq11 = check (!."S" $ !."O") id11

let congsuc_ty, _ =
  synth
    (("x", !~"N")
    @=> ("y", !~"N")
    @=> ("", id !~"N" !!"x" !!"y")
    @=> id !~"N" (!."S" $ !!"x") (!."S" $ !!"y"))

let congsuc = check ("x" @-> "y" @-> "p" @-> (!."S" $ !!"p")) congsuc_ty

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
        $ (!."S" $ !!"x00")
        $ (!."S" $ !!"x01")
        $ (!."S" $ !!"x02")
        $ (!."S" $ !!"x10")
        $ (!."S" $ !!"x11")
        $ (!."S" $ !!"x12")
        $ (!."S" $ !!"x20")
        $ (!."S" $ !!"x21")))

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
    @-> (!."S" $ !!"x22"))
    cong2suc_ty

(* Addition *)
let one_plus_one, _ = synth (!~"plus" $ raw1 $ raw1)
let () = equal_at one_plus_one two nat
let () = unequal_at one_plus_one one nat
let () = unequal_at one_plus_one three nat
let one_plus_two, _ = synth (!~"plus" $ raw1 $ raw2)
let () = equal_at one_plus_two three nat
let () = unequal_at one_plus_two one nat
let two_plus_zero, _ = synth (!~"plus" $ raw2 $ raw0)
let () = equal_at two_plus_zero two nat
let zero_plus_zero, _ = synth (!~"plus" $ raw0 $ raw0)
let () = equal_at zero_plus_zero zero nat
let zero_plus_one, _ = synth (!~"plus" $ raw0 $ raw1)
let () = equal_at zero_plus_one one nat
let zero_plus_two, _ = synth (!~"plus" $ raw0 $ raw2)
let () = equal_at zero_plus_two two nat

(* Refl of a constant still computes *)
let refl_zero_plus_zero, _ =
  synth (refl !~"plus" $ raw0 $ raw0 $ refl (raw0 <:> !~"N") $ raw0 $ raw0 $ refl (raw0 <:> !~"N"))

let refl_zero, _ = synth (refl (raw0 <:> !~"N"))
let id_zero_zero, _ = synth (id !~"N" !."O" !."O")
let () = equal_at refl_zero_plus_zero refl_zero id_zero_zero

let refl_one_plus_one, _ =
  synth (refl !~"plus" $ raw1 $ raw1 $ refl (raw1 <:> !~"N") $ raw1 $ raw1 $ refl (raw1 <:> !~"N"))

let refl_one, _ = synth (refl (raw1 <:> !~"N"))
let refl_two, _ = synth (refl (raw2 <:> !~"N"))
let id_two_two, _ = synth (id !~"N" (!."S" $ (!."S" $ !."O")) (!."S" $ (!."S" $ !."O")))
let () = equal_at refl_one_plus_one refl_two id_two_two

(* We can also define addition with the general recursor/inductor  *)
let rop = ("", !~"N") @=> ("", !~"N") @=> !~"N"

let rplus =
  "x" @-> "y" @-> (!~"N_ind" $ "" @-> !~"N" $ !!"x" $ "" @-> "x+y" @-> (!~"S" $ !!"x+y") $ !!"y")
  <:> rop

let plus, _ = synth rplus
let one_plus_one', _ = synth (rplus $ raw1 $ raw1)
let () = equal_at one_plus_one' two nat
let () = unequal_at one_plus_one' one nat
let () = unequal_at one_plus_one' three nat
let one_plus_two', _ = synth (rplus $ raw1 $ raw2)
let () = equal_at one_plus_two' three nat
let () = unequal_at one_plus_two' one nat
let two_plus_zero', _ = synth (rplus $ raw2 $ raw0)
let () = equal_at two_plus_zero' two nat
let zero_plus_zero', _ = synth (rplus $ raw0 $ raw0)
let () = equal_at zero_plus_zero' zero nat
let zero_plus_one', _ = synth (rplus $ raw0 $ raw1)
let () = equal_at zero_plus_one' one nat
let zero_plus_two', _ = synth (rplus $ raw0 $ raw2)
let () = equal_at zero_plus_two' two nat

(* And prove by induction that it equals the other one.  Note that this uses ap on suc. *)
let plus_is_plus_ty, _ =
  synth
    (("x", !~"N") @=> ("y", !~"N") @=> id !~"N" (!~"plus" $ !!"x" $ !!"y") (rplus $ !!"x" $ !!"y"))

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
    plus_is_plus_ty

(* We also have multiplication *)
let one_times_zero, _ = synth (!~"times" $ raw1 $ raw0)
let () = equal_at one_times_zero zero nat
let zero_times_one, _ = synth (!~"times" $ raw0 $ raw1)
let () = equal_at zero_times_one zero nat
let one_times_one, _ = synth (!~"times" $ raw1 $ raw1)
let () = equal_at one_times_one one nat
let two_times_two, _ = synth (!~"times" $ raw2 $ raw2)
let () = equal_at two_times_two four nat
