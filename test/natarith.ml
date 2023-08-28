open Pmp

let () = Narya.Nat.install ()
let nat, _ = synth !~"N"
let raw0 = !~"0"
let zero, nat0 = synth raw0
let () = equal nat nat0
let raw1 = !~"S" $ raw0
let one, nat1 = synth raw1
let () = equal nat nat1
let raw2 = !~"S" $ raw1
let two, _ = synth raw2
let three, _ = synth (!~"S" $ raw2)
let one_plus_one, _ = synth (!~"+" $ raw1 $ raw1)
let () = equal one_plus_one two
let () = unequal one_plus_one one
let () = unequal one_plus_one three
let one_plus_two, _ = synth (!~"+" $ raw1 $ raw2)
let () = equal one_plus_two three
let () = unequal one_plus_two one
let two_plus_zero, _ = synth (!~"+" $ raw2 $ raw0)
let () = equal two_plus_zero two
let zero_plus_zero, _ = synth (!~"+" $ raw0 $ raw0)
let () = equal zero_plus_zero zero
let zero_plus_one, _ = synth (!~"+" $ raw0 $ raw1)
let () = equal zero_plus_one one
let zero_plus_two, _ = synth (!~"+" $ raw0 $ raw2)
let () = equal zero_plus_two two

(* Refl of a constant still computes *)
let refl_zero_plus_zero, _ = synth (refl !~"+" $ raw0 $ raw0 $ refl raw0 $ raw0 $ raw0 $ refl raw0)
let refl_zero, _ = synth (refl raw0)
let () = equal refl_zero_plus_zero refl_zero
let refl_one_plus_one, _ = synth (refl !~"+" $ raw1 $ raw1 $ refl raw1 $ raw1 $ raw1 $ refl raw1)
let refl_one, _ = synth (refl raw1)
let refl_two, _ = synth (refl raw2)
let () = equal refl_one_plus_one refl_two
let () = unequal refl_one_plus_one refl_one

(* We can also define addition with the general recursor/inductor  *)
let rop = ("", !~"N") @=> ("", !~"N") @=> !~"N"

let rplus =
  "x" @-> "y" @-> (!~"ind" $ "" @-> !~"N" $ !!"x" $ "" @-> "x+y" @-> (!~"S" $ !!"x+y") $ !!"y")
  <:> rop

let plus, _ = synth rplus
let one_plus_one', _ = synth (rplus $ raw1 $ raw1)
let () = equal one_plus_one' two
let () = unequal one_plus_one' one
let () = unequal one_plus_one' three
let one_plus_two', _ = synth (rplus $ raw1 $ raw2)
let () = equal one_plus_two' three
let () = unequal one_plus_two' one
let two_plus_zero', _ = synth (rplus $ raw2 $ raw0)
let () = equal two_plus_zero' two
let zero_plus_zero', _ = synth (rplus $ raw0 $ raw0)
let () = equal zero_plus_zero' zero
let zero_plus_one', _ = synth (rplus $ raw0 $ raw1)
let () = equal zero_plus_one' one
let zero_plus_two', _ = synth (rplus $ raw0 $ raw2)
let () = equal zero_plus_two' two

(* And prove by induction that it equals the other one.  Note that this uses ap on suc. *)
let plus_is_plus_ty, _ =
  synth (("x", !~"N") @=> ("y", !~"N") @=> id !~"N" (!~"+" $ !!"x" $ !!"y") (rplus $ !!"x" $ !!"y"))

let plus_is_plus =
  check
    ("x"
    @-> "y"
    @-> (!~"ind"
        $ "u" @-> id !~"N" (!~"+" $ !!"x" $ !!"u") (rplus $ !!"x" $ !!"u")
        $ refl !!"x"
        $ "u"
          @-> "equ"
          @-> (refl !~"S" $ (!~"+" $ !!"x" $ !!"u") $ (rplus $ !!"x" $ !!"u") $ !!"equ")
        $ !!"y"))
    plus_is_plus_ty
