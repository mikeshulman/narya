open Pmp

let () = Narya.Gel.install ()
let ggel, ggelty = synth !~"Gel"

let ggelty', _ =
  synth
    (("X", UU) @=> ("Y", UU) @=> ("R", ("x", !!"X") @=> ("y", !!"Y") @=> UU) @=> id UU !!"X" !!"Y")

let () = equal ggelty ggelty'

let gelty, _ =
  synth
    (("X", UU)
    @=> ("Y", UU)
    @=> ("R", ("x", !!"X") @=> ("y", !!"Y") @=> UU)
    @=> ("x", !!"X")
    @=> ("y", !!"Y")
    @=> ("r", !!"R" $ !!"x" $ !!"y")
    @=> (!~"Gel" $ !!"X" $ !!"Y" $ !!"R" $ !!"x" $ !!"y"))

let rgel x = struc [ ("ungel", x) ]
let gel = check ("X" @-> "Y" @-> "R" @-> "x" @-> "y" @-> "r" @-> rgel !!"r")

let ungelty, _ =
  synth
    (("X", UU)
    @=> ("Y", UU)
    @=> ("R", ("x", !!"X") @=> ("y", !!"Y") @=> UU)
    @=> ("x", !!"X")
    @=> ("y", !!"Y")
    @=> ("r", !~"Gel" $ !!"X" $ !!"Y" $ !!"R" $ !!"x" $ !!"y")
    @=> (!!"R" $ !!"x" $ !!"y"))

let ungel = check ("X" @-> "Y" @-> "R" @-> "x" @-> "y" @-> "r" @-> (!!"r" $. "ungel")) ungelty

(* Now we set up some assumptions *)

let uu, _ = synth UU
let aa = assume "A" uu
let bb = assume "B" uu
let corrab, _ = synth (("x", !!"A") @=> ("y", !!"B") @=> UU)
let rr = assume "R" corrab
let a = assume "a" aa
let b = assume "b" bb
let _, corrab' = synth !!"R"
let () = equal corrab corrab'
let rab, _ = synth (!!"R" $ !!"a" $ !!"b")

(* We test ungel(gel)  *)

let r = assume "r" rab
let r', _ = synth (rgel !!"r" <:> (!~"Gel" $ !!"A" $ !!"B" $ !!"R" $ !!"a" $ !!"b") $. "ungel")
let () = equal r r'

(* and gel(ungel) *)

let gelab, _ = synth (!~"Gel" $ !!"A" $ !!"B" $ !!"R" $ !!"a" $ !!"b")
let s = assume "s" gelab
let s' = check (rgel (!!"s" $. "ungel")) gelab
let () = equal_at s s' gelab
