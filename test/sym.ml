open Pmp

let uu, _ = synth UU
let xx = assume "X" uu
let x00 = assume "x00" xx
let x01 = assume "x01" xx
let xx02, _ = synth (id !!"X" !!"x00" !!"x01")
let x02 = assume "x02" xx02
let x10 = assume "x10" xx
let x11 = assume "x11" xx
let xx12, _ = synth (id !!"X" !!"x10" !!"x11")
let x12 = assume "x12" xx12
let xx20, _ = synth (id !!"X" !!"x00" !!"x10")
let xx21, _ = synth (id !!"X" !!"x01" !!"x11")
let x20 = assume "x20" xx20
let x21 = assume "x21" xx21

(* We can't apply symmetry to 0- or 1-dimensional things *)
let () = unsynth (sym !!"x00")
let () = unsynth (sym !!"x02")

let xx22, _ =
  synth
    (refl (refl !!"X")
    $ !!"x00"
    $ !!"x01"
    $ !!"x02"
    $ !!"x10"
    $ !!"x11"
    $ !!"x12"
    $ !!"x20"
    $ !!"x21")

let x22 = assume "x22" xx22

(* We can apply symmetry to a square, and the result has a different type in general. *)
let sx22, sxx22 = synth (sym !!"x22")
let () = unequal xx22 sxx22

(* Its type has transposed boundary *)
let sxx22', _ =
  synth
    (refl (refl !!"X")
    $ !!"x00"
    $ !!"x10"
    $ !!"x20"
    $ !!"x01"
    $ !!"x11"
    $ !!"x21"
    $ !!"x02"
    $ !!"x12")

let () = equal sxx22 sxx22'

(* Symmetry is an involution *)
let ssx22, ssxx22 = synth (sym (sym !!"x22"))
let () = equal ssxx22 xx22
let () = equal ssx22 x22

(* The action of functions on squares preserves symmetry *)
let yy = assume "Y" uu
let xtoy, _ = synth (("x", !!"X") @=> !!"Y")
let f = assume "f" xtoy

let fx22, fx22ty =
  synth
    (refl (refl !!"f")
    $ !!"x00"
    $ !!"x01"
    $ !!"x02"
    $ !!"x10"
    $ !!"x11"
    $ !!"x12"
    $ !!"x20"
    $ !!"x21"
    $ !!"x22")

let sfx22, sfx22ty =
  synth
    (sym
       (refl (refl !!"f")
       $ !!"x00"
       $ !!"x01"
       $ !!"x02"
       $ !!"x10"
       $ !!"x11"
       $ !!"x12"
       $ !!"x20"
       $ !!"x21"
       $ !!"x22"))

let fsx22, fsx22ty =
  synth
    (refl (refl !!"f")
    $ !!"x00"
    $ !!"x10"
    $ !!"x20"
    $ !!"x01"
    $ !!"x11"
    $ !!"x21"
    $ !!"x02"
    $ !!"x12"
    $ sym !!"x22")

let () = equal sfx22ty fsx22ty
let () = equal sfx22 fsx22
