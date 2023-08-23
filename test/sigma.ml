open Pmp

let () = Narya.Sigma.install ()
let uu, _ = synth UU
let aa = assume "A" uu
let atou, _ = synth (("", !!"A") @=> UU)
let bb = assume "B" atou
let ss, _ = synth (!~"Sig" $ !!"A" $ !!"B")

(* Pairs have the correct type *)
let a = assume "a" aa
let bba, _ = synth (!!"B" $ !!"a")
let b = assume "b" bba
let rs = !~"pair" $ !!"A" $ !!"B" $ !!"a" $ !!"b"
let s, sty = synth rs
let () = equal sty ss

(* Projections have the correct type *)
let x = assume "x" ss
let x1, x1ty = synth (!!"x" $. "fst")
let () = equal x1ty aa
let x2, x2ty = synth (!!"x" $. "snd")
let () = unequal x2ty bba
let x2ty', _ = synth (!!"B" $ (!!"x" $. "fst"))
let () = equal x2ty x2ty'

(* Projections of pairs compute *)
let a', aa' = synth (rs $. "fst")
let () = equal aa' aa
let () = equal_at a a' aa
let b', bba' = synth (rs $. "snd")
let () = equal bba' bba
let () = equal b b'

(* Projections satisfy eta-conversion *)
let x' = check (!~"pair" $ !!"A" $ !!"B" $ (!!"x" $. "fst") $ (!!"x" $. "snd")) ss
let () = equal_at x x' ss
let () = unequal x x' (* Need typed equality for eta! *)

(* Identifications can be paired to give an identification of pairs *)
let a0 = assume "a0" aa
let bba0, _ = synth (!!"B" $ !!"a0")
let b0 = assume "b0" bba0
let a1 = assume "a1" aa
let bba1, _ = synth (!!"B" $ !!"a1")
let b1 = assume "b1" bba1
let ida0a1, _ = synth (id !!"A" !!"a0" !!"a1")
let a2 = assume "a2" ida0a1
let idb0b1, _ = synth (refl !!"B" $ !!"a0" $ !!"a1" $ !!"a2" $ !!"b0" $ !!"b1")
let b2 = assume "b2" idb0b1
let s0 = check (!~"pair" $ !!"A" $ !!"B" $ !!"a0" $ !!"b0") ss
let s1 = check (!~"pair" $ !!"A" $ !!"B" $ !!"a1" $ !!"b1") ss

let ids0s1, _ =
  synth
    (id
       (!~"Sig" $ !!"A" $ !!"B")
       (!~"pair" $ !!"A" $ !!"B" $ !!"a0" $ !!"b0")
       (!~"pair" $ !!"A" $ !!"B" $ !!"a1" $ !!"b1"))

let rs2 =
  refl !~"pair"
  $ !!"A"
  $ !!"A"
  $ refl !!"A"
  $ !!"B"
  $ !!"B"
  $ refl !!"B"
  $ !!"a0"
  $ !!"a1"
  $ !!"a2"
  $ !!"b0"
  $ !!"b1"
  $ !!"b2"

let s2 = check rs2 ids0s1

(* And projected back out again to the inputs *)
let a2', ida0a1' = synth (rs2 $. "fst")
let () = equal ida0a1 ida0a1'
let b2', idb0b1' = synth (rs2 $. "snd")
let () = equal idb0b1 idb0b1'

(* Refl commutes with pairing *)
let refls, _ = synth (refl (!~"pair" $ !!"A" $ !!"B" $ !!"a" $ !!"b"))

let refls', _ =
  synth
    (refl !~"pair"
    $ !!"A"
    $ !!"A"
    $ refl !!"A"
    $ !!"B"
    $ !!"B"
    $ refl !!"B"
    $ !!"a"
    $ !!"a"
    $ refl !!"a"
    $ !!"b"
    $ !!"b"
    $ refl !!"b")

let () = equal refls refls'
