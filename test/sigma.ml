open Pmp

let () = Narya.Sigma.install ()
let uu, _ = synth UU
let aa = assume "A" uu
let atou, _ = synth (("", !!"A") @=> UU)
let bb = assume "B" atou
let rss = !~"Sig" $ !!"A" $ !!"B"
let ss, _ = synth rss

(* Pairs have the correct type *)
let a = assume "a" aa
let bba, _ = synth (!!"B" $ !!"a")
let b = assume "b" bba
let rs = !~"pair" $ !!"A" $ !!"B" $ !!"a" $ !!"b"
let s, sty = synth rs
let () = equal sty ss

(* Structs also have the correct type *)
let ( & ) x y = struc [ ("fst", x); ("snd", y) ]
let rt = !!"a" & !!"b"
let t = check rt ss

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
let () = equal a a'
let b', bba' = synth (rs $. "snd")
let () = equal bba' bba
let () = equal b b'

(* Projections of structs also compute *)
let a'', aa'' = synth (rt <:> rss $. "fst")
let () = equal aa'' aa
let () = equal a'' a
let b'', bba'' = synth (rt <:> rss $. "snd")
let () = equal bba'' bba
let () = equal b'' b

(* Projections satisfy eta-conversion for both pairs and structs *)
let x' = check (!~"pair" $ !!"A" $ !!"B" $ (!!"x" $. "fst") $ (!!"x" $. "snd")) ss
let () = equal_at x x' ss
let () = unequal x x' (* Need typed equality for eta! *)
let x'' = check (!!"x" $. "fst" & !!"x" $. "snd") ss
let () = equal_at x x'' ss
let () = equal_at x' x'' ss

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

(* As for function-types, identity types of sigma-types are invariant under eta-conversion *)
let rs0 = !~"pair" $ !!"A" $ !!"B" $ !!"a0" $ !!"b0"
let rs0' = !!"a0" & !!"b0"
let s0 = check rs0 ss
let rs1 = !~"pair" $ !!"A" $ !!"B" $ !!"a1" $ !!"b1"
let s1 = check rs1 ss
let ids0s1, _ = synth (id rss rs0 rs1)
let ids0s1', _ = synth (id rss rs0' rs1)
let () = equal ids0s1 ids0s1'

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

let rs2' = !!"a2" & !!"b2"
let s2, s2ty = synth rs2
let () = equal s2ty ids0s1
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

(* And with structs *)
let reflt, idabab = synth (refl ((!!"a" & !!"b") <:> rss))
let reflt' = check (refl !!"a" & refl !!"b") idabab
let () = equal_at reflt reflt' idabab
let () = equal_at reflt refls idabab
let () = equal_at reflt refls' idabab
let () = equal_at reflt' refls idabab
let () = equal_at reflt' refls' idabab

(* Sigmas can store identities and squares, and symmetry can act on them *)
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

let rxx22 =
  refl (refl !!"X") $ !!"x00" $ !!"x01" $ !!"x02" $ !!"x10" $ !!"x11" $ !!"x12" $ !!"x20" $ !!"x21"

let xx22, _ = synth rxx22
let x22 = assume "x22" xx22
let yy = assume "Y" uu
let y = assume "y" yy
let xx22y, _ = synth (!~"Sig" $ rxx22 $ "" @-> !!"Y")
let s = assume "s" xx22y
let () = unsynth (sym !!"s")

(* Huh, where is the problem? *)
let fsts, _ = synth (sym (!!"s" $. "fst"))
