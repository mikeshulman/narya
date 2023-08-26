open Pmp

let () = Narya.Stream.install ()
let uu, _ = synth UU
let aa = assume "A" uu
let straa, _ = synth (!~"Stream" $ !!"A")

(* We suppose a stream and take some parts of it *)
let s = assume "s" straa
let s0 = check (!!"s" $. "head") aa
let s0t = check (!!"s" $. "tail") straa
let s1 = check (!!"s" $. "tail" $. "head") aa
let s2 = check (!!"s" $. "tail" $. "tail" $. "head") aa

(* Streams don't satisfy eta-conversion *)
let s' = check (struc [ ("head", !!"s" $. "head"); ("tail", !!"s" $. "tail") ]) straa
let () = unequal_at s s' straa

let rs' =
  !~"corec"
  $ !!"A"
  $ (!~"Stream" $ !!"A")
  $ "x" @-> (!!"x" $. "head")
  $ "x" @-> (!!"x" $. "tail")
  $ !!"s"

let s', sty' = synth rs'
let () = equal straa sty'
let () = unequal s s'

(* Their identity/bridge types are bisimulations, but structs don't suffice to prove this, as the tails are not yet equal. *)

let s0' = check (rs' $. "head") aa
let () = equal s0 s0'
let s0t' = check (rs' $. "tail") straa
let () = unequal s0t s0t'

(* refl corec doesn't suffice to prove this either, as it only equates two values of corec.  A bisimulation must be defined by a full coinduction, which requires a new operation defined by a higher-dimensional copattern case tree. *)

(* We construct a stream of natural numbers and check its first few elements *)

let () = Narya.Nat.install ()
let rnats = !~"corec" $ !~"N" $ !~"N" $ "x" @-> !!"x" $ "x" @-> (!~"S" $ !!"x") $ !~"0"
let nats, _ = synth rnats
let zero, _ = synth !~"0"
let zero', _ = synth (rnats $. "head")
let () = equal zero zero'
let one, _ = synth (!~"S" $ !~"0")
let one', _ = synth (rnats $. "tail" $. "head")
let () = equal one one'
let two, _ = synth (!~"S" $ (!~"S" $ !~"0"))
let two', _ = synth (rnats $. "tail" $. "tail" $. "head")
let () = equal two two'
let three, _ = synth (!~"S" $ (!~"S" $ (!~"S" $ !~"0")))
let three', _ = synth (rnats $. "tail" $. "tail" $. "tail" $. "head")
let () = equal three three'
let () = Narya.Sigma.install ()

(* Now we construct the stream of fibonacci numbers and check the first few of its elements *)

let rfib =
  !~"corec"
  $ !~"N"
  $ (!~"Sig" $ !~"N" $ "" @-> !~"N")
  $ "x" @-> (!!"x" $. "fst")
  $ "x" @-> struc [ ("fst", !!"x" $. "snd"); ("snd", !~"+" $ (!!"x" $. "fst") $ (!!"x" $. "snd")) ]
  $ struc [ ("fst", !~"S" $ !~"0"); ("snd", !~"S" $ !~"0") ]

let f1, _ = synth (rfib $. "head")
let () = equal f1 one
let f2, _ = synth (rfib $. "tail" $. "head")
let () = equal f2 one
let f3, _ = synth (rfib $. "tail" $. "tail" $. "head")
let () = equal f3 two
let f4, _ = synth (rfib $. "tail" $. "tail" $. "tail" $. "head")
let () = equal f4 three
let five, _ = synth (!~"S" $ (!~"S" $ (!~"S" $ (!~"S" $ (!~"S" $ !~"0")))))
let f5, _ = synth (rfib $. "tail" $. "tail" $. "tail" $. "tail" $. "head")
let () = equal f5 five

let eight, _ =
  synth (!~"S" $ (!~"S" $ (!~"S" $ (!~"S" $ (!~"S" $ (!~"S" $ (!~"S" $ (!~"S" $ !~"0"))))))))

let f6, _ = synth (rfib $. "tail" $. "tail" $. "tail" $. "tail" $. "tail" $. "head")
let () = equal f6 eight
