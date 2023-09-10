open Testutil.Pmp

let () = Types.Stream.install ()
let uu, _ = synth UU
let aa = assume "A" uu
let straa, _ = synth (!~"Stream" $ !!"A")

(* We suppose a stream and take some parts of it *)
let s = assume "s" straa
let s0 = check (!!"s" $. "head") aa
let s0t = check (!!"s" $. "tail") straa
let s1 = check (!!"s" $. "tail" $. "head") aa
let s2 = check (!!"s" $. "tail" $. "tail" $. "head") aa

(* With structs, we can define a one-step eta-expansion, and see that streams don't satisfy eta-conversion. *)

let rs' = struc [ ("head", !!"s" $. "head"); ("tail", !!"s" $. "tail") ]
let s' = check rs' straa
let () = unequal_at s s' straa

(* Their identity/bridge types are bisimulations.  We can use this to prove propositional one-step eta-conversion. *)

let s0' = check (rs' <:> (!~"Stream" $ !!"A") $. "head") aa
let () = equal s0 s0'
let s0t' = check (rs' <:> (!~"Stream" $ !!"A") $. "tail") straa
let () = equal s0t s0t'
let s_is_s'_ty, _ = synth (id (!~"Stream" $ !!"A") !!"s" rs')

let s_is_s' =
  check (struc [ ("head", refl (!!"s" $. "head")); ("tail", refl (!!"s" $. "tail")) ]) s_is_s'_ty

(* Using corec, we can also define an infinitary eta-expansion. *)

let rs'' =
  !~"corec"
  $ !!"A"
  $ (!~"Stream" $ !!"A")
  $ "x" @-> (!!"x" $. "head")
  $ "x" @-> (!!"x" $. "tail")
  $ !!"s"

let s'', sty'' = synth rs''
let () = equal straa sty''
let () = unequal s s''

(* However, we can't prove this either with structs (since it's more than one step) or with "refl corec" (since it can only equate two values of corec).  We need a more general bisimulation, which must be defined by a full coinduction, which in turn requires a new operation defined by a higher-dimensional copattern case tree. *)

(* We construct a stream of natural numbers and check its first few elements *)

let () = Types.Nat.install ()
let nat, _ = synth !~"N"
let rnats = !~"corec" $ !~"N" $ !~"N" $ "x" @-> !!"x" $ "x" @-> (!~"S" $ !!"x") $ !~"O"
let nats, _ = synth rnats
let zero, _ = synth !~"O"
let zero', _ = synth (rnats $. "head")
let () = equal_at zero zero' nat
let one, _ = synth (!~"S" $ !~"O")
let one', _ = synth (rnats $. "tail" $. "head")
let () = equal_at one one' nat
let two, _ = synth (!~"S" $ (!~"S" $ !~"O"))
let two', _ = synth (rnats $. "tail" $. "tail" $. "head")
let () = equal_at two two' nat
let three, _ = synth (!~"S" $ (!~"S" $ (!~"S" $ !~"O")))
let three', _ = synth (rnats $. "tail" $. "tail" $. "tail" $. "head")
let () = equal_at three three' nat
let () = Types.Sigma.install ()

(* Now we construct the stream of fibonacci numbers and check the first few of its elements *)

let rfib =
  !~"corec"
  $ !~"N"
  $ (!~"Σ" $ !~"N" $ "" @-> !~"N")
  $ "x" @-> (!!"x" $. "fst")
  $ "x"
    @-> struc [ ("fst", !!"x" $. "snd"); ("snd", !~"plus" $ (!!"x" $. "fst") $ (!!"x" $. "snd")) ]
  $ struc [ ("fst", !~"S" $ !~"O"); ("snd", !~"S" $ !~"O") ]

let f1, _ = synth (rfib $. "head")
let () = equal_at f1 one nat
let f2, _ = synth (rfib $. "tail" $. "head")
let () = equal_at f2 one nat
let f3, _ = synth (rfib $. "tail" $. "tail" $. "head")
let () = equal_at f3 two nat
let f4, _ = synth (rfib $. "tail" $. "tail" $. "tail" $. "head")
let () = equal_at f4 three nat
let five, _ = synth (!~"S" $ (!~"S" $ (!~"S" $ (!~"S" $ (!~"S" $ !~"O")))))
let f5, _ = synth (rfib $. "tail" $. "tail" $. "tail" $. "tail" $. "head")
let () = equal_at f5 five nat

let eight, _ =
  synth (!~"S" $ (!~"S" $ (!~"S" $ (!~"S" $ (!~"S" $ (!~"S" $ (!~"S" $ (!~"S" $ !~"O"))))))))

let f6, _ = synth (rfib $. "tail" $. "tail" $. "tail" $. "tail" $. "tail" $. "head")
let () = equal_at f6 eight nat
