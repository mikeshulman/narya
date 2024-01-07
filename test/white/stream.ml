open Testutil.Pmp

let () =
  run @@ fun () ->
  Types.Stream.install ();
  let uu, _ = synth UU in
  let aa = assume "A" uu in
  let straa, _ = synth (!~"Stream" $ !!"A") in

  (* We suppose a stream and take some parts of it *)
  let s = assume "s" straa in
  let s0 = check (!!"s" $. "head") aa in
  let s0t = check (!!"s" $. "tail") straa in
  let s1 = check (!!"s" $. "tail" $. "head") aa in
  let s2 = check (!!"s" $. "tail" $. "tail" $. "head") aa in

  (* With structs, we can define a one-step eta-expansion, and see that streams don't satisfy eta-conversion. *)
  let rs' = struc [ ("head", !!"s" $. "head"); ("tail", !!"s" $. "tail") ] in
  let s' = check rs' straa in
  let () = unequal_at s s' straa in

  (* Their identity/bridge types are bisimulations.  We can use this to prove propositional one-step eta-conversion. *)
  let s0' = check (rs' <:> (!~"Stream" $ !!"A") $. "head") aa in
  let () = equal s0 s0' in
  let s0t' = check (rs' <:> (!~"Stream" $ !!"A") $. "tail") straa in
  let () = equal s0t s0t' in
  let s_is_s'_ty, _ = synth (id (!~"Stream" $ !!"A") !!"s" rs') in

  let s_is_s' =
    check (struc [ ("head", refl (!!"s" $. "head")); ("tail", refl (!!"s" $. "tail")) ]) s_is_s'_ty
  in

  (* Using corec, we can also define an infinitary eta-expansion. *)
  let rs'' =
    !~"corec"
    $ !!"A"
    $ (!~"Stream" $ !!"A")
    $ "x" @-> (!!"x" $. "head")
    $ "x" @-> (!!"x" $. "tail")
    $ !!"s" in

  let s'', sty'' = synth rs'' in
  let () = equal straa sty'' in
  let () = unequal s s'' in

  (* However, we can't prove this either with structs (since it's more than one step) or with "refl corec" (since it can only equate two values of corec).  We need a more general bisimulation, which must be defined by a full coinduction, which in turn requires a new operation defined by a higher-dimensional copattern case tree. *)

  (* We construct a stream of natural numbers and check its first few elements *)
  let () = Types.Nat.install () in
  let nat, _ = synth !~"ℕ" in
  let rnats = !~"corec" $ !~"ℕ" $ !~"ℕ" $ "x" @-> !!"x" $ "x" @-> (!~"S" $ !!"x") $ !~"O" in
  let nats, _ = synth rnats in
  let zero, _ = synth !~"O" in
  let zero', _ = synth (rnats $. "head") in
  let () = equal_at zero zero' nat in
  let one, _ = synth (!~"S" $ !~"O") in
  let one', _ = synth (rnats $. "tail" $. "head") in
  let () = equal_at one one' nat in
  let two, _ = synth (!~"S" $ (!~"S" $ !~"O")) in
  let two', _ = synth (rnats $. "tail" $. "tail" $. "head") in
  let () = equal_at two two' nat in
  let three, _ = synth (!~"S" $ (!~"S" $ (!~"S" $ !~"O"))) in
  let three', _ = synth (rnats $. "tail" $. "tail" $. "tail" $. "head") in
  let () = equal_at three three' nat in
  let () = Types.Sigma.install () in

  (* Now we construct the stream of fibonacci numbers and check the first few of its elements *)
  let rfib =
    !~"corec"
    $ !~"ℕ"
    $ (!~"Σ" $ !~"ℕ" $ "" @-> !~"ℕ")
    $ "x" @-> (!!"x" $. "fst")
    $ "x"
      @-> struc [ ("fst", !!"x" $. "snd"); ("snd", !~"plus" $ (!!"x" $. "fst") $ (!!"x" $. "snd")) ]
    $ struc [ ("fst", !~"S" $ !~"O"); ("snd", !~"S" $ !~"O") ] in

  let f1, _ = synth (rfib $. "head") in
  let () = equal_at f1 one nat in
  let f2, _ = synth (rfib $. "tail" $. "head") in
  let () = equal_at f2 one nat in
  let f3, _ = synth (rfib $. "tail" $. "tail" $. "head") in
  let () = equal_at f3 two nat in
  let f4, _ = synth (rfib $. "tail" $. "tail" $. "tail" $. "head") in
  let () = equal_at f4 three nat in
  let five, _ = synth (!~"S" $ (!~"S" $ (!~"S" $ (!~"S" $ (!~"S" $ !~"O"))))) in
  let f5, _ = synth (rfib $. "tail" $. "tail" $. "tail" $. "tail" $. "head") in
  let () = equal_at f5 five nat in

  let eight, _ =
    synth (!~"S" $ (!~"S" $ (!~"S" $ (!~"S" $ (!~"S" $ (!~"S" $ (!~"S" $ (!~"S" $ !~"O"))))))))
  in

  let f6, _ = synth (rfib $. "tail" $. "tail" $. "tail" $. "tail" $. "tail" $. "head") in
  let () = equal_at f6 eight nat in
  ()
