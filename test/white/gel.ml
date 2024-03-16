open Testutil.Pmp

let () =
  run @@ fun () ->
  Testutil.Repl.gel_install ();

  (* First we define and typecheck the basic operations Gel, gel (as a struct), and ungel (as a field). *)
  let ggel, ggelty = synth !~"Gel" in

  let ggelty', _ =
    synth
      (("X", UU) @=> ("Y", UU) @=> ("R", ("x", !!"X") @=> ("y", !!"Y") @=> UU) @=> id UU !!"X" !!"Y")
  in

  let () = equal ggelty ggelty' in

  let gelty, _ =
    synth
      (("X", UU)
      @=> ("Y", UU)
      @=> ("R", ("x", !!"X") @=> ("y", !!"Y") @=> UU)
      @=> ("x", !!"X")
      @=> ("y", !!"Y")
      @=> ("r", !!"R" $ !!"x" $ !!"y")
      @=> (!~"Gel" $ !!"X" $ !!"Y" $ !!"R" $ !!"x" $ !!"y")) in

  let rgel x = struc [ ("ungel", x) ] in
  let gel = check ("X" @-> "Y" @-> "R" @-> "x" @-> "y" @-> "r" @-> rgel !!"r") in

  let ungelty, _ =
    synth
      (("X", UU)
      @=> ("Y", UU)
      @=> ("R", ("x", !!"X") @=> ("y", !!"Y") @=> UU)
      @=> ("x", !!"X")
      @=> ("y", !!"Y")
      @=> ("r", !~"Gel" $ !!"X" $ !!"Y" $ !!"R" $ !!"x" $ !!"y")
      @=> (!!"R" $ !!"x" $ !!"y")) in

  let ungel = check ("X" @-> "Y" @-> "R" @-> "x" @-> "y" @-> "r" @-> (!!"r" $. "ungel")) ungelty in

  (* Now we set up some assumptions *)
  let uu, _ = synth UU in
  let aa = assume "A" uu in
  let bb = assume "B" uu in
  let corrab, _ = synth (("x", !!"A") @=> ("y", !!"B") @=> UU) in
  let rr = assume "R" corrab in
  let a = assume "a" aa in
  let b = assume "b" bb in
  let _, corrab' = synth !!"R" in
  let () = equal corrab corrab' in
  let rab, _ = synth (!!"R" $ !!"a" $ !!"b") in

  (* We test ungel(gel), which is a beta-reduction step. *)
  let r = assume "r" rab in
  let r', _ = synth (rgel !!"r" <:> (!~"Gel" $ !!"A" $ !!"B" $ !!"R" $ !!"a" $ !!"b") $. "ungel") in
  let () = equal r r' in

  (* and gel(ungel), which is an eta-conversion step *)
  let rgelab = !~"Gel" $ !!"A" $ !!"B" $ !!"R" $ !!"a" $ !!"b" in
  let gelab, _ = synth rgelab in
  let s = assume "s" gelab in
  let s' = check (rgel (!!"s" $. "ungel")) gelab in
  let () = equal_at s s' gelab in

  (* We can't compare gel untypedly since it is a struct, which doesn't synthesize. *)
  let () =
    match equal s s' with
    | exception _ -> ()
    | _ -> raise (Failure "Expected exception") in

  (* refl of Gel builds a square of correspondences *)
  let uu, _ = synth UU in
  let aa0 = assume "A0" uu in
  let bb0 = assume "B0" uu in
  let corrab0, _ = synth (("x", !!"A0") @=> ("y", !!"B0") @=> UU) in
  let rr0 = assume "R0" corrab0 in
  let aa1 = assume "A1" uu in
  let bb1 = assume "B1" uu in
  let corrab1, _ = synth (("x", !!"A1") @=> ("y", !!"B1") @=> UU) in
  let rr1 = assume "R1" corrab1 in
  let iduua, _ = synth (id UU !!"A0" !!"A1") in
  let aa2 = assume "A2" iduua in
  let iduub, _ = synth (id UU !!"B0" !!"B1") in
  let bb2 = assume "B2" iduub in

  let iduur, _ =
    synth
      (refl ("X" @-> "Y" @-> ("x", !!"X") @=> ("y", !!"Y") @=> UU <:> ("", UU) @=> ("", UU) @=> UU)
      $ !!"A0"
      $ !!"A1"
      $ !!"A2"
      $ !!"B0"
      $ !!"B1"
      $ !!"B2"
      $ !!"R0"
      $ !!"R1") in

  let r2 = assume "R2" iduur in

  let r_gelr2 =
    refl !~"Gel" $ !!"A0" $ !!"A1" $ !!"A2" $ !!"B0" $ !!"B1" $ !!"B2" $ !!"R0" $ !!"R1" $ !!"R2"
  in

  let gelr2, gelr2ty = synth r_gelr2 in

  let gelr2ty', _ =
    synth
      (refl (refl UU)
      $ !!"A0"
      $ !!"A1"
      $ !!"A2"
      $ !!"B0"
      $ !!"B1"
      $ !!"B2"
      $ (!~"Gel" $ !!"A0" $ !!"B0" $ !!"R0")
      $ (!~"Gel" $ !!"A1" $ !!"B1" $ !!"R1")) in

  let () = equal gelr2ty gelr2ty' in

  (* We can apply it to some points *)
  let a0 = assume "a0" aa0 in
  let a1 = assume "a1" aa1 in
  let a2 = assume "a2" (fst (synth (!!"A2" $ !!"a0" $ !!"a1"))) in
  let b0 = assume "b0" bb0 in
  let b1 = assume "b1" bb1 in
  let b2 = assume "b2" (fst (synth (!!"B2" $ !!"b0" $ !!"b1"))) in
  let r0 = assume "r0" (fst (synth (!!"R0" $ !!"a0" $ !!"b0"))) in
  let r1 = assume "r1" (fst (synth (!!"R1" $ !!"a1" $ !!"b1"))) in

  let r2ty, _ =
    synth (r_gelr2 $ !!"a0" $ !!"a1" $ !!"a2" $ !!"b0" $ !!"b1" $ !!"b2" $ rgel !!"r0" $ rgel !!"r1")
  in

  let r2 = assume "r2" r2ty in

  (* Since this is a square in UU, we can symmetrize it. *)
  let r_sym_gelr2 =
    sym
      (refl !~"Gel" $ !!"A0" $ !!"A1" $ !!"A2" $ !!"B0" $ !!"B1" $ !!"B2" $ !!"R0" $ !!"R1" $ !!"R2")
  in

  let sym_gelr2, sym_gelr2ty = synth r_sym_gelr2 in

  (* This doesn't compute to anything: the symmetry is "stuck" as an insertion outside the Gel.  In particular, it is a different type, which can be applied to the same points in transposed order. *)
  let () = unequal gelr2ty sym_gelr2ty in

  let sym_r2ty, _ =
    synth
      (r_sym_gelr2 $ !!"a0" $ !!"b0" $ rgel !!"r0" $ !!"a1" $ !!"b1" $ rgel !!"r1" $ !!"a2" $ !!"b2")
  in

  let () = unequal r2ty sym_r2ty in
  let r2' = assume "r2'" sym_r2ty in

  (* However, it is *isomorphic* to the original double span, by symmetry again. *)
  let _ = check (sym !!"r2") sym_r2ty in
  let _ = check (sym !!"r2'") r2ty in
  let symsym_r2, _ = synth (sym (sym !!"r2")) in
  let () = equal symsym_r2 r2 in
  let symsym_r2', _ = synth (sym (sym !!"r2'")) in
  let () = equal symsym_r2' r2' in
  ()
