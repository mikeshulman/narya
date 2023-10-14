open Testutil.Pmp

let () =
  run @@ fun () ->
  Types.Sigma.install ();
  let uu, _ = synth UU in
  let aa = assume "A" uu in
  let atou, _ = synth (("", !!"A") @=> UU) in
  let bb = assume "B" atou in
  let rss = !~"Σ" $ !!"A" $ !!"B" in
  let ss, _ = synth rss in

  (* Pairs have the correct type *)
  let a = assume "a" aa in
  let bba, _ = synth (!!"B" $ !!"a") in
  let b = assume "b" bba in
  let rs = !~"pair" $ !!"A" $ !!"B" $ !!"a" $ !!"b" in
  let s, sty = synth rs in
  let () = equal sty ss in

  (* Structs also have the correct type *)
  let ( & ) x y = struc [ ("fst", x); ("snd", y) ] in
  let rt = !!"a" & !!"b" in
  let t = check rt ss in

  (* Projections have the correct type *)
  let x = assume "x" ss in
  let x1, x1ty = synth (!!"x" $. "fst") in
  let () = equal x1ty aa in
  let x2, x2ty = synth (!!"x" $. "snd") in
  let () = unequal x2ty bba in
  let x2ty', _ = synth (!!"B" $ (!!"x" $. "fst")) in
  let () = equal x2ty x2ty' in

  (* Projections of pairs compute *)
  let a', aa' = synth (rs $. "fst") in
  let () = equal aa' aa in
  let () = equal a a' in
  let b', bba' = synth (rs $. "snd") in
  let () = equal bba' bba in
  let () = equal b b' in

  (* Projections of structs also compute *)
  let a'', aa'' = synth (rt <:> rss $. "fst") in
  let () = equal aa'' aa in
  let () = equal a'' a in
  let b'', bba'' = synth (rt <:> rss $. "snd") in
  let () = equal bba'' bba in
  let () = equal b'' b in

  (* Projections satisfy eta-conversion for both pairs and structs *)
  let x' = check (!~"pair" $ !!"A" $ !!"B" $ (!!"x" $. "fst") $ (!!"x" $. "snd")) ss in
  let () = equal_at x x' ss in

  (* Need typed equality for eta! *)
  let () =
    match equal x x' with
    | _ -> raise (Failure "Unexpectedly equal terms")
    | exception _ -> () in

  let x'' = check (!!"x" $. "fst" & !!"x" $. "snd") ss in
  let () = equal_at x x'' ss in
  let () = equal_at x' x'' ss in

  (* Identifications can be paired to give an identification of pairs *)
  let a0 = assume "a0" aa in
  let bba0, _ = synth (!!"B" $ !!"a0") in
  let b0 = assume "b0" bba0 in
  let a1 = assume "a1" aa in
  let bba1, _ = synth (!!"B" $ !!"a1") in
  let b1 = assume "b1" bba1 in
  let ida0a1, _ = synth (id !!"A" !!"a0" !!"a1") in
  let a2 = assume "a2" ida0a1 in
  let idb0b1, _ = synth (refl !!"B" $ !!"a0" $ !!"a1" $ !!"a2" $ !!"b0" $ !!"b1") in
  let b2 = assume "b2" idb0b1 in

  (* As for function-types, identity types of sigma-types are invariant under eta-conversion *)
  let rs0 = !~"pair" $ !!"A" $ !!"B" $ !!"a0" $ !!"b0" in
  let rs0' = !!"a0" & !!"b0" in
  let s0 = check rs0 ss in
  let rs1 = !~"pair" $ !!"A" $ !!"B" $ !!"a1" $ !!"b1" in
  let s1 = check rs1 ss in
  let ids0s1, _ = synth (id rss rs0 rs1) in
  let ids0s1', _ = synth (id rss rs0' rs1) in
  let () = equal ids0s1 ids0s1' in

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
    $ !!"b2" in

  let rs2' = !!"a2" & !!"b2" in
  let s2, s2ty = synth rs2 in
  let () = equal s2ty ids0s1 in
  let s2 = check rs2 ids0s1 in

  (* And projected back out again to the inputs *)
  let a2', ida0a1' = synth (rs2 $. "fst") in
  let () = equal ida0a1 ida0a1' in
  let b2', idb0b1' = synth (rs2 $. "snd") in
  let () = equal idb0b1 idb0b1' in

  (* Refl commutes with pairing *)
  let refls, idabab = synth (refl (!~"pair" $ !!"A" $ !!"B" $ !!"a" $ !!"b")) in

  let refls', idabab' =
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
      $ refl !!"b") in

  let () = equal idabab idabab' in
  let () = equal_at refls refls' idabab in

  (* And with structs *)
  let reflt, idabab = synth (refl ((!!"a" & !!"b") <:> rss)) in
  let reflt' = check (refl !!"a" & refl !!"b") idabab in
  let () = equal_at reflt reflt' idabab in
  let () = equal_at reflt refls idabab in
  let () = equal_at reflt refls' idabab in
  let () = equal_at reflt' refls idabab in
  let () = equal_at reflt' refls' idabab in

  (* Sigmas can store identities and squares, and symmetry can act on them *)
  let xx = assume "X" uu in
  let x00 = assume "x00" xx in
  let x01 = assume "x01" xx in
  let xx02, _ = synth (id !!"X" !!"x00" !!"x01") in
  let x02 = assume "x02" xx02 in
  let x10 = assume "x10" xx in
  let x11 = assume "x11" xx in
  let xx12, _ = synth (id !!"X" !!"x10" !!"x11") in
  let x12 = assume "x12" xx12 in
  let xx20, _ = synth (id !!"X" !!"x00" !!"x10") in
  let xx21, _ = synth (id !!"X" !!"x01" !!"x11") in
  let x20 = assume "x20" xx20 in
  let x21 = assume "x21" xx21 in

  let rxx22 =
    refl (refl !!"X")
    $ !!"x00"
    $ !!"x01"
    $ !!"x02"
    $ !!"x10"
    $ !!"x11"
    $ !!"x12"
    $ !!"x20"
    $ !!"x21" in

  let xx22, _ = synth rxx22 in
  let x22 = assume "x22" xx22 in
  let yy = assume "Y" uu in
  let y = assume "y" yy in
  let xx22y, _ = synth (!~"Σ" $ rxx22 $ "" @-> !!"Y") in
  let s = assume "s" xx22y in
  let () = unsynth (sym !!"s") in

  (* Huh, where is the problem? *)
  let fsts, _ = synth (sym (!!"s" $. "fst")) in
  ()
