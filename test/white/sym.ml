open Testutil.Pmp

let () =
  run @@ fun () ->
  let uu, _ = synth UU in
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

  (* We can't apply symmetry to 0- or 1-dimensional things *)
  let () = unsynth (sym !!"x00") in
  let () = unsynth (sym !!"x02") in

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
      $ !!"x21") in

  let x22 = assume "x22" xx22 in

  (* We can apply symmetry to a square, and the result has a different type in general. *)
  let sx22, sxx22 = synth (sym !!"x22") in
  let () = unequal xx22 sxx22 in

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
      $ !!"x12") in

  let () = equal sxx22 sxx22' in

  (* Symmetry is an involution *)
  let ssx22, ssxx22 = synth (sym (sym !!"x22")) in
  let () = equal ssxx22 xx22 in
  let () = equal ssx22 x22 in

  (* The action of functions on squares preserves symmetry *)
  let yy = assume "Y" uu in
  let xtoy, _ = synth (("x", !!"X") @=> !!"Y") in
  let f = assume "f" xtoy in

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
      $ !!"x22") in

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
         $ !!"x22")) in

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
      $ sym !!"x22") in

  let () = equal sfx22ty fsx22ty in
  let () = equal sfx22 fsx22 in
  ()
