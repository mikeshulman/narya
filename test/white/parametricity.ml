open Testutil.Pmp

let () =
  run @@ fun () ->
  Types.Gel.install ();
  let rgel x = struc [ ("ungel", x) ] in

  (* First we postulate an equality type *)
  let eqty, _ = synth (("X", UU) @=> ("x", !!"X") @=> ("y", !!"X") @=> UU) in
  let eq = assume "eq" eqty in
  let eqrty, _ = synth (("X", UU) @=> ("x", !!"X") @=> (!!"eq" $ !!"X" $ !!"x" $ !!"x")) in
  let eqr = assume "eqr" eqrty in

  (* Now we prove a first application of parametricity: anything in the type of the polymorphic identity function is pointwise equal to the identity.  (This doesn't actually require the computation laws for gel/ungel, and it only uses unary parametricity.) *)
  let idfuncty, _ = synth (("X", UU) @=> ("x", !!"X") @=> !!"X") in
  let f = assume "f" idfuncty in

  let fisid, _ =
    synth (("X", UU) @=> ("x", !!"X") @=> (!!"eq" $ !!"X" $ !!"x" $ (!!"f" $ !!"X" $ !!"x"))) in

  let fisid_pf =
    check
      ("X"
      @-> "x"
      @-> (refl !!"f"
          $ !!"X"
          $ !!"X"
          $ (!~"Gel" $ !!"X" $ !!"X" $ "a" @-> "b" @-> (!!"eq" $ !!"X" $ !!"x" $ !!"b"))
          $ !!"x"
          $ !!"x"
          $ rgel (!!"eqr" $ !!"X" $ !!"x")
          $. "ungel"))
      fisid in
  ()
