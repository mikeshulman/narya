open Testutil.Pmp

let () =
  run @@ fun () ->
  let uu, _ = synth UU in
  let xx = assume "X" uu (* Bottom face *) in

  let x000 = assume "x000" xx in
  let x001 = assume "x001" xx in
  let xx002, _ = synth (id !!"X" !!"x000" !!"x001") in
  let x002 = assume "x002" xx002 in
  let x010 = assume "x010" xx in
  let x011 = assume "x011" xx in
  let xx012, _ = synth (id !!"X" !!"x010" !!"x011") in
  let x012 = assume "x012" xx012 in
  let xx020, _ = synth (id !!"X" !!"x000" !!"x010") in
  let xx021, _ = synth (id !!"X" !!"x001" !!"x011") in
  let x020 = assume "x020" xx020 in
  let x021 = assume "x021" xx021 in

  let xx022, _ =
    synth
      (refl (refl !!"X")
      $ !!"x000"
      $ !!"x001"
      $ !!"x002"
      $ !!"x010"
      $ !!"x011"
      $ !!"x012"
      $ !!"x020"
      $ !!"x021") in

  let x022 = assume "x022" xx022 (* Top face *) in

  let x100 = assume "x100" xx in
  let x101 = assume "x101" xx in
  let xx102, _ = synth (id !!"X" !!"x100" !!"x101") in
  let x102 = assume "x102" xx102 in
  let x110 = assume "x110" xx in
  let x111 = assume "x111" xx in
  let xx112, _ = synth (id !!"X" !!"x110" !!"x111") in
  let x112 = assume "x112" xx112 in
  let xx120, _ = synth (id !!"X" !!"x100" !!"x110") in
  let xx121, _ = synth (id !!"X" !!"x101" !!"x111") in
  let x120 = assume "x120" xx120 in
  let x121 = assume "x121" xx121 in

  let xx122, _ =
    synth
      (refl (refl !!"X")
      $ !!"x100"
      $ !!"x101"
      $ !!"x102"
      $ !!"x110"
      $ !!"x111"
      $ !!"x112"
      $ !!"x120"
      $ !!"x121") in

  let x122 = assume "x122" xx122 (* Front face *) in

  let xx200, _ = synth (id !!"X" !!"x000" !!"x100") in
  let x200 = assume "x200" xx200 in
  let xx201, _ = synth (id !!"X" !!"x001" !!"x101") in
  let x201 = assume "x201" xx201 in

  let xx202, _ =
    synth
      (refl (refl !!"X")
      $ !!"x000"
      $ !!"x001"
      $ !!"x002"
      $ !!"x100"
      $ !!"x101"
      $ !!"x102"
      $ !!"x200"
      $ !!"x201") in

  let x202 = assume "x202" xx202 (* Back face *) in

  let xx210, _ = synth (id !!"X" !!"x010" !!"x110") in
  let x210 = assume "x210" xx210 in
  let xx211, _ = synth (id !!"X" !!"x011" !!"x111") in
  let x211 = assume "x211" xx211 in

  let xx212, _ =
    synth
      (refl (refl !!"X")
      $ !!"x010"
      $ !!"x011"
      $ !!"x012"
      $ !!"x110"
      $ !!"x111"
      $ !!"x112"
      $ !!"x210"
      $ !!"x211") in

  let x212 = assume "x212" xx212 (* Left face *) in

  let xx220, _ =
    synth
      (refl (refl !!"X")
      $ !!"x000"
      $ !!"x010"
      $ !!"x020"
      $ !!"x100"
      $ !!"x110"
      $ !!"x120"
      $ !!"x200"
      $ !!"x210") in

  let x220 = assume "x220" xx220 (* Right face *) in

  let xx221, _ =
    synth
      (refl (refl !!"X")
      $ !!"x001"
      $ !!"x011"
      $ !!"x021"
      $ !!"x101"
      $ !!"x111"
      $ !!"x121"
      $ !!"x201"
      $ !!"x211") in

  let x221 = assume "x221" xx221 (* Center *) in

  let xx222, _ =
    synth
      (refl (refl (refl !!"X"))
      $ !!"x000"
      $ !!"x001"
      $ !!"x002"
      $ !!"x010"
      $ !!"x011"
      $ !!"x012"
      $ !!"x020"
      $ !!"x021"
      $ !!"x022"
      $ !!"x100"
      $ !!"x101"
      $ !!"x102"
      $ !!"x110"
      $ !!"x111"
      $ !!"x112"
      $ !!"x120"
      $ !!"x121"
      $ !!"x122"
      $ !!"x200"
      $ !!"x201"
      $ !!"x202"
      $ !!"x210"
      $ !!"x211"
      $ !!"x212"
      $ !!"x220"
      $ !!"x221") in

  let x222 = assume "x222" xx222 (* The two transpositions that can act on a cube *) in

  let sym_x222, sym_xx222 = synth (sym !!"x222") in

  let apsym_x222, apsym_xx222 =
    synth
      (refl
         ("y00"
          @-> "y01"
          @-> "y02"
          @-> "y10"
          @-> "y11"
          @-> "y12"
          @-> "y20"
          @-> "y21"
          @-> "y22"
          @-> sym !!"y22"
         <:> ("y00", !!"X")
             @=> ("y01", !!"X")
             @=> ("y02", id !!"X" !!"y00" !!"y01")
             @=> ("y10", !!"X")
             @=> ("y11", !!"X")
             @=> ("y12", id !!"X" !!"y10" !!"y11")
             @=> ("y20", id !!"X" !!"y00" !!"y10")
             @=> ("y21", id !!"X" !!"y01" !!"y11")
             @=> ( "y22",
                   refl (refl !!"X")
                   $ !!"y00"
                   $ !!"y01"
                   $ !!"y02"
                   $ !!"y10"
                   $ !!"y11"
                   $ !!"y12"
                   $ !!"y20"
                   $ !!"y21" )
             @=> (refl (refl !!"X")
                 $ !!"y00"
                 $ !!"y10"
                 $ !!"y20"
                 $ !!"y01"
                 $ !!"y11"
                 $ !!"y21"
                 $ !!"y02"
                 $ !!"y12"))
      $ !!"x000"
      $ !!"x001"
      $ !!"x002"
      $ !!"x010"
      $ !!"x011"
      $ !!"x012"
      $ !!"x020"
      $ !!"x021"
      $ !!"x022"
      $ !!"x100"
      $ !!"x101"
      $ !!"x102"
      $ !!"x110"
      $ !!"x111"
      $ !!"x112"
      $ !!"x120"
      $ !!"x121"
      $ !!"x122"
      $ !!"x200"
      $ !!"x201"
      $ !!"x202"
      $ !!"x210"
      $ !!"x211"
      $ !!"x212"
      $ !!"x220"
      $ !!"x221"
      $ !!"x222")
    (* They have different types *) in

  let () = unequal sym_xx222 apsym_xx222 (* Here are their types. *) in

  let sym_xx222', _ =
    synth
      (refl (refl (refl !!"X"))
      $ !!"x000"
      $ !!"x010"
      $ !!"x020"
      $ !!"x001"
      $ !!"x011"
      $ !!"x021"
      $ !!"x002"
      $ !!"x012"
      $ sym !!"x022"
      $ !!"x100"
      $ !!"x110"
      $ !!"x120"
      $ !!"x101"
      $ !!"x111"
      $ !!"x121"
      $ !!"x102"
      $ !!"x112"
      $ sym !!"x122"
      $ !!"x200"
      $ !!"x210"
      $ !!"x220"
      $ !!"x201"
      $ !!"x211"
      $ !!"x221"
      $ !!"x202"
      $ !!"x212") in

  let () = equal sym_xx222 sym_xx222' in

  let apsym_xx222', _ =
    synth
      (refl (refl (refl !!"X"))
      $ !!"x000"
      $ !!"x001"
      $ !!"x002"
      $ !!"x100"
      $ !!"x101"
      $ !!"x102"
      $ !!"x200"
      $ !!"x201"
      $ !!"x202"
      $ !!"x010"
      $ !!"x011"
      $ !!"x012"
      $ !!"x110"
      $ !!"x111"
      $ !!"x112"
      $ !!"x210"
      $ !!"x211"
      $ !!"x212"
      $ !!"x020"
      $ !!"x021"
      $ !!"x022"
      $ !!"x120"
      $ !!"x121"
      $ !!"x122"
      $ sym !!"x220"
      $ sym !!"x221") in

  let () = equal apsym_xx222 apsym_xx222' (* They both have alternative degeneracy notations. *) in

  let sym_x222', sym_xx222' = synth (!!"x222" $^ "213") in
  let () = equal sym_xx222 sym_xx222' in
  let () = equal sym_x222 sym_x222' in
  let apsym_x222', apsym_xx222' = synth (!!"x222" $^ "132") in
  let () = equal apsym_xx222 apsym_xx222' in
  let () =
    equal apsym_x222 apsym_x222'
    (* But the two sides of the braid equation are equal.  We build them up in stages, checking their types as we go.  First the left-hand side sym-apsym-sym. *)
  in

  let apsym_sym_x222, apsym_sym_xx222 =
    synth
      (refl
         ("y00"
          @-> "y01"
          @-> "y02"
          @-> "y10"
          @-> "y11"
          @-> "y12"
          @-> "y20"
          @-> "y21"
          @-> "y22"
          @-> sym !!"y22"
         <:> ("y00", !!"X")
             @=> ("y01", !!"X")
             @=> ("y02", id !!"X" !!"y00" !!"y01")
             @=> ("y10", !!"X")
             @=> ("y11", !!"X")
             @=> ("y12", id !!"X" !!"y10" !!"y11")
             @=> ("y20", id !!"X" !!"y00" !!"y10")
             @=> ("y21", id !!"X" !!"y01" !!"y11")
             @=> ( "y22",
                   refl (refl !!"X")
                   $ !!"y00"
                   $ !!"y01"
                   $ !!"y02"
                   $ !!"y10"
                   $ !!"y11"
                   $ !!"y12"
                   $ !!"y20"
                   $ !!"y21" )
             @=> (refl (refl !!"X")
                 $ !!"y00"
                 $ !!"y10"
                 $ !!"y20"
                 $ !!"y01"
                 $ !!"y11"
                 $ !!"y21"
                 $ !!"y02"
                 $ !!"y12"))
      $ !!"x000"
      $ !!"x010"
      $ !!"x020"
      $ !!"x001"
      $ !!"x011"
      $ !!"x021"
      $ !!"x002"
      $ !!"x012"
      $ sym !!"x022"
      $ !!"x100"
      $ !!"x110"
      $ !!"x120"
      $ !!"x101"
      $ !!"x111"
      $ !!"x121"
      $ !!"x102"
      $ !!"x112"
      $ sym !!"x122"
      $ !!"x200"
      $ !!"x210"
      $ !!"x220"
      $ !!"x201"
      $ !!"x211"
      $ !!"x221"
      $ !!"x202"
      $ !!"x212"
      $ sym !!"x222") in

  let apsym_sym_xx222', _ =
    synth
      (refl (refl (refl !!"X"))
      $ !!"x000"
      $ !!"x010"
      $ !!"x020"
      $ !!"x100"
      $ !!"x110"
      $ !!"x120"
      $ !!"x200"
      $ !!"x210"
      $ !!"x220"
      $ !!"x001"
      $ !!"x011"
      $ !!"x021"
      $ !!"x101"
      $ !!"x111"
      $ !!"x121"
      $ !!"x201"
      $ !!"x211"
      $ !!"x221"
      $ !!"x002"
      $ !!"x012"
      $ sym !!"x022"
      $ !!"x102"
      $ !!"x112"
      $ sym !!"x122"
      $ sym !!"x202"
      $ sym !!"x212") in

  let () = equal apsym_sym_xx222 apsym_sym_xx222' in

  let sym_apsym_sym_x222, sym_apsym_sym_xx222 =
    synth
      (sym
         (refl
            ("y00"
             @-> "y01"
             @-> "y02"
             @-> "y10"
             @-> "y11"
             @-> "y12"
             @-> "y20"
             @-> "y21"
             @-> "y22"
             @-> sym !!"y22"
            <:> ("y00", !!"X")
                @=> ("y01", !!"X")
                @=> ("y02", id !!"X" !!"y00" !!"y01")
                @=> ("y10", !!"X")
                @=> ("y11", !!"X")
                @=> ("y12", id !!"X" !!"y10" !!"y11")
                @=> ("y20", id !!"X" !!"y00" !!"y10")
                @=> ("y21", id !!"X" !!"y01" !!"y11")
                @=> ( "y22",
                      refl (refl !!"X")
                      $ !!"y00"
                      $ !!"y01"
                      $ !!"y02"
                      $ !!"y10"
                      $ !!"y11"
                      $ !!"y12"
                      $ !!"y20"
                      $ !!"y21" )
                @=> (refl (refl !!"X")
                    $ !!"y00"
                    $ !!"y10"
                    $ !!"y20"
                    $ !!"y01"
                    $ !!"y11"
                    $ !!"y21"
                    $ !!"y02"
                    $ !!"y12"))
         $ !!"x000"
         $ !!"x010"
         $ !!"x020"
         $ !!"x001"
         $ !!"x011"
         $ !!"x021"
         $ !!"x002"
         $ !!"x012"
         $ sym !!"x022"
         $ !!"x100"
         $ !!"x110"
         $ !!"x120"
         $ !!"x101"
         $ !!"x111"
         $ !!"x121"
         $ !!"x102"
         $ !!"x112"
         $ sym !!"x122"
         $ !!"x200"
         $ !!"x210"
         $ !!"x220"
         $ !!"x201"
         $ !!"x211"
         $ !!"x221"
         $ !!"x202"
         $ !!"x212"
         $ sym !!"x222")) in

  let sym_apsym_sym_xx222', _ =
    synth
      (refl (refl (refl !!"X"))
      $ !!"x000"
      $ !!"x100"
      $ !!"x200"
      $ !!"x010"
      $ !!"x110"
      $ !!"x210"
      $ !!"x020"
      $ !!"x120"
      $ sym !!"x220"
      $ !!"x001"
      $ !!"x101"
      $ !!"x201"
      $ !!"x011"
      $ !!"x111"
      $ !!"x211"
      $ !!"x021"
      $ !!"x121"
      $ sym !!"x221"
      $ !!"x002"
      $ !!"x102"
      $ sym !!"x202"
      $ !!"x012"
      $ !!"x112"
      $ sym !!"x212"
      $ sym !!"x022"
      $ sym !!"x122") in

  let () =
    equal sym_apsym_sym_xx222 sym_apsym_sym_xx222'
    (* Now the right-hand side, apsym-sym-apsym *) in

  let sym_apsym_x222, sym_apsym_xx222 =
    synth
      (sym
         (refl
            ("y00"
             @-> "y01"
             @-> "y02"
             @-> "y10"
             @-> "y11"
             @-> "y12"
             @-> "y20"
             @-> "y21"
             @-> "y22"
             @-> sym !!"y22"
            <:> ("y00", !!"X")
                @=> ("y01", !!"X")
                @=> ("y02", id !!"X" !!"y00" !!"y01")
                @=> ("y10", !!"X")
                @=> ("y11", !!"X")
                @=> ("y12", id !!"X" !!"y10" !!"y11")
                @=> ("y20", id !!"X" !!"y00" !!"y10")
                @=> ("y21", id !!"X" !!"y01" !!"y11")
                @=> ( "y22",
                      refl (refl !!"X")
                      $ !!"y00"
                      $ !!"y01"
                      $ !!"y02"
                      $ !!"y10"
                      $ !!"y11"
                      $ !!"y12"
                      $ !!"y20"
                      $ !!"y21" )
                @=> (refl (refl !!"X")
                    $ !!"y00"
                    $ !!"y10"
                    $ !!"y20"
                    $ !!"y01"
                    $ !!"y11"
                    $ !!"y21"
                    $ !!"y02"
                    $ !!"y12"))
         $ !!"x000"
         $ !!"x001"
         $ !!"x002"
         $ !!"x010"
         $ !!"x011"
         $ !!"x012"
         $ !!"x020"
         $ !!"x021"
         $ !!"x022"
         $ !!"x100"
         $ !!"x101"
         $ !!"x102"
         $ !!"x110"
         $ !!"x111"
         $ !!"x112"
         $ !!"x120"
         $ !!"x121"
         $ !!"x122"
         $ !!"x200"
         $ !!"x201"
         $ !!"x202"
         $ !!"x210"
         $ !!"x211"
         $ !!"x212"
         $ !!"x220"
         $ !!"x221"
         $ !!"x222")) in

  let sym_apsym_xx222', _ =
    synth
      (refl (refl (refl !!"X"))
      $ !!"x000"
      $ !!"x100"
      $ !!"x200"
      $ !!"x001"
      $ !!"x101"
      $ !!"x201"
      $ !!"x002"
      $ !!"x102"
      $ sym !!"x202"
      $ !!"x010"
      $ !!"x110"
      $ !!"x210"
      $ !!"x011"
      $ !!"x111"
      $ !!"x211"
      $ !!"x012"
      $ !!"x112"
      $ sym !!"x212"
      $ !!"x020"
      $ !!"x120"
      $ sym !!"x220"
      $ !!"x021"
      $ !!"x121"
      $ sym !!"x221"
      $ !!"x022"
      $ !!"x122") in

  let () = equal sym_apsym_xx222 sym_apsym_xx222' in

  let apsym_sym_apsym_x222, apsym_sym_apsym_xx222 =
    synth
      (refl
         ("y00"
          @-> "y01"
          @-> "y02"
          @-> "y10"
          @-> "y11"
          @-> "y12"
          @-> "y20"
          @-> "y21"
          @-> "y22"
          @-> sym !!"y22"
         <:> ("y00", !!"X")
             @=> ("y01", !!"X")
             @=> ("y02", id !!"X" !!"y00" !!"y01")
             @=> ("y10", !!"X")
             @=> ("y11", !!"X")
             @=> ("y12", id !!"X" !!"y10" !!"y11")
             @=> ("y20", id !!"X" !!"y00" !!"y10")
             @=> ("y21", id !!"X" !!"y01" !!"y11")
             @=> ( "y22",
                   refl (refl !!"X")
                   $ !!"y00"
                   $ !!"y01"
                   $ !!"y02"
                   $ !!"y10"
                   $ !!"y11"
                   $ !!"y12"
                   $ !!"y20"
                   $ !!"y21" )
             @=> (refl (refl !!"X")
                 $ !!"y00"
                 $ !!"y10"
                 $ !!"y20"
                 $ !!"y01"
                 $ !!"y11"
                 $ !!"y21"
                 $ !!"y02"
                 $ !!"y12"))
      $ !!"x000"
      $ !!"x100"
      $ !!"x200"
      $ !!"x001"
      $ !!"x101"
      $ !!"x201"
      $ !!"x002"
      $ !!"x102"
      $ sym !!"x202"
      $ !!"x010"
      $ !!"x110"
      $ !!"x210"
      $ !!"x011"
      $ !!"x111"
      $ !!"x211"
      $ !!"x012"
      $ !!"x112"
      $ sym !!"x212"
      $ !!"x020"
      $ !!"x120"
      $ sym !!"x220"
      $ !!"x021"
      $ !!"x121"
      $ sym !!"x221"
      $ !!"x022"
      $ !!"x122"
      $ sym
          (refl
             ("y00"
              @-> "y01"
              @-> "y02"
              @-> "y10"
              @-> "y11"
              @-> "y12"
              @-> "y20"
              @-> "y21"
              @-> "y22"
              @-> sym !!"y22"
             <:> ("y00", !!"X")
                 @=> ("y01", !!"X")
                 @=> ("y02", id !!"X" !!"y00" !!"y01")
                 @=> ("y10", !!"X")
                 @=> ("y11", !!"X")
                 @=> ("y12", id !!"X" !!"y10" !!"y11")
                 @=> ("y20", id !!"X" !!"y00" !!"y10")
                 @=> ("y21", id !!"X" !!"y01" !!"y11")
                 @=> ( "y22",
                       refl (refl !!"X")
                       $ !!"y00"
                       $ !!"y01"
                       $ !!"y02"
                       $ !!"y10"
                       $ !!"y11"
                       $ !!"y12"
                       $ !!"y20"
                       $ !!"y21" )
                 @=> (refl (refl !!"X")
                     $ !!"y00"
                     $ !!"y10"
                     $ !!"y20"
                     $ !!"y01"
                     $ !!"y11"
                     $ !!"y21"
                     $ !!"y02"
                     $ !!"y12"))
          $ !!"x000"
          $ !!"x001"
          $ !!"x002"
          $ !!"x010"
          $ !!"x011"
          $ !!"x012"
          $ !!"x020"
          $ !!"x021"
          $ !!"x022"
          $ !!"x100"
          $ !!"x101"
          $ !!"x102"
          $ !!"x110"
          $ !!"x111"
          $ !!"x112"
          $ !!"x120"
          $ !!"x121"
          $ !!"x122"
          $ !!"x200"
          $ !!"x201"
          $ !!"x202"
          $ !!"x210"
          $ !!"x211"
          $ !!"x212"
          $ !!"x220"
          $ !!"x221"
          $ !!"x222")) in

  let apsym_sym_apsym_xx222', _ =
    synth
      (refl (refl (refl !!"X"))
      $ !!"x000"
      $ !!"x100"
      $ !!"x200"
      $ !!"x010"
      $ !!"x110"
      $ !!"x210"
      $ !!"x020"
      $ !!"x120"
      $ sym !!"x220"
      $ !!"x001"
      $ !!"x101"
      $ !!"x201"
      $ !!"x011"
      $ !!"x111"
      $ !!"x211"
      $ !!"x021"
      $ !!"x121"
      $ sym !!"x221"
      $ !!"x002"
      $ !!"x102"
      $ sym !!"x202"
      $ !!"x012"
      $ !!"x112"
      $ sym !!"x212"
      $ sym !!"x022"
      $ sym !!"x122") in

  let () =
    equal apsym_sym_apsym_xx222 apsym_sym_apsym_xx222'
    (* Now we check that both sides have the same types and are equal *) in

  let () = equal sym_apsym_sym_xx222 apsym_sym_apsym_xx222 in
  let () =
    equal sym_apsym_sym_x222 apsym_sym_apsym_x222
    (* And they have an alternative, much simpler, degeneracy notation *) in

  let braid', braidty' = synth (!!"x222" $^ "321") in
  let () = equal sym_apsym_sym_xx222 braidty' in
  let () = equal sym_apsym_sym_x222 braid' in
  ()
