open Testutil.Pmp

(* Uniqueness of iteration for Church encoded Nat from parametricity (from Thorsten) *)

let () =
  run @@ fun () ->
  Types.Gel.install ();
  let rgel x = struc [ ("ungel", x) ] in

  (* First we postulate an equality type, with congruence, transitivity, and reversal *)
  let eqty, _ = synth (("X", UU) @=> ("x", !!"X") @=> ("y", !!"X") @=> UU) in
  let eq = assume "eq" eqty in
  let eqrty, _ = synth (("X", UU) @=> ("x", !!"X") @=> (!!"eq" $ !!"X" $ !!"x" $ !!"x")) in
  let eqr = assume "eqr" eqrty in

  let congty, _ =
    synth
      (("X", UU)
      @=> ("Y", UU)
      @=> ("f", ("", !!"X") @=> !!"Y")
      @=> ("x", !!"X")
      @=> ("y", !!"X")
      @=> ("e", !!"eq" $ !!"X" $ !!"x" $ !!"y")
      @=> (!!"eq" $ !!"Y" $ (!!"f" $ !!"x") $ (!!"f" $ !!"y"))) in

  let cong = assume "cong" congty in

  let transty, _ =
    synth
      (("X", UU)
      @=> ("x", !!"X")
      @=> ("y", !!"X")
      @=> ("z", !!"X")
      @=> ("p", !!"eq" $ !!"X" $ !!"x" $ !!"y")
      @=> ("q", !!"eq" $ !!"X" $ !!"y" $ !!"z")
      @=> (!!"eq" $ !!"X" $ !!"x" $ !!"z")) in

  let trans = assume "trans" transty in

  let revty, _ =
    synth
      (("X", UU)
      @=> ("x", !!"X")
      @=> ("y", !!"X")
      @=> ("p", !!"eq" $ !!"X" $ !!"x" $ !!"y")
      @=> (!!"eq" $ !!"X" $ !!"y" $ !!"x")) in

  let rev = assume "rev" revty in

  (* Now we define the Church-encoded natural numbers.

     - Nat   := (A:U)→A→(A→A)→A
       zero  := λA z s.z
       suc n := λA z s.(s n)
       ite_A n := n A z_A s_A
  *)
  let rnat = ("A", UU) @=> ("", !!"A") @=> ("", ("", !!"A") @=> !!"A") @=> !!"A" in
  let nat, _ = synth rnat in
  let rzero = "A" @-> "z" @-> "s" @-> !!"z" in
  let zero = check rzero nat in
  let rnat_to_nat = ("", rnat) @=> rnat in
  let nat_to_nat, _ = synth rnat_to_nat in
  let rsuc = "n" @-> "A" @-> "z" @-> "s" @-> (!!"s" $ (!!"n" $ !!"A" $ !!"z" $ !!"s")) in
  let suc = check rsuc nat_to_nat in

  (* We postulate funext for such natural numbers.  (Doing it explicitly, for nat only, avoids the need to introduce dependent equality types to express general funext for dependent function-types.) *)
  let natfunext_ty, _ =
    synth
      (("m", rnat)
      @=> ("n", rnat)
      @=> ( "",
            ("A", UU)
            @=> ("zA", !!"A")
            @=> ("sA", ("", !!"A") @=> !!"A")
            @=> (!!"eq"
                $ !!"A"
                $ (!!"m" $ !!"A" $ !!"zA" $ !!"sA")
                $ (!!"n" $ !!"A" $ !!"zA" $ !!"sA")) )
      @=> (!!"eq" $ rnat $ !!"m" $ !!"n")) in

  let natfunext = assume "natfunext" natfunext_ty in

  (*
  - by parametricity, we can prove that the following triangle
    commutes if f is a Nat-homomorphism:

        ite_A
    N --------> A
      \         /
       \ite_B  / f          f (ite_A n) = ite_B n
        \     /
         v   v
           B
*)
  let ritenat_ty =
    ("A", UU)
    @=> ("zA", !!"A")
    @=> ("sA", ("", !!"A") @=> !!"A")
    @=> ("B", UU)
    @=> ("zB", !!"B")
    @=> ("sB", ("", !!"B") @=> !!"B")
    @=> ("f", ("", !!"A") @=> !!"B")
    @=> ("zf", !!"eq" $ !!"B" $ (!!"f" $ !!"zA") $ !!"zB")
    @=> ( "sf",
          ("a", !!"A") @=> (!!"eq" $ !!"B" $ (!!"f" $ (!!"sA" $ !!"a")) $ (!!"sB" $ (!!"f" $ !!"a")))
        )
    @=> ("n", rnat)
    @=> (!!"eq"
        $ !!"B"
        $ (!!"f" $ (!!"n" $ !!"A" $ !!"zA" $ !!"sA"))
        $ (!!"n" $ !!"B" $ !!"zB" $ !!"sB")) in

  let itenat_ty, _ = synth ritenat_ty in

  (*
   we just use (binary) parametricity for n:

   nᴾ A B (λa b.f a = b) z_A z_B (f z_A = z_B) s_A s_B (λa b (f a = b) . f (s_A a) = s_B (f a) = s_B b)
      : f (n A z_A s_A) = n B z_B s_B
*)
  let ritenat =
    "A"
    @-> "zA"
    @-> "sA"
    @-> "B"
    @-> "zB"
    @-> "sB"
    @-> "f"
    @-> "zf"
    @-> "sf"
    @-> "n"
    @-> (refl !!"n"
        $ !!"A"
        $ !!"B"
        $ (!~"Gel" $ !!"A" $ !!"B" $ "a" @-> "b" @-> (!!"eq" $ !!"B" $ (!!"f" $ !!"a") $ !!"b"))
        $ !!"zA"
        $ !!"zB"
        $ rgel !!"zf"
        $ !!"sA"
        $ !!"sB"
        $ "a"
          @-> "b"
          @-> "r"
          @-> rgel
                (!!"trans"
                $ !!"B"
                $ (!!"f" $ (!!"sA" $ !!"a"))
                $ (!!"sB" $ (!!"f" $ !!"a"))
                $ (!!"sB" $ !!"b")
                $ (!!"sf" $ !!"a")
                $ (!!"cong" $ !!"B" $ !!"B" $ !!"sB" $ (!!"f" $ !!"a") $ !!"b" $ (!!"r" $. "ungel"))
                )
        $. "ungel") in

  let itenat = check ritenat itenat_ty in

  (*
  - now we apply this to

      ite_X (ite_Nat n) = ite_X n

    i.e.

      n Nat zero suc X z_X s_X = n X z_X s_X

    by η/funext we get

      ite_N n = n Nat zero suc = n
*)
  let ritenn_ty = ("n", rnat) @=> (!!"eq" $ rnat $ (!!"n" $ rnat $ rzero $ rsuc) $ !!"n") in
  let itenn_ty, _ = synth ritenn_ty in

  let ritenn =
    "n"
    @-> (!!"natfunext"
        $ (!!"n" $ rnat $ rzero $ rsuc)
        $ !!"n"
        $ "X"
          @-> "zX"
          @-> "sX"
          @-> (ritenat
              <:> ritenat_ty
              $ rnat
              $ rzero
              $ rsuc
              $ !!"X"
              $ !!"zX"
              $ !!"sX"
              $ "m" @-> (!!"m" $ !!"X" $ !!"zX" $ !!"sX")
              $ (!!"eqr" $ !!"X" $ !!"zX")
              $ "m" @-> (!!"eqr" $ !!"X" $ (!!"sX" $ (!!"m" $ !!"X" $ !!"zX" $ !!"sX")))
              $ !!"n")) in

  let itenn = check ritenn itenn_ty in

  (*
  - so now we can apply this to any f : N → A homomorphism and obtain

    f n = f (ite_N n) = ite_A n
*)
  let uniq_ty, _ =
    synth
      (("A", UU)
      @=> ("zA", !!"A")
      @=> ("sA", ("", !!"A") @=> !!"A")
      @=> ("f", ("", rnat) @=> !!"A")
      @=> ("zf", !!"eq" $ !!"A" $ (!!"f" $ rzero) $ !!"zA")
      @=> ( "sf",
            ("n", rnat)
            @=> (!!"eq"
                $ !!"A"
                $ (!!"f" $ (rsuc <:> rnat_to_nat $ !!"n"))
                $ (!!"sA" $ (!!"f" $ !!"n"))) )
      @=> ("n", rnat)
      @=> (!!"eq" $ !!"A" $ (!!"f" $ !!"n") $ (!!"n" $ !!"A" $ !!"zA" $ !!"sA"))) in

  let uniq =
    check
      ("A"
      @-> "zA"
      @-> "sA"
      @-> "f"
      @-> "zf"
      @-> "sf"
      @-> "n"
      @-> (!!"trans"
          $ !!"A"
          $ (!!"f" $ !!"n")
          $ (!!"f" $ (!!"n" $ rnat $ rzero $ rsuc))
          $ (!!"n" $ !!"A" $ !!"zA" $ !!"sA")
          $ (!!"cong"
            $ rnat
            $ !!"A"
            $ !!"f"
            $ !!"n"
            $ (!!"n" $ rnat $ rzero $ rsuc)
            $ (!!"rev"
              $ rnat
              $ (!!"n" $ rnat $ rzero $ rsuc)
              $ !!"n"
              $ (ritenn <:> ritenn_ty $ !!"n")))
          $ (ritenat
            <:> ritenat_ty
            $ rnat
            $ rzero
            $ rsuc
            $ !!"A"
            $ !!"zA"
            $ !!"sA"
            $ !!"f"
            $ !!"zf"
            $ !!"sf"
            $ !!"n")))
      uniq_ty in
  ()
