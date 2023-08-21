open Pmp

let () = Narya.Gel.install ()

(* First we postulate an equality type *)

let eqty, _ = synth (pi "X" UU (pi "x" !!"X" (pi "y" !!"X" UU)))
let eq = assume "eq" eqty
let eqrty, _ = synth (pi "X" UU (pi "x" !!"X" (!!"eq" $ !!"X" $ !!"x" $ !!"x")))
let eqr = assume "eqr" eqrty

(* Now we prove a first application of parametricity: anything in the type of the polymorphic identity function is pointwise equal to the identity.  (This doesn't actually require the computation laws for gel/ungel, and it only uses unary parametricity.) *)

let idfuncty, _ = synth (pi "X" UU (pi "x" !!"X" !!"X"))
let f = assume "f" idfuncty
let fisid, _ = synth (pi "X" UU (pi "x" !!"X" (!!"eq" $ !!"X" $ !!"x" $ (!!"f" $ !!"X" $ !!"x"))))

let fisid_pf =
  check
    ("X"
    @-> "x"
    @-> (!~"ungel"
        $ !!"X"
        $ !!"X"
        $ "a" @-> "b" @-> (!!"eq" $ !!"X" $ !!"x" $ !!"b")
        $ (!!"f" $ !!"X" $ !!"x")
        $ (!!"f" $ !!"X" $ !!"x")
        $ (refl !!"f"
          $ !!"X"
          $ !!"X"
          $ (!~"GEL" $ !!"X" $ !!"X" $ "a" @-> "b" @-> (!!"eq" $ !!"X" $ !!"x" $ !!"b"))
          $ !!"x"
          $ !!"x"
          $ (!~"gel"
            $ !!"X"
            $ !!"X"
            $ "a" @-> "b" @-> (!!"eq" $ !!"X" $ !!"x" $ !!"b")
            $ !!"x"
            $ !!"x"
            $ (!!"eqr" $ !!"X" $ !!"x")))))
    fisid
