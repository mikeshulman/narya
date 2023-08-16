open Pmp

let uu, _ = synth UU
let xx = assume "X" uu
let x0 = assume "x0" xx
let x1 = assume "x1" xx
let idx01, _ = synth (id !!"X" !!"x0" !!"x1")
let x2 = assume "x2" idx01
let xtox, _ = synth (pi "x" !!"X" !!"X")

(* The identity function acts as the identity *)
let idmap = check ("x" @-> !!"x") xtox
let () = equal (idmap $$ x0) x0
let () = unequal (idmap $$ x0) x1
let idmapx0, _ = synth ("x" @-> !!"x" <:> pi "x" !!"X" !!"X" $ !!"x0")
let () = equal idmapx0 x0
let () = unsynth ("x" @-> !!"x" <:> pi "x" !!"X" !!"X" $ !!"x2")

(* refl of the identity function acts as the identity on identifications *)
let refl_idmap_x2, _ = synth (refl ("x" @-> !!"x" <:> pi "x" !!"X" !!"X") $ !!"x0" $ !!"x1" $ !!"x2")
let () = unsynth (refl ("x" @-> !!"x" <:> pi "x" !!"X" !!"X") $ !!"x0" $ !!"x0" $ !!"x2")
let () = unsynth (refl ("x" @-> !!"x" <:> pi "x" !!"X" !!"X") $ !!"x0" $ !!"x1" $ !!"x0")
let () = equal refl_idmap_x2 x2

(*  *)
let yy = assume "Y" uu
let zz = assume "Z" uu
let xtoy, _ = synth (pi "x" !!"X" !!"Y")
let ytoz, _ = synth (pi "y" !!"Y" !!"Z")
let xtoz, _ = synth (pi "x" !!"X" !!"Z")
let f = assume "f" xtoy
let g = assume "g" ytoz
let gof = check ("x" @-> (!!"g" $ (!!"f" $ !!"x"))) xtoz
let () = uncheck ("x" @-> (!!"f" $ (!!"g" $ !!"x"))) xtoz

(* Identity types of pi-types don't *compute* to the expected thing, but they are isomorphic *)
let reflf, idff' = synth (refl !!"f")

let idff, _ =
  synth
    (pi "x" !!"X"
       (pi "x'" !!"X"
          (pi "x''" (id !!"X" !!"x" !!"x'") (id !!"Y" (!!"f" $ !!"x") (!!"f" $ !!"x'")))))

let () = unequal idff' idff
let h = assume "h" idff'
let h' = check ("x" @-> "x'" @-> "x''" @-> (!!"h" $ !!"x" $ !!"x'" $ !!"x''")) idff
let k = assume "k" idff
let k' = check ("x" @-> "x'" @-> "x''" @-> (!!"k" $ !!"x" $ !!"x'" $ !!"x''")) idff'

(* Ap is functorial *)
let reflg, _ = synth (refl !!"g")
let reflf_x2, _ = synth (refl !!"f" $ !!"x0" $ !!"x1" $ !!"x2")
let () = unsynth (refl !!"g" $ !!"x0" $ !!"x1" $ !!"x2")

let reflg_reflf_x2, _ =
  synth (refl !!"g" $ (!!"f" $ !!"x0") $ (!!"f" $ !!"x1") $ (refl !!"f" $ !!"x0" $ !!"x1" $ !!"x2"))

let refl_gof_x2, _ =
  synth (refl ("x" @-> (!!"g" $ (!!"f" $ !!"x")) <:> pi "x" !!"X" !!"Z") $ !!"x0" $ !!"x1" $ !!"x2")

let () = equal reflg_reflf_x2 refl_gof_x2
