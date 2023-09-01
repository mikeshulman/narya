open Testutil.Pmp

let uu, _ = synth UU
let xx = assume "X" uu
let x0 = assume "x0" xx
let x1 = assume "x1" xx

(* Identity types are equivalently instantiations of refl of a type *)
let idx01, _ = synth (id !!"X" !!"x0" !!"x1")
let idx01', _ = synth (refl !!"X" $ !!"x0" $ !!"x1")
let () = equal idx01 idx01'
let x2 = assume "x2" idx01
let xtox, _ = synth (("x", !!"X") @=> !!"X")

(* The identity function acts as the identity *)
let idmap = check ("x" @-> !!"x") xtox
let () = equal (idmap $$ x0) x0
let () = unequal (idmap $$ x0) x1
let idmapx0, _ = synth ("x" @-> !!"x" <:> ("x", !!"X") @=> !!"X" $ !!"x0")
let () = equal idmapx0 x0
let () = unsynth ("x" @-> !!"x" <:> ("x", !!"X") @=> !!"X" $ !!"x2")

(* refl of the identity function acts as the identity on identifications *)
let refl_idmap_x2, _ =
  synth (refl ("x" @-> !!"x" <:> ("x", !!"X") @=> !!"X") $ !!"x0" $ !!"x1" $ !!"x2")

let () = unsynth (refl ("x" @-> !!"x" <:> ("x", !!"X") @=> !!"X") $ !!"x0" $ !!"x0" $ !!"x2")
let () = unsynth (refl ("x" @-> !!"x" <:> ("x", !!"X") @=> !!"X") $ !!"x0" $ !!"x1" $ !!"x0")
let () = equal refl_idmap_x2 x2

(*  *)
let yy = assume "Y" uu
let zz = assume "Z" uu
let xtoy, _ = synth (("x", !!"X") @=> !!"Y")
let ytoz, _ = synth (("y", !!"Y") @=> !!"Z")
let xtoz, _ = synth (("x", !!"X") @=> !!"Z")
let f = assume "f" xtoy
let g = assume "g" ytoz
let gof = check ("x" @-> (!!"g" $ (!!"f" $ !!"x"))) xtoz
let () = uncheck ("x" @-> (!!"f" $ (!!"g" $ !!"x"))) xtoz

(* Identity types of pi-types don't *compute* to the expected thing, but they are isomorphic *)
let f' = assume "f'" xtoy
let idff, _ = synth (id (("x", !!"X") @=> !!"Y") !!"f" !!"f'")

let idff', _ =
  synth
    (("x", !!"X")
    @=> ("x'", !!"X")
    @=> ("x''", id !!"X" !!"x" !!"x'")
    @=> id !!"Y" (!!"f" $ !!"x") (!!"f'" $ !!"x'"))

let () = unequal idff idff'

let idff_to_idff'_ty, _ =
  synth
    (("", id (("x", !!"X") @=> !!"Y") !!"f" !!"f'")
    @=> ("x", !!"X")
    @=> ("x'", !!"X")
    @=> ("x''", id !!"X" !!"x" !!"x'")
    @=> id !!"Y" (!!"f" $ !!"x") (!!"f'" $ !!"x'"))

let idff_to_idff' =
  check ("h" @-> "x" @-> "x'" @-> "x''" @-> (!!"h" $ !!"x" $ !!"x'" $ !!"x''")) idff_to_idff'_ty

let idff'_to_idff_ty, _ =
  synth
    (( "",
       ("x", !!"X")
       @=> ("x'", !!"X")
       @=> ("x''", id !!"X" !!"x" !!"x'")
       @=> id !!"Y" (!!"f" $ !!"x") (!!"f'" $ !!"x'") )
    @=> id (("x", !!"X") @=> !!"Y") !!"f" !!"f'")

let idff'_to_idff =
  check ("k" @-> "x" @-> "x'" @-> "x''" @-> (!!"k" $ !!"x" $ !!"x'" $ !!"x''")) idff'_to_idff_ty

let p = assume "p" idff
let q = assume "q" idff'

let idff_roundtrip, _ =
  synth
    ("k" @-> "x" @-> "x'" @-> "x''" @-> (!!"k" $ !!"x" $ !!"x'" $ !!"x''")
    <:> ( "",
          ("x", !!"X")
          @=> ("x'", !!"X")
          @=> ("x''", id !!"X" !!"x" !!"x'")
          @=> id !!"Y" (!!"f" $ !!"x") (!!"f'" $ !!"x'") )
        @=> id (("x", !!"X") @=> !!"Y") !!"f" !!"f'"
    $ ("h" @-> "x" @-> "x'" @-> "x''" @-> (!!"h" $ !!"x" $ !!"x'" $ !!"x''")
      <:> ("", id (("x", !!"X") @=> !!"Y") !!"f" !!"f'")
          @=> ("x", !!"X")
          @=> ("x'", !!"X")
          @=> ("x''", id !!"X" !!"x" !!"x'")
          @=> id !!"Y" (!!"f" $ !!"x") (!!"f'" $ !!"x'")
      $ !!"p"))

let () = equal_at idff_roundtrip p idff

let idff'_roundtrip, _ =
  synth
    ("h" @-> "x" @-> "x'" @-> "x''" @-> (!!"h" $ !!"x" $ !!"x'" $ !!"x''")
    <:> ("", id (("x", !!"X") @=> !!"Y") !!"f" !!"f'")
        @=> ("x", !!"X")
        @=> ("x'", !!"X")
        @=> ("x''", id !!"X" !!"x" !!"x'")
        @=> id !!"Y" (!!"f" $ !!"x") (!!"f'" $ !!"x'")
    $ ("k" @-> "x" @-> "x'" @-> "x''" @-> (!!"k" $ !!"x" $ !!"x'" $ !!"x''")
      <:> ( "",
            ("x", !!"X")
            @=> ("x'", !!"X")
            @=> ("x''", id !!"X" !!"x" !!"x'")
            @=> id !!"Y" (!!"f" $ !!"x") (!!"f'" $ !!"x'") )
          @=> id (("x", !!"X") @=> !!"Y") !!"f" !!"f'"
      $ !!"q"))

let () = equal_at idff'_roundtrip q idff'

(* Identity types are invariant under eta-expansion *)
let idff_eta, _ = synth (id (("x", !!"X") @=> !!"Y") ("x" @-> (!!"f" $ !!"x")) !!"f'")
let () = equal idff idff_eta

(* Ap is functorial *)
let reflg, _ = synth (refl !!"g")
let reflf_x2, _ = synth (refl !!"f" $ !!"x0" $ !!"x1" $ !!"x2")
let () = unsynth (refl !!"g" $ !!"x0" $ !!"x1" $ !!"x2")

let reflg_reflf_x2, _ =
  synth (refl !!"g" $ (!!"f" $ !!"x0") $ (!!"f" $ !!"x1") $ (refl !!"f" $ !!"x0" $ !!"x1" $ !!"x2"))

let refl_gof_x2, _ =
  synth
    (refl ("x" @-> (!!"g" $ (!!"f" $ !!"x")) <:> ("x", !!"X") @=> !!"Z") $ !!"x0" $ !!"x1" $ !!"x2")

let () = equal reflg_reflf_x2 refl_gof_x2

(* The two degenerate squares associated to an identification have unequal types. *)
let r1x2, r1x2ty = synth (refl !!"x2")

let r2x2, r2x2ty =
  synth
    (refl ("x" @-> refl !!"x" <:> ("x", !!"X") @=> id !!"X" !!"x" !!"x") $ !!"x0" $ !!"x1" $ !!"x2")

let () = unequal r1x2ty r2x2ty

(* But applying symmetry identifies both their types and values. *)
let sr1x2, sr1x2ty = synth (sym (refl !!"x2"))
let () = equal sr1x2ty r2x2ty
let () = equal sr1x2 r2x2

(* But the two degenerate squares associated to a reflexivity *are* equal. *)
let r1reflx0, r1reflx0ty = synth (refl (refl !!"x0"))

let r2reflx0, r2reflx0ty =
  synth
    (refl ("x" @-> refl !!"x" <:> ("x", !!"X") @=> id !!"X" !!"x" !!"x")
    $ !!"x0"
    $ !!"x0"
    $ refl !!"x0")

let () = equal r1reflx0ty r2reflx0ty
let () = equal r1reflx0 r2reflx0

(* Doubly-degenerate squares are also fixed by symmetry *)
let sr1reflx0, _ = synth (sym (refl (refl !!"x0")))
let () = equal r1reflx0 sr1reflx0
