open Pmp

let () = Narya.Gel.install ()

(* First we define and typecheck the basic operations Gel, gel (as a struct), and ungel (as a field). *)

let ggel, ggelty = synth !~"Gel"

let ggelty', _ =
  synth
    (("X", UU) @=> ("Y", UU) @=> ("R", ("x", !!"X") @=> ("y", !!"Y") @=> UU) @=> id UU !!"X" !!"Y")

let () = equal ggelty ggelty'

let gelty, _ =
  synth
    (("X", UU)
    @=> ("Y", UU)
    @=> ("R", ("x", !!"X") @=> ("y", !!"Y") @=> UU)
    @=> ("x", !!"X")
    @=> ("y", !!"Y")
    @=> ("r", !!"R" $ !!"x" $ !!"y")
    @=> (!~"Gel" $ !!"X" $ !!"Y" $ !!"R" $ !!"x" $ !!"y"))

let rgel x = struc [ ("ungel", x) ]
let gel = check ("X" @-> "Y" @-> "R" @-> "x" @-> "y" @-> "r" @-> rgel !!"r")

let ungelty, _ =
  synth
    (("X", UU)
    @=> ("Y", UU)
    @=> ("R", ("x", !!"X") @=> ("y", !!"Y") @=> UU)
    @=> ("x", !!"X")
    @=> ("y", !!"Y")
    @=> ("r", !~"Gel" $ !!"X" $ !!"Y" $ !!"R" $ !!"x" $ !!"y")
    @=> (!!"R" $ !!"x" $ !!"y"))

let ungel = check ("X" @-> "Y" @-> "R" @-> "x" @-> "y" @-> "r" @-> (!!"r" $. "ungel")) ungelty

(* Now we set up some assumptions *)

let uu, _ = synth UU
let aa = assume "A" uu
let bb = assume "B" uu
let corrab, _ = synth (("x", !!"A") @=> ("y", !!"B") @=> UU)
let rr = assume "R" corrab
let a = assume "a" aa
let b = assume "b" bb
let _, corrab' = synth !!"R"
let () = equal corrab corrab'
let rab, _ = synth (!!"R" $ !!"a" $ !!"b")

(* We test ungel(gel), which is a beta-reduction step. *)

let r = assume "r" rab
let r', _ = synth (rgel !!"r" <:> (!~"Gel" $ !!"A" $ !!"B" $ !!"R" $ !!"a" $ !!"b") $. "ungel")
let () = equal r r'

(* and gel(ungel), which is an eta-conversion step *)

let rgelab = !~"Gel" $ !!"A" $ !!"B" $ !!"R" $ !!"a" $ !!"b"
let gelab, _ = synth rgelab
let s = assume "s" gelab
let s' = check (rgel (!!"s" $. "ungel")) gelab
let () = equal_at s s' gelab

(* We can't compare gel untypedly since it is a struct, which doesn't synthesize. *)
let () =
  match equal s s' with
  | exception _ -> ()
  | _ -> raise (Failure "Expected exception")

(* refl of Gel builds a square of correspondences *)
let uu, _ = synth UU
let aa0 = assume "A0" uu
let bb0 = assume "B0" uu
let corrab0, _ = synth (("x", !!"A0") @=> ("y", !!"B0") @=> UU)
let rr0 = assume "R0" corrab0
let aa1 = assume "A1" uu
let bb1 = assume "B1" uu
let corrab1, _ = synth (("x", !!"A1") @=> ("y", !!"B1") @=> UU)
let rr1 = assume "R1" corrab1
let iduua, _ = synth (id UU !!"A0" !!"A1")
let aa2 = assume "A2" iduua
let iduub, _ = synth (id UU !!"B0" !!"B1")
let bb2 = assume "B2" iduub

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
    $ !!"R1")

let r2 = assume "R2" iduur

let r_gelr2 =
  refl !~"Gel" $ !!"A0" $ !!"A1" $ !!"A2" $ !!"B0" $ !!"B1" $ !!"B2" $ !!"R0" $ !!"R1" $ !!"R2"

let gelr2, gelr2ty = synth r_gelr2

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
    $ (!~"Gel" $ !!"A1" $ !!"B1" $ !!"R1"))

let () = equal gelr2ty gelr2ty'

(* We can apply it to some points *)

let a0 = assume "a0" aa0
let a1 = assume "a1" aa1
let a2 = assume "a2" (fst (synth (!!"A2" $ !!"a0" $ !!"a1")))
let b0 = assume "b0" bb0
let b1 = assume "b1" bb1
let b2 = assume "b2" (fst (synth (!!"B2" $ !!"b0" $ !!"b1")))
let r0 = assume "r0" (fst (synth (!!"R0" $ !!"a0" $ !!"b0")))
let r1 = assume "r1" (fst (synth (!!"R1" $ !!"a1" $ !!"b1")))

let r2ty, _ =
  synth (r_gelr2 $ !!"a0" $ !!"a1" $ !!"a2" $ !!"b0" $ !!"b1" $ !!"b2" $ rgel !!"r0" $ rgel !!"r1")

let r2 = assume "r2" r2ty

(* Since this is a square in UU, we can symmetrize it. *)

let r_sym_gelr2 =
  sym (refl !~"Gel" $ !!"A0" $ !!"A1" $ !!"A2" $ !!"B0" $ !!"B1" $ !!"B2" $ !!"R0" $ !!"R1" $ !!"R2")

let sym_gelr2, sym_gelr2ty = synth r_sym_gelr2

(* This doesn't compute to anything: the symmetry is "stuck" as an insertion outside the Gel.  In particular, it is a different type, which can be applied to the same points in transposed order. *)

let () = unequal gelr2ty sym_gelr2ty

let sym_r2ty, _ =
  synth
    (r_sym_gelr2 $ !!"a0" $ !!"b0" $ rgel !!"r0" $ !!"a1" $ !!"b1" $ rgel !!"r1" $ !!"a2" $ !!"b2")

let () = unequal r2ty sym_r2ty
let r2' = assume "r2'" sym_r2ty

(* However, it is *isomorphic* to the original double span, by symmetry again. *)

let _ = check (sym !!"r2") sym_r2ty
let _ = check (sym !!"r2'") r2ty
let symsym_r2, _ = synth (sym (sym !!"r2"))
let () = equal symsym_r2 r2
let symsym_r2', _ = synth (sym (sym !!"r2'"))
let () = equal symsym_r2' r2'
