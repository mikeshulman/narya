open Testutil.Mcp

let () =
  run @@ fun () ->
  let uu, _ = synth "Type" in
  let xx = assume "X" uu in
  let x0 = assume "x0" xx in
  let x1 = assume "x1" xx in

  (* Identity types are equivalently instantiations of refl of a type *)
  let idx01, _ = synth "Id X x0 x1" in
  let idx01', _ = synth "refl X x0 x1" in
  equal idx01 idx01';
  (* We also have a standard degeneracy notation *)
  let idx01'', _ = synth "X^(e) x0 x1" in
  equal idx01 idx01'';
  let x2 = assume "x2" idx01 in
  let xtox, _ = synth "X → X" in

  (* The identity function acts as the identity *)
  let idmap = check "x ↦ x" xtox in
  let idmapx0, _ = synth "((x ↦ x) : X → X) x0" in
  equal idmapx0 x0;
  unequal idmapx0 x1;
  unsynth "((x ↦ x) : X → X) x2";

  (* refl of the identity function acts as the identity on identifications *)
  let refl_idmap_x2, _ = synth "refl ((x ↦ x) : (X → X)) x0 x1 x2" in

  unsynth "refl ((x ↦ x) : (X → X)) x0 x0 x2";
  unsynth "refl ((x ↦ x) : (X → X)) x0 x0 x0";
  equal refl_idmap_x2 x2;

  (* *)
  let yy = assume "Y" uu in
  let zz = assume "Z" uu in
  let xtoy, _ = synth "X → Y" in
  let ytoz, _ = synth "Y → Z" in
  let xtoz, _ = synth "X → Z" in
  let f = assume "f" xtoy in
  let g = assume "g" ytoz in
  let gof = check "x ↦ g (f x)" xtoz in
  uncheck "x ↦ f (g x)" xtoz;

  (* Identity types of pi-types don't *compute* to the expected thing, but they are isomorphic, by eta-expansion in both directions. *)
  let f' = assume "f'" xtoy in
  let idff, _ = synth "Id (X → Y) f f'" in

  let idff', _ = synth "(x:X) (x':X) (x'':Id X x x') → Id Y (f x) (f' x')" in

  unequal idff idff';

  let idff_to_idff'_ty, _ =
    synth "Id (X → Y) f f' → (x:X) (x':X) (x'':Id X x x') → Id Y (f x) (f' x')" in

  let idff_to_idff' = check "h x x' x'' ↦ h x x' x''" idff_to_idff'_ty in

  let idff'_to_idff_ty, _ =
    synth "((x:X) (x':X) (x'':Id X x x') → Id Y (f x) (f' x')) → Id (X → Y) f f'" in

  let idff'_to_idff = check "k x x' x'' ↦ k x x' x''" idff'_to_idff_ty in
  let idff'_to_idff_cube = check "k x ⤇ k x.0 x.1 x.2" idff'_to_idff_ty in
  equal_at idff'_to_idff idff'_to_idff_cube idff'_to_idff_ty;

  let p = assume "p" idff in
  let q = assume "q" idff' in

  let idff_roundtrip, _ =
    synth
      "((k x x' x'' ↦ k x x' x'') : ((x:X) (x':X) (x'':Id X x x') → Id Y (f x) (f' x')) → Id (X → Y) f f')
       (((h x x' x'' ↦ h x x' x'') : Id (X → Y) f f' → (x:X) (x':X) (x'':Id X x x') → Id Y (f x) (f' x')) p)"
  in

  equal_at idff_roundtrip p idff;

  let idff'_roundtrip, _ =
    synth
      "((h x x' x'' ↦ h x x' x'') : Id (X → Y) f f' → (x:X) (x':X) (x'':Id X x x') → Id Y (f x) (f' x'))
       (((k x x' x'' ↦ k x x' x'') : ((x:X) (x':X) (x'':Id X x x') → Id Y (f x) (f' x')) → Id (X → Y) f f') q)"
  in

  equal_at idff'_roundtrip q idff';

  (* Identity types are invariant under eta-expansion *)
  let idff_eta, _ = synth "Id (X → Y) (x ↦ f x) f'" in
  equal idff idff_eta;

  (* Ap is functorial *)
  let reflg, _ = synth "refl g" in
  let reflf_x2, _ = synth "refl f x0 x1 x2" in
  unsynth "refl g x0 x1 x2";

  let reflg_reflf_x2, _ = synth "refl g (f x0) (f x1) (refl f x0 x1 x2)" in

  let refl_gof_x2, _ = synth "refl ((x ↦ g (f x)) : X → Z) x0 x1 x2" in

  equal reflg_reflf_x2 refl_gof_x2;

  (* The two degenerate squares associated to an identification have unequal types, although each has a standard degeneracy notation. *)
  let r1x2, r1x2ty = synth "refl x2" in
  let r1x2', r1x2ty' = synth "x2⁽¹ᵉ⁾" in
  let () = equal r1x2ty r1x2ty' in
  let () = equal r1x2 r1x2' in

  let r2x2, r2x2ty = synth "refl ((x ↦ refl x) : (x:X) → Id X x x) x0 x1 x2" in
  let r2x2', r2x2ty' = synth "x2⁽ᵉ¹⁾" in
  let () = equal r2x2ty r2x2ty' in
  let () = equal r2x2 r2x2' in

  unequal r1x2ty r2x2ty;

  (* But applying symmetry identifies both their types and values. *)
  let sr1x2, sr1x2ty = synth "sym (refl x2)" in
  equal sr1x2ty r2x2ty;
  equal sr1x2 r2x2;

  let sr1x2', sr1x2ty' = synth "x2^(e)^(21)" in
  equal sr1x2ty sr1x2ty';
  equal sr1x2 sr1x2';

  (* But the two degenerate squares associated to a reflexivity *are* equal. *)
  let r1reflx0, r1reflx0ty = synth "refl (refl x0)" in

  let r2reflx0, r2reflx0ty = synth "refl ((x ↦ refl x) : (x:X) → Id X x x) x0 x0 (refl x0)" in

  equal r1reflx0ty r2reflx0ty;
  equal r1reflx0 r2reflx0;

  let r1reflx0', r1reflx0ty' = synth "x0⁽ᵉᵉ⁾" in
  equal r1reflx0ty r1reflx0ty';
  equal r1reflx0 r1reflx0';

  (* Doubly-degenerate squares are also fixed by symmetry *)
  let sr1reflx0, _ = synth "sym (refl (refl x0))" in
  equal r1reflx0 sr1reflx0;

  ()
