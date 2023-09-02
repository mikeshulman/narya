open Testutil.Mcp

let uu, _ = synth "Type"
let aa = assume "A" uu
let atou, _ = synth "A → Type"
let bb = assume "B" atou
let atob, _ = synth "(x : A) → B x"
let f = assume "f" atob
let () = unequal atou atob
let () = equal f f
let abtou, _ = synth "(x:A)→ B x → Type"
let cc = assume "C" abtou
let abtoc, _ = synth "(x:A)→(y:B x)→C x y"
let g = assume "g" abtoc
let a0 = assume "a₀" aa
let a1 = assume "a₁" aa
let ida01, _ = synth "Id A a₀ a₁"
let ida01', _ = synth "refl A a₀ a₁"
let () = equal ida01 ida01'
let a2 = assume "a₂" ida01
let fa2, fa2ty = synth "refl f a₀ a₁ a₂"
let fa2ty', _ = synth "refl B a₀ a₁ a₂ (f a₀) (f a₁)"
let () = equal fa2ty fa2ty'
let f' = check "x ↦ f x" atob
let () = equal_at f f' atob
let f'', _ = synth "(x ↦ f x) : (x:A)→ B x"
let () = equal_at f f'' atob

(* Since lambdas and ascription have the same scope, and ascription is nonassociative, this is a parse error.  I think this is a good thing, because it *looks* ambiguous to me.  The user should disambiguate it with parentheses. *)
let () = unparse "x ↦ f x : (x:A)→ B x"

(* Cubes *)
let xx = assume "X" uu
let x00 = assume "x00" xx
let x01 = assume "x01" xx
let xx02, _ = synth "Id X x00 x01"
let x02 = assume "x02" xx02
let x10 = assume "x10" xx
let x11 = assume "x11" xx
let xx12, _ = synth "Id X x10 x11"
let x12 = assume "x12" xx12
let xx20, _ = synth "Id X x00 x10"
let xx21, _ = synth "Id X x01 x11"
let x20 = assume "x20" xx20
let x21 = assume "x21" xx21
let xx22, _ = synth "refl (refl X) x00 x01 x02 x10 x11 x12 x20 x21"
let x22 = assume "x22" xx22
let sx22, sx22ty = synth "sym x22"
let sx22ty', _ = synth "refl (refl X) x00 x10 x20 x01 x11 x21 x02 x12"
let () = equal sx22ty sx22ty'

(* Applied ascriptions *)
let ida = check "((x ↦ x) : A → A) a₀" aa
let () = equal ida a0

(* Check for the ambiguity bug. *)
let _ = synth "(A:Type) → (A:Type) → A"

(* Efficiency *)
let churchnat, _ = synth "(X:Type) → (X → X) → (X → X)"

let cnat n =
  let rec cnat n = if n <= 0 then "x" else "(f " ^ cnat (n - 1) ^ ")" in
  "X f x ↦ " ^ cnat n

(* This is near instantaneous. *)
let fifty = check (cnat 50) churchnat

(* Doing 100 takes a noticeable fraction of a second, but only in the typechecking; the parsing is still near instantaneous. *)
let cien = Parser.Parse.term Util.Bwv.Emp (cnat 100)

(* Parsing church numerals starts to take a noticable fraction of a second around 250. *)

let () = Types.Sigma.install ()
let sigab, _ = synth "(x:A) × B x"
let s = assume "s" sigab
let s1, s1ty = synth "s .fst"
let () = equal s1ty aa
let s2, s2ty = synth "s .snd"
let s2ty', _ = synth "B (s .fst)"
let () = equal s2ty s2ty'
let ba0, _ = synth "B a₀"
let b0 = assume "b₀" ba0
let ab0 = check "{ fst ≔ a₀; snd := b₀ }" sigab
let () = uncheck "{ fst ≔ a₁; snd := b₀ }" sigab
let a0', _ = synth "({ fst ≔ a₀; snd ≔ b₀ } : (x:A) × B x) .fst"
let () = equal a0 a0'
let b0', _ = synth "({ fst ≔ a₀; snd ≔ b₀ } : (x:A) × B x) .snd"
let () = equal b0 b0'
let ab0' = check "a₀ , b₀" sigab
let a0'', _ = synth "((a₀ , b₀) : (x:A) × B x) .fst"
let () = equal a0 a0''

(* Right-associativity of prod and comma *)
let dd = assume "D" uu
let ee = assume "E" uu
let a = assume "a" aa
let d = assume "d" dd
let e = assume "e" ee
let aaddee, _ = synth "A × D × E"
let aaddee', _ = synth "A × (D × E)"
let aaddee'', _ = synth "(A × D) × E"
let () = equal aaddee aaddee'
let () = unequal aaddee aaddee''
let ade = check "a , d , e" aaddee
let () = uncheck "a , d , e" aaddee''

(* Interaction of prod and arrow *)
let t, _ = synth "(x:A) → (y:D) × E"
let x = assume "x" t
let _ = check "x a .fst" dd
let () = unparse "(x:A) × (y:D) → E"
let t, _ = synth "(x:A) → D × E"
let x = assume "x" t
let _ = check "x a .fst" dd
let t, _ = synth "(x:A) × D → E"
let x = assume "x" t
let _ = check "x (a,d)" ee
let t, _ = synth "A → (y:D) × E"
let x = assume "x" t
let _ = check "x a .fst" dd
let _ = unparse "A × (y:B) → C"
let t, _ = synth "A → D × E"
let x = assume "x" t
let _ = check "x a .fst" dd
let t, _ = synth "A × D → E"
let x = assume "x" t
let _ = check "x (a,d)" ee

(* Sigmas could also have an ambiguity bug. *)
let _ = synth "(A:Type) × (A:Type) × A"

(* Let's try some comments *)
let _ = synth "(x : A) → ` a line comment
 B x"

let _ = synth "(x : A) {` a block comment `} →  B x"

let _ = synth "(x : A) {` a block comment
 spanning multiple
lines`} →  B x"

let _ =
  synth
    "(x : A) {` a block comment
 containing ` a line comment
 and showing that {` block comments
don't nest `} →  B x"

let _ =
  synth
    "(x : A) {`` but block comments
 with different {` numbers of `} backquotes
can be nested ``} →  B x"

(* Precedence and associativity *)
let () = Types.Nat.install ()
let onetwothree, _ = synth "S O + S (S O) + S (S (S O))"
let six, _ = synth "S (S (S (S (S (S O)))))"
let () = equal onetwothree six
let twotwo_two, _ = synth "S (S O) * S (S O) + S (S O)"
let () = equal twotwo_two six
let twotwo_two, _ = synth "S (S O) * (S (S O) + S (S O))"
let () = unequal twotwo_two six

(* But we can't mix operations that don't have a declared precedence relation.  (Never mind that this won't typecheck; it won't even parse.) *)
let () = unparse "S O * S O → S O"

(* To parse it, we need parentheses. *)
let () = unsynth "(S O * S O) → S O"
let () = unsynth "S O * (S O → S O)"

(* Numeral notations *)
let nsix, _ = synth "6"
let () = equal six nsix
let thirty, _ = synth "30"
let thirty', _ = synth "3*10"
let () = equal thirty thirty'

(* Identifiers can start with digits, but an identifier consisting entirely of digits leads to ambiguous parses in the presence of numeral notations. *)
let atoa, _ = synth "A → A"
let _ = check "0a ↦ 0a" atoa
let () = ambparse "0 ↦ 0"
