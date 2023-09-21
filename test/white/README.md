This directory contains "white-box" tests that call library functions directly, often using the Testutils utilities to construct terms by hand.  Some of them use the "poor man's parser" from `Testutil.Pmp`, which is implemented as a DSL in OCaml with infix and prefix operators.  This is largely for historical reasons, since these tests were written before the actual parser, but it also means those tests don't depend on the parser.

- `!!"x"` -- Use a variable (an OCaml string).
- `!~"c"` -- Use a built-in constant, such as `Sig` or `Gel` (also an OCaml string).
- `!."c"` -- Use a built-in datatype constructor (an OCaml string).
- `UU` -- The universe
- `M $ N` -- Function application (left-associative).
- `"x" @-> M` -- Lambda-abstraction (right-associative).  The variable must be an OCaml string.
- `("x", M) @=> N` -- Pi-type (right-associative).
- `M $. "fld"` -- Field access of a record (left-associative).  The field is an OCaml string.
- `struc [("fld1", M); ("fld2", N)]` -- Anonymous record (structure).
- `M <:> N` -- Type ascription.
- `id M X Y` -- Identity/bridge type.
- `refl M` -- Reflexivity.
- `sym M` -- Symmetry.

Here the associativities and precedence are determined by the uniform rules of OCaml, based on the first character of each infix operator.  In particular, this means that `@->` and `@=>` bind tighter than `$`, so you have to write `"x" @-> (M $ !!"x")` but you can write `!!"f" $ "x" @-> M`.  (This is the opposite of the "real" parser described above.)
