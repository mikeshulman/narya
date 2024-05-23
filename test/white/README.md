This directory contains "white-box" tests that call library functions directly, often using the Testutils utilities to construct terms by hand.

### Old-style interaction

Many of these tests use the interaction facilities in `Testutil.Pmp` and `Testutil.Mcp`, which were written before it was possible to typecheck definitions of constants.  (The difference between the two is in the parser they use, see below.)  Thus, they add variables to the context rather than defining constants, and store terms and values in OCaml variables.  The basic interaction functions in these packages are:

- `synth M` -- Synthesize a type from a term `M` and return the corresponding "value" of `M` as well as the synthesized type (also a value).
- `check M T` -- Check the term `M` against the type `T`, which must be a value.  Returns the value of `M`.
- `assume "x" T` -- Assume a variable `x` of type `T` (a value), and return that variable (as a value).
- `equal R S` -- Assert that two values are definitionally equal.  They must be synthesizing, since this does no type-directed checking.
- `equal_at R S T` -- Assert that two values `R` and `S` are definitionally equal at the value type `T` (which they are assumed to belong to).
- `unsyth M` -- Verify that the term `M` *doesn't* synthesize.
- `uncheck M T` -- Verify that the term `M` *doesn't* typecheck at value type `T`.
- `unequal R S` -- Assert that two synthesizing values are *not* definitionally equal.
- `unequal_at R S T` -- Assert that two values `R` and `S` are *not* definitionally equal at the value type `T`.

In particular, a common idiom is

```
let theorem_ty, _ = synth "..."
let theorem = check "..." theorem_ty
```
That is, we first write the type of a theorem, synthesize it (its type will be `Type`, which we discard), and then check a proof of that theorem against the resulting value.  Of course this can be shortcut with
```
let theorem = check "..." (fst (synth "..."))
```
Since there wasn't a built-in notion of "definition", when a term will be used again later, it was convenient to give a name to its raw syntax also, e.g.
```
let rdefn = "..."
let defn = check rdefn defn_ty
```

### Poor-man's parser

Some of these tests also use the "poor man's parser" from `Testutil.Pmp`, which is implemented as a DSL in OCaml with infix and prefix operators.  This is largely for historical reasons, since these tests were written before the actual parser, but it also means those tests don't depend on the parser.

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

