# Narya

Narya is eventually intended to be a proof assistant implementing Multimodal, Parametric, Higher Observational Type Theory.  However, a formal type theory combining all those adjectives has not yet been specified.  At the moment, Narya implements a normalization-by-evaluation algorithm and typechecker for an observational-style theory with binary Id/Bridge types, with Gel types for internal parametricity as an option.  The alternative option of transport and univalence is not yet implemented, nor are any other modalities included.


## Poor man's parser

There is no parser or pretty-printer yet.  However, there is a "poor man's parser" implemented as a DSL in OCaml with infix and prefix operators, which is used to formalize a number of examples in the `test/` directory.  It is loaded with `open Pmp`, which makes available the following syntax for terms:

- `!!"x"` -- Use a variable (again, an OCaml string).
- `!~"c"` -- Use a built-in constant, such as `Sig` or `Gel`.
- `UU` -- Universe (currently we have type-in-type).
- `M $ N` -- Function application (left-associative).
- `"x" @-> M` -- Lambda-abstraction (right-associative).  Note the variable must be an OCaml string.
- `("x", M) @=> N` -- Pi-type (right-associative).
- `M $. "fld"` -- Field access of a record (left-associative).
- `struc [("fld1", M); ("fld2", N)]` -- Anonymous record (structure).
- `M <:> N` -- Type ascription.  Necessary if you want to apply an abstraction to an argument (i.e. manually write a beta-redex) or similarly apply a field to a structure, since the typechecker is bidirectional.
- `id M X Y` -- Homogeneous identity/bridge type.
- `refl M` -- Reflexivity term.
- `sym M` -- Symmetry of a two-dimensional square.

This grammar produces a "raw term" which can be either synthesized or checked against a type, using the following functions:

- `synth M` -- Synthesize a type from a term `M` and return the corresponding "value" of `M` as well as the synthesized type (also a value).
- `check M T` -- Check the term `M` against the type `T`, which must be a value.  Returns the value of `M`.

Thus, a common idiom is

```
let theorem_ty, _ = synth (...)
let theorem = check (...) theorem_ty
```
That is, we first write the type of a theorem, synthesize it (its type will be `UU`, which we discard), and then check a proof of that theorem against the resulting value.  Of course this can be shortcut with
```
let theorem = check (...) (fst (synth (...)))
```
Some other helpful functions include:

- `assume "x" T` -- Assume a variable `x` of type `T` (a value), and return that variable (as a value).
- `equal R S` -- Assert that two values are definitionally equal.  They must be synthesizing, since this does no type-directed checking.
- `equal_at R S T` -- Assert that two values `R` and `S` are definitionally equal at the value type `T` (which they are assumed to belong to).


## Constants, case trees, and records

Currently, constants can only be built into the OCaml code, not defined by the user.  But when defined, they can be stipulated to compute according to any case tree.  For example, currently there is an implementation of the natural numbers with addition, which can be accessed by calling `Narya.Nat.install ()`.

A constant that is a type family can be declared (again, only in the OCaml code) as a record type by giving a list of fields with their types.  Then an element of an instance of that family can have its fields projected out, and can be constructed using the record syntax given above.  For example, currently there is an implementation of Sigma-types as a record, which can be accessed by calling `Narya.Sigma.install ()`.  Records can be declared to have, or not have, eta-conversion (Sigma-types do).  Note that `struc` does not synthesize, so in a synthesizing context you must ascribe it.

Case trees can include fields (copatterns) as well as matches against other constants (patterns).  Thus it is also possible to define constructors of records by case trees, in addition to `struc`.  These have the advantage that they synthesize, but the disadvantage that they must be applied explicitly to all the parameters.  For example, Sigma-types also come with a `pair` constructor defined in this way; one can write `!~"pair" $ !!"A" $ !!"B" $ !!"a" $ !!"b"` instead of `struc [("fst", !!"a"); ("snd", !!"b")]`.

Record types can be coinductive, with the type of a field involving the record itself.  Coinductive types should not be declared to have eta-conversion since that is undecidable, but there is no check for that.  Corecursive elements of a coinductive type cannot be constructed with `struc`, but they can be defined as constants with copattern case trees.  For example, currently there is an implementation of coinductive streams accessible with `Narya.Stream.install ()`, with a built-in corecursor `corec` defined with copatterns.

There is currently no parsing or typechecking for constants, case trees, and records: the programmer is required and trusted to write them by hand in abstract syntax with De Bruijn indices.  In particular, there is no coverage, termination, or productivity checking.  Branches of case trees also do not specialize any previous arguments, so using them for indexed inductive types is questionable.


## Parametric Observational Type Theory

The identity/bridge type of a pi-type computes to another pi-type.  In Narya this computation is "up to definitional isomorphism", meaning that the following two types are isomorphic:
```
id (("x", A) @=> B) F G
("x0", A) @=> ("x1", A) @=> ("x2", id A !!"x0" !!"x1") @=> (id B (F $ !!"x0") (G $ !!"x1))
```
However, in most cases we can pretend that these two types are literally the same, because the typechecker allows lambda-abstractions matching the structure of the second to also typecheck at the first, and likewise elements of the first can be applied to arguments as if they were functions belonging to the second.  There is no unifier yet (duh), so such an application must include both endpoints `x0` and `x1` explicitly as well as the identity `x2`.

There is no primitive `ap`; instead it is accessed by applying `refl` to a function.  That is, if `f : ("x", A) @=> B`, then `refl f $ x0 $ x1 $ x2` relates `f $ x0` to `f $ x1` in `B`.  Likewise, identity types can be obtained by applying `refl` to a type: `id M X Y` is just a convenient abbreviation of `refl M $ X $ Y`.

Heterogeneous identity/bridge types are similarly obtained from `refl` of a type family: if `B : ("", A) @=> UU`, then `refl B $ x0 $ x1 $ x2` is a identification/bridge in `UU` between `B $ x0` and `B $ x1`.  Given elements `y0 : B $ x0` and `y1 : B $ x1`, we can "instantiate" this identification at them to obtain a type of heterogeneous identifications.  This is also written as function application, `refl B $ x0 $ x1 $ x2 $ y0 $ y1`.

The identity/bridge type of a record type is another record type, which inherits eta-conversion and uses the same field names as the original.  For instance, `id (!~"Sig" $ A $ B) X Y` is a record type with fields `fst` and `snd`, having types
```
s $. "fst"  :  id !!"A" (X $. "fst") (Y $. "fst")
s $. "snd"  :  refl B $ (X $. "fst") $ (Y $. "fst") $ (s $. "fst") $ (X $. "snd") $ (Y $. "snd")
```
Since it also satisfies eta-conversion, this record is definitionally isomorphic (but not equal) to another Sigma-type
```
!~"Sig" $ (id !!"A" (X $. "fst") (Y $. "fst")) $ ("p" @-> refl B $ (X $. "fst") $ (Y $. "fst") $ !!"p" $ (X $. "snd") $ (Y $. "snd"))
```
As with function-types, since the fields of `id (!~"Sig" $ A $ B) X Y` are again named `fst` and `snd`, in most cases one can pretend it is actually equal to the latter Sigma-type, including constructing elements of it with `struc [("fst", P); ("snd", Q)]`.

This applies also to corecursive record types, whose identity/bridge types are thus coinductive types of bisimulations.  However, `struc` does not suffice to construct any nontrivial bisimulation, and since bisimulation types are *indexed* coinductive types it does not seem possible to formulate a generic corecursor for them by postulating a single typed constant with a case tree.  Thus, in practice bisimulations are inaccessible until we give the user the ability to define (and typecheck) their own constants with case trees.

Internal parametricity is implemented by the constant `Gel`, whose type is
```
("A", UU) @=> ("B", UU) @=> ("R", ("x", !!"A") @=> ("y", !!"B") @=> UU) @=> id U !!"A" !!"B"
```
As above, since `!~"Gel" $ A $ B $ R` is an identification in the universe, it can be further instantiated at elements `a : A` and `b : B` to obtain a type `!~"Gel" $ A $ B $ R $ a $ b`.  This type is isomorphic to the original `R $ a $ b`.  In fact, `Gel` is declared as a special kind of "one-dimensional record type" with eta-conversion, with a single field `ungel` of type `R $ a $ b`.  Thus the isomorphism is implemented by, on the one hand, accessing this field `M $. "ungel"`, and on the other by building a record `struc [("ungel", M)]`.  (The code actually allows for record types of arbitrary dimension, but in practice Gel is the only one expected to be needed.)

To access `Gel`, you need to first call `Narya.Gel.install ()`.


## Remarks on implementation

As is common for normalization-by-evaluation, the implementation uses De Bruijn *indices* for syntactic terms and De Bruijn *levels* for semantic values.  A little more unusually, however, the De Bruijn indices are intrinsically well-scoped.  This means that the type of terms is parametrized by the length of the context (as a type-level natural number, using GADTs), so that the OCaml compiler ensures *statically* that De Bruijn indices never go out of scope.  Other consistency checks are also ensured statically in a similar way, such as the matching of dimensions for certain types and operators.

This approach does have the drawback that it requires a fair amount of arithmetic on the natural numbers to ensure well-typedness, which is not only tedious but some of it also ends up happening at run-time.  Since type-level natural numbers are represented in unary, this could be a source of inefficiency in the future.
