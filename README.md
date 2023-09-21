# Narya

Narya is eventually intended to be a proof assistant implementing Multimodal, Parametric, Higher Observational Type Theory.  However, a formal type theory combining all those adjectives has not yet been specified.  At the moment, Narya implements a normalization-by-evaluation algorithm and typechecker for an observational-style theory with binary Id/Bridge types, with Gel types for internal parametricity as an option.  The alternative option of transport and univalence is not yet implemented, nor are any other modalities included.

Narya is very much a work in progress.  Expect breaking changes, including even in fundamental aspects of the syntax.  But on the other side of the coin, feedback on any and everything is welcome.


## Compilation

Narya requires OCaml version 5.1.0.

```
opam switch create 5.1.0
opam install bwd fmlib_parse
cd narya
dune build
dune runtest
```

There is no executable yet, but you can load the libraries in `utop` and use the `Mcp` commands mentioned below.


## Parsing

Narya cannot read and parse an entire file yet, and doesn't understand any kind of commands or directives.  Thus, one still has to interact with it as an OCaml library.  However, there is a parser for terms which can be used to write them in a convenient way.

The parser supports arbitrary mixfix operations with associativities and precedences, although at present these have to be defined in OCaml.  We prefer to say "tightness" instead of "precedence", to indicate that higher numbers bind more tightly.  Tightnesses are floating-point numbers; ∞ and −∞ are used internally for certain built-in notations, and NaN is used for "closed" notations (those that start and end with a symbol rather than a term) which don't need a tightness.  The built-in notations are:

- `Type` -- The unique universe (currently we have type-in-type).
- `M N` -- Function application (left-associative).
- `x ↦ M` -- Lambda-abstraction.  The unicode ↦ can be replaced by ASCII `|->`.
- `(x : M) → N` -- Pi-type.  The unicode → can be replaced by ASCII `->`.
- `(x : M) (y z : N) (w : P) → Q` -- Multivariable Pi-type.
- `M → N` -- Non-dependent function-type (right-associative).
- `M .fld` -- Field access of a record (left-associative).
- `{ fld1 ≔ M; fld2 ≔ N }` -- Anonymous record (structure).  The unicode ≔ can be replaced by ASCII `:=`.
- `constr. M N` -- Constructor of a datatype, applied to arguments (but not parameters).  Checks, doesn't synthesize.
- `M : N` -- Type ascription.  Necessary if you want to apply an abstraction to an argument (i.e. manually write a beta-redex) or similarly apply a field to a structure, since the typechecker is bidirectional.
- `let x ≔ M in N` -- Local binding.  Computationally equivalent to `(x ↦ N) M`, but also binds `x` to `M` while typechecking `N`, which is stronger in the presence of dependent types.  As before, ≔ can be replaced by `:=`, and `let x ≔ (M : A) in N` (commonly needed since `M` must synthesize) can be abbreviated `let x : A ≔ M in N`.
- `Id M X Y` -- Homogeneous identity/bridge type.
- `refl M` -- Reflexivity term.
- `sym M` -- Symmetry of a two-dimensional square.

Here parentheses have tightness +∞, and function application and field access can be thought of as left-associative operations with no symbols and tightness +∞ although they are implemented specially internally.  On the other hand, abstraction, ascription, and let-bindings have tightness −∞, so they bind more loosely than anything except each other.  Pi-types and function-types have tightness 0.

Of note is that type ascription is non-associative, so `M : N : P` is a parse error.  Abstraction, let-binding, and pi-types are also non-associative: because they start with a name or symbol rather than a term, they don't need to be right-associative in order to get the expected behavior of `x ↦ y ↦ M` and `(x : M) → (y : N) → P`.  This non-associativity means that they cannot be mixed with type ascription: `x ↦ M : A` is a parse error.  This is intentional, as I regard that as inherently ambiguous; you should write either `x ↦ (M : A)` or `(x ↦ M) : A` depending on what you meant.

There is also a syntax for comments, although these are not so useful yet when writing only single terms.  A line comment starts with a backquote \` and extends to the end of the line.  A block comment starts with {\` and ends with \`}.  Block comments can be nested.  However, if (part of) a block comment appears on a line before any code, then no code may appear on that line at all.  In other words, the only whitespace that can appear on a line before code is 0x20 SPACE (tab characters are not allowed anywhere).

As in Agda, mixfix notations can involve arbitrary Unicode characters, but must usually be surrounded by spaces to prevent them from being interpreted as part of an identifier.  However, in Narya this has the following exceptions:

- The characters `( ) { } → ↦ ≔` with built-in meaning are always treated as single tokens.  Thus, they do not need to be surrounded by whitespace.  This is the case for paretheses and braces in Agda, but the others are different: in Narya you can write `A→B`.
- A nonempty string consisting of the characters `[ ] ~ ! @ # $ % ^ & * / ? = + \ | , < > : ; -` is always treated as a single token, and does not need to be surrounded by whitespace.  Note that this is most of the non-alphanumeric characters that appear on a standard US keyboard except for parentheses (grouping), curly braces (structures and, later, implicit arguments), backquote (comments), period (fields, constructors, and namespaces), underscore (later, inferred arguments), double quote (later, string literals) and single quote (allowed for primes on variable names).  In particular:
  - Ordinary algebraic operations like `+` and `*` can be defined so that `x+y` and `x*y` are valid.
  - This includes the colon, so you can write `(x:A) → B`, and similarly for the semicolon separating the fields of a structure.  But the user can also use these characters in other operators, such as `::` for list cons.  (Or you can use the Unicode ∷ if you want to require spacing.)
  - The ASCII substitutes `->` and `|->` and `:=` for the Unicode →, ↦, and ≔ also fall into this category, so you can write `A->B`.

  This rule is intended to be a compromise, allowing the user to define plenty of infix operators that don't require spacing, while keeping the lexer as a simple regexp that doesn't need to change as new operators are defined.

Numerals are strings consisting of digits and periods, not starting or ending with a period.  Identifiers (variables and constant names) can be any string consisting of non-whitespace characters other than the above two groups that does *not* consist entirely of digits and periods, and does not start or end with a period.  Field names, which must be identifiers, are prefixed a period when accessed, and likewise constructor names are postfixed a period when applied.  Identifiers prefixed with one or more underscores are reserved for internal use.  Internal periods in identifiers are reserved to denote namespace qualifiers on constants; thus they cannot appear in local variable names, field names, or constructor names.

Once you have written a raw term using this syntax as an OCaml string, you can parse it and pass it off to the typechecker with these functions defined in `Testutil.Mcp`:

- `synth M` -- Synthesize a type from a term `M` and return the corresponding "value" of `M` as well as the synthesized type (also a value).
- `check M T` -- Check the term `M` against the type `T`, which must be a value.  Returns the value of `M`.

Thus, a common idiom is

```
let theorem_ty, _ = synth "..."
let theorem = check "..." theorem_ty
```
That is, we first write the type of a theorem, synthesize it (its type will be `Type`, which we discard), and then check a proof of that theorem against the resulting value.  Of course this can be shortcut with
```
let theorem = check "..." (fst (synth "..."))
```
Since we don't have a built-in notion of "definition" yet, when a term will be used again later, it is convenient to give a name to its raw syntax also, e.g.
```
let rdefn = "..."
let defn = check rdefn defn_ty
```
Some other helpful functions include:

- `assume "x" T` -- Assume a variable `x` of type `T` (a value), and return that variable (as a value).
- `equal R S` -- Assert that two values are definitionally equal.  They must be synthesizing, since this does no type-directed checking.
- `equal_at R S T` -- Assert that two values `R` and `S` are definitionally equal at the value type `T` (which they are assumed to belong to).


## Constants, records, datatypes, and case trees

Currently, constants can only be built into the OCaml code, not defined by the user.

### Records and coinductive types

A constant that is a type family can be declared (again, currently only in the OCaml code) to be a *record type*, by giving a list of its fields with their types.  The fields themselves are *not* constants; they belong to a separate name domain.  (They can be thought of as analogous to "methods" in an object-oriented programming language.)  Then an element of an instance of that family can have its fields projected out with the postfix syntax `M .fld`, and can be constructed using the record syntax described above.

For example, currently there is an implementation of Sigma-types as a record, which can be accessed by calling `Types.Sigma.install ()`.  The notation for a Sigma-type is `(x:A) × B`, or `A × B` in the non-dependent case (both right-associative and binding tighter than →), with fields `fst` and `snd`, and an infix comma (right-associative) as notation for an anonymous record.

Records can be declared to have, or not have, eta-conversion (Sigma-types do).  Record types can be coinductive, with the type of a field involving the record itself.  Coinductive types should not be declared to have eta-conversion since that is undecidable, but there is no check for that.  Corecursive elements of a coinductive type cannot be constructed as structures, but they can be defined as constants with copattern case trees.  For example, currently there is an implementation of coinductive streams accessible with `Types.Stream.install ()`, with fields `head` and `tail`, and a built-in corecursor `corec` defined with copatterns.

Note that field projections synthesize (hence do not require the parameters of the record type as arguments).  But anonymous structures (including the comma) do not synthesize, so in a synthesizing context you must ascribe them.

### Datatypes and inductive types

A constant that is a type family can also be declared to be a *datatype*, by separating its arguments into parameters and indices, and giving a list of its constructors.  Each constructor has a number of arguments, with types depending on the parameters (but not the indices), and a list of values for the indices depending on values of the arguments.  As with fields, constructors are not constants and belong to a separate name domain.  (This is in line with functional programming languages such as Haskell and OCaml, where constructors have a separate syntax, e.g. begin with a capital letter.)

Once a datatype is defined, the constructors can be used to build elements of it, by applying them like functions (but with a final period on their name, dually to a field projection) to their arguments (but not the parameters or indices of the datatype).  This syntactic form *checks*, rather than synthesizing, against an instance of the datatype.  You can define another constant to equal an application of a constructor, however, and it will synthesize.

Datatypes can be inductive, with the arguments of constructors involving the datatype itself.

For example, currently there is an implementation of the natural numbers, which can be accessed by calling `Types.Nat.install ()`, with the general recursor/inductor, and also addition and multiplication constants defined by direct case trees rather than in terms of the recursor.  The latter have right-associative infix notations `+` and `*`, with `*` binding more tightly, and also numeral notations.  There are also implementations of sum types (with two type parameters), lists (with type parameter), and vectors (with type parameter and length index).

### Defined constants

Constants that are not records or datatypes can be axioms (undefined), or they can be stipulated to compute according to any *case tree*.  A case tree alternates abstractions with pattern matches against constructors and copattern comatches against fields.  A degenerate version of a case tree simply defines the constant to equal some given term.

As noted, case trees can include fields (copatterns) as well as matches against other constants (patterns).  Thus it is also possible to define constructors of records by case trees, in addition to as structures.  These have the advantage that they synthesize, but the disadvantage that they must be applied explicitly to all the parameters.  For example, Sigma-types also come with a `pair` constructor defined in this way; one can write `pair A B a b` instead of `{ fst ≔ a; snd ≔ b }` or `(a,b)`.

A constant defined by a case tree does not compute unless the tree can be followed all the way down to a leaf.  In particular, a "match" or "comatch" is never exposed as part of a term.  Moreover, this means that when defining a constant to equal a given term, by putting the abstractions into the case tree rather than the term you can specify that it must be applied to some number of arguments in order to compute.  Usually one would want to do this with all the arguments, so that the bare constant doesn't compute to an abstraction but only computes to the body of that abstraction once it's fully applied.

There is currently no parsing or typechecking for definitions of constants, case trees, records, and datatypes: the programmer is required and trusted to write them by hand in abstract syntax with De Bruijn indices.  In particular, there is no coverage, positivity, termination, or productivity checking.


## Parametric Observational Type Theory

The identity/bridge type of a pi-type computes to another pi-type.  In Narya this computation is "up to definitional isomorphism", meaning that the following two types are isomorphic:
```
id ((x:A) → B) f g
(x₀ : A) (x₁ : A) (x₂ : id A x₀ x₁) → id B (f x₀) (g x₁)
```
However, in most cases we can pretend that these two types are literally the same, because the typechecker allows lambda-abstractions matching the structure of the second to also typecheck at the first, and likewise elements of the first can be applied to arguments as if they were functions belonging to the second.  There is no unifier yet, so such an application must include both endpoints `x₀` and `x₁` explicitly as well as the identity `x₂`.

There is no primitive `ap`; instead it is accessed by applying `refl` to a function.  That is, if `f : (x:A) → B`, then `refl f x₀ x₁ x₂` relates `f x₀` to `f x₁` in `B`.  Likewise, identity types can be obtained by applying `refl` to a type: `Id M X Y` is just a convenient abbreviation of `refl M X Y`.

Heterogeneous identity/bridge types are similarly obtained from `refl` of a type family: if `B : A → Type`, then `refl B x₀ x₁ x₂` is a identification/bridge in `Type` between `B x₀` and `B x₁`.  Given elements `y₀ : B x₀` and `y₁ : B x₁`, we can "instantiate" this identification at them to obtain a type of heterogeneous identifications.  This is also written as function application, `refl B x₀ x₁ x₂ y₀ y₁`.

The identity/bridge type of a record type is another record type, which inherits eta-conversion and uses the same field names as the original.  For instance, `Id ((x:A) × B) X Y` is a record type with fields `fst` and `snd`, where for `s : Id ((x:A) × B) X Y` we have
```
s .fst  :  Id A (X .fst) (Y .fst)
s .snd  :  refl B (X .fst) (Y .fst) (s .fst) (X .snd) (Y .snd)
```
Since it also satisfies eta-conversion, this record is definitionally isomorphic (but not equal) to another Sigma-type
```
(p : Id A (X .fst) (Y .fst)) × refl B (X .fst) (Y .fst) p (X .snd) (Y .snd)
```
Similarly to the case with function-types, since the fields of `Id ((x:A) × B) X Y` are again named `fst` and `snd`, in most cases one can pretend it is actually equal to the latter Sigma-type, including constructing elements of it with `{ fst ≔ P; snd ≔ Q }`.

This applies also to corecursive record types, whose identity/bridge types are thus coinductive types of bisimulations.  We can use structures to construct bisimulations that become trivial after a finite number of steps, such as to prove propostional one-step eta-expansion, but for infinitary ones we would need a corecursion.  And since bisimulation types are *indexed* coinductive types it does not seem possible to formulate a generic corecursor for them by postulating a single typed constant with a case tree.  Thus, in practice, nontrivial bisimulations are inaccessible until we give the user the ability to define (and typecheck) their own constants with case trees.

The identity/bridge type of a datatype is currently itself another datatype, with constructors applied at higher elements to construct their elements (with the boundary treated like indices), and case trees allowed to discriminate on them.  It's unclear whether the latter is correct, so it might change.

Internal parametricity is implemented by the constant `Gel`, defined with `Types.Gel.install ()`, whose type is
```
(A : Type) (B : Type) (R : (x:A) (y:B) → Type) → Id Type A B
```
As above, since `Gel A B R` is an identification in the universe, it can be further instantiated at elements `a : A` and `b : B` to obtain a type `Gel A B R a b`.  This type is isomorphic to the original `R a b`.  In fact, `Gel` is declared as a special kind of "one-dimensional record type" (in contrast to the usual zero-dimensional ones) with eta-conversion, with a single field `ungel` of type `R a b`.  Thus the isomorphism is implemented by, on the one hand, accessing this field `M .ungel`, and on the other by building a record `{ ungel ≔ M }`.  (The code actually allows for record types of arbitrary dimension, but in practice Gel is the only one expected to be needed.)


## Remarks on implementation

As is common for normalization-by-evaluation, the implementation uses De Bruijn *indices* for syntactic terms and De Bruijn *levels* for semantic values.  A little more unusually, however, the De Bruijn indices are intrinsically well-scoped.  This means that the type of terms is parametrized by the length of the context (as a type-level natural number, using GADTs), so that the OCaml compiler ensures *statically* that De Bruijn indices never go out of scope.  Other consistency checks are also ensured statically in a similar way, such as the matching of dimensions for certain types and operators.

This approach does have the drawback that it requires a fair amount of arithmetic on the natural numbers to ensure well-typedness, which is not only tedious but some of it also ends up happening at run-time.  Since type-level natural numbers are represented in unary, this could be a source of inefficiency in the future.
