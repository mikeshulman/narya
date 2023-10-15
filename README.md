# Narya

Narya is eventually intended to be a proof assistant implementing Multi-Modal, Multi-Parametric, Higher Observational Type Theory.  However, a formal type theory combining all those adjectives has not yet been specified.  At the moment, Narya implements a normalization-by-evaluation algorithm and typechecker for an observational-style theory with binary Id/Bridge types, with Gel types for internal parametricity as an option.  The alternative option of transport and univalence is not yet implemented, nor are any other modalities included.

Narya is very much a work in progress.  Expect breaking changes, including even in fundamental aspects of the syntax.  But on the other side of the coin, feedback on anything and everything is welcome.


## Compilation

Narya requires OCaml version 5.1.0 and the libraries [Bwd](https://github.com/redprl/ocaml-bwd), [Asai](https://redprl.org/asai/asai/), [Yuujinchou](https://redprl.org/yuujinchou/yuujinchou/), and [Fmlib_parse](https://hbr.github.io/fmlib/odoc/fmlib_parse/index.html).  The version of Asai is not yet in Opam, so you need to compile that from source.

```
opam switch create 5.1.0
opam install bwd yuujinchou fmlib_parse
git clone git@github.com:RedPRL/asai.git
cd asai
dune build
dune install
cd ../narya
dune build
dune runtest
```

There is no executable yet, but you can load the library in an OCaml executable and interact with it using the `Repl` commands mentioned below.


## Parsing

The parser supports arbitrary mixfix operations with associativities and precedences, although at present these have to be defined (like everything else) using the OCaml interface.  We prefer to say "tightness" instead of "precedence", to make it clear that higher numbers bind more tightly.  Tightnesses are floating-point values; ∞ and −∞ are reserved for internal use, while NaN is used for "closed" notations (those that start and end with a symbol rather than a term) which can occur anywhere and thus don't need a tightness.  More generally, notations can be either left-closed or left-open, and either right-closed or right-open, and tightness and associativity are only relevant on the open side(s).  The built-in notations are:

- `( M )` – Parentheses for grouping (a closed notation).
- `Type` – The unique universe (currently we have type-in-type).
- `M N` – Function application (left-associative).
- `x ↦ M` – Lambda-abstraction.  The unicode ↦ can be replaced by ASCII `|->`.
- `(x : M) → N` – Pi-type.  The unicode → can be replaced by ASCII `->`.
- `(x : M) (y z : N) (w : P) → Q` – Multivariable Pi-type.
- `M → N` – Non-dependent function-type (right-associative).
- `M .fld` – Field access of a record (left-associative).
- `{ fld1 ≔ M; fld2 ≔ N }` – Anonymous record (structure).  The unicode ≔ can be replaced by ASCII `:=`.  Checks, doesn't synthesize.
- `constr. M N` – Constructor of a datatype, applied to arguments (but not parameters).  Checks, doesn't synthesize.
- `M : N` – Type ascription.  Necessary if you want to apply an abstraction to an argument (i.e. manually write a beta-redex) or similarly apply a field to a structure, since the typechecker is bidirectional.
- `let x ≔ M in N` – Local binding.  Computationally equivalent to `(x ↦ N) M`, but also binds `x` to `M` while typechecking `N`, which is stronger in the presence of dependent types.  As before, ≔ can be replaced by `:=`, and `let x ≔ (M : A) in N` (commonly needed since `M` must synthesize) can be abbreviated `let x : A ≔ M in N`.
- `match x with constr1. a b ↦ M | constr2. c d ↦ N end` – Match against datatype constructors.  Only valid in a top-level case tree (see below).
- `Id M X Y` – Homogeneous identity/bridge type.  In fact this is equivalent to `refl M X Y`, and `Id` is just a synonym for `refl`.
- `refl M` – Reflexivity term.
- `sym M` – Symmetry of a two-dimensional square.

Function application and field access can be thought of as left-associative operations with zero symbols and tightness +∞, although they are implemented specially internally so that tightness +∞ is not technically actually used currently.  On the other hand, abstraction, ascription, and let-bindings have tightness −∞, so they bind more loosely than anything except each other.  Pi-types and function-types have tightness 0.

Of note is that type ascription is non-associative, so `M : N : P` is a parse error.  Abstraction, let-binding, and pi-types are also non-associative: because they are left-closed, they don't need to be right-associative in order to get the expected behavior of `x ↦ y ↦ M` and `(x : M) → (y : N) → P` (although note that these are redundant since one can also write `x y ↦ M` and `(x : M) (y : N) → P`).  This non-associativity means that they cannot be mixed with type ascription: `x ↦ M : A` is a parse error.  This is intentional, as I regard that as inherently ambiguous; you should write either `x ↦ (M : A)` or `(x ↦ M) : A` depending on what you meant.

There is also a syntax for comments, although these are not so useful yet when writing only single terms.  A line comment starts with a backquote \` and extends to the end of the line.  A block comment starts with {\` and ends with \`}.  Block comments can be nested.  However, if (part of) a block comment appears on a line before any code, then no code may appear on that line at all.  In other words, the only whitespace that can appear on a line before code is 0x20 SPACE (tab characters are not allowed anywhere).

As in Agda, mixfix notations can involve arbitrary Unicode characters, but must usually be surrounded by spaces to prevent them from being interpreted as part of an identifier.  However, in Narya this has the following exceptions:

- The characters `( ) { } → ↦ ≔` with built-in meaning are always treated as single tokens.  Thus, they do not need to be surrounded by whitespace.  This is the case for paretheses and braces in Agda, but the others are different: in Narya you can write `A→B`.
- A nonempty string consisting of the characters `[ ] ~ ! @ # $ % ^ & * / ? = + \ | , < > : ; -` is always treated as a single token, and does not need to be surrounded by whitespace.  Note that this is most of the non-alphanumeric characters that appear on a standard US keyboard except for parentheses (grouping), curly braces (structures and, later, implicit arguments), backquote (comments), period (fields, constructors, and, later, namespaces), underscore (later, inferred arguments), double quote (later, string literals) and single quote (allowed for primes on variable names).  In particular:
  - Ordinary algebraic operations like `+` and `*` can be defined so that `x+y` and `x*y` are valid.
  - This includes the colon, so you can write `(x:A) → B`, and similarly for the semicolon separating the fields of a structure.  But the user can also use these characters in other operators, such as `::` for list cons.  (Or you can use the Unicode ∷ if you want to require spacing.)
  - The ASCII substitutes `->` and `|->` and `:=` for the Unicode →, ↦, and ≔ also fall into this category, so you can write `A->B`.
  - Currently the ASCII hyphen `-` is in this category, allowing a subtraction operator `x-y` to be written without spaces.  (Note, though, that the current parser does not permit a binary subtraction to coexist with a unary negation using the same character.)  However, it might move out of this category in the future so that identifiers can be written in Agda style as `some-long-name` rather than `some_long_name` or `SomeLongName` — input from users on this question is welcome!

  This rule is intended to be a compromise, allowing the user to define plenty of infix operators that don't require spacing but also arbitrary unicode operators, while keeping the lexer rules simple and unchanging as new operators are defined.  If it turns out to be too unintuitive, it may be changed.

Numerals are strings consisting of digits and periods, not starting or ending with a period.  Identifiers (variables and constant names) can be any string consisting of non-whitespace characters other than the above two groups that does *not* consist entirely of digits and periods, and does not start or end with a period.  (In particular, identifiers may start with a digit as long as they do not consist entirely of digits and periods.)  Field names, which must be identifiers, are prefixed a period when accessed, and likewise constructor names are postfixed a period when applied.  Identifiers prefixed with one or more underscores are reserved for internal use.  Internal periods in identifiers are reserved to denote namespace qualifiers on constants; thus they cannot appear in local variable names, field names, or constructor names.

## REPL

Narya cannot read and parse an entire file yet, so one has to interact with it as an OCaml library.  Currently the easiest way to do this is with the following functions defined in `Testutil.Repl`.  They must be called inside a wrapper of `run @@ fun () ->` which supplies a namespace for definitions, with each call to `run` using a fresh namespace.

- `def NAME TYPE TERM` – Define a global constant called `NAME` having type `TYPE` and value `TERM`.  The arguments `NAME`, `TYPE`, and `TERM` must all be (double-quoted) OCaml strings.  Thus `NAME` must be a valid identifier, while `TYPE` must parse and typecheck at type `Type`, and `TERM` must parse and typecheck at type `TYPE`.  In addition, `TERM` can be a case tree (see below).

- `assume NAME TYPE` – Assert a global constant called `NAME` having type `TYPE`, without any definition (an axiom).

- `undef NAME` – Remove the global constant `NAME` from the environment.

- `equal_at M N T` – Check that the terms `M` and `N` both belong to the type `T` and are equal.

- `unequal_at M N T` – Check that the terms `M` and `N` both belong to the type `T` but are *not* equal.

For an example of how to use these functions, see the file [constants.ml](test/white/constants.ml).


## Constants, records, datatypes, and case trees

### Records and coinductive types

A constant that is a type family can be declared to be a *record type*, by giving a list of its fields with their types.  (Currently, this is only possible with direct OCaml coding, not through the Repl interface.)  The fields themselves are *not* constants; they belong to a separate name domain.  (They can be thought of as analogous to "methods" in an object-oriented programming language.)  Then an element of an instance of that family can have its fields projected out with the postfix syntax `M .fld`, and can be constructed using the record syntax described above.

For example, currently there is an implementation of Sigma-types as a record, which can be accessed by calling `Types.Sigma.install ()`.  The notation for a Sigma-type is `(x:A) × B`, or `A × B` in the non-dependent case (both right-associative and with tightness 10, tighter than →), with fields `fst` and `snd`, and an infix comma (right-associative) as notation for an anonymous record.  The Unicode × can be replaced by ASCII `><`.

Records can be declared to have, or not have, eta-conversion (Sigma-types do).  Record types can be coinductive, with the type of a field involving the record itself.  Coinductive types should not be declared to have eta-conversion since that is undecidable, but there is no check for that.  Corecursive elements of a coinductive type cannot be constructed as structures, but they can be defined as constants with copattern case trees (see below).  For example, currently there is an implementation of coinductive streams accessible with `Types.Stream.install ()`, with fields `head` and `tail`, and a built-in corecursor `corec` defined with copatterns.

Note that field projections synthesize (hence do not require the parameters of the record type as arguments).  But anonymous structures (including the comma) do not synthesize, so in a synthesizing context you must ascribe them.

### Datatypes and inductive types

A constant that is a type family can also be declared (again, currently only in OCaml code) to be a *datatype*, by separating its arguments into parameters and indices, and giving a list of its constructors.  Each constructor has a number of arguments, with types depending on the parameters (but not the indices), and a list of values for the indices depending on values of the arguments.  As with fields, constructors are not constants and belong to a separate name domain, and since they are "dual" to fields they are indicated with a suffixed period instead of a prefixed one.  (This is in line with functional programming languages such as Haskell and OCaml, where constructors have a separate syntax, e.g. begin with a capital letter.)

Once a datatype is defined, the constructors can be used to build elements of it, by applying them like functions (with final period) to their arguments (but not the parameters or indices of the datatype).  This syntactic form *checks*, rather than synthesizing, against an instance of the datatype.  You can define another constant to equal an application of a constructor, however, and it will synthesize.

Datatypes can be inductive, with the arguments of constructors involving the datatype itself.

For example, currently there is an implementation of the natural numbers, which can be accessed by calling `Types.Nat.install ()`, with the general recursor/inductor, and also addition and multiplication constants defined by direct case trees rather than in terms of the recursor.  The latter have right-associative infix notations `+` and `*`, with `*` binding more tightly, and also numeral notations.  There are also implementations of sum types (with two type parameters), lists (with type parameter), and vectors (with type parameter and length index).

### Defined constants and case trees

Constants that are not records or datatypes can be axioms (undefined), or they can be stipulated to compute according to any *case tree*.  A case tree is composed of nested abstraction, pattern matches against constructors, and copattern comatches against fields, until it reaches a "leaf" which is an arbitrary term (in the context of the variables introduced so far by the abstractions and pattern matches).  A degenerate version of a case tree is just a leaf, which simply defines the constant to equal some given term.

The syntax for pattern matches is
```
match x with
| constr1. a b ↦ BRANCH1
| constr2. c d ↦ BRANCH2
end
```
Note that `x` must be a *free variable*: it is not possible to match against an arbitrary term (you can achieve that effect by defining an auxiliary constant).  The syntax for abstractions in case trees is the same as that for abstractions in terms, `x ↦ M`, and similarly the syntax for copattern matches in case trees is the same as that for anonymous structures in terms, `{ fld1 ≔ M; fld2 ≔ N }`.  (There is currently no analogue of `match` inside a term; pattern-matching can only be done in the case tree of a toplevel constant.)

This means that defining a constant to equal something like "`x y ↦ { fld1 ≔ M; fld2 ≔ N }`" appears ambiguous as to whether it is just a leaf or whether it is a case tree involving abstractions and perhaps a copattern match.  The rule to resolve this ambiguity is that *as much as possible of a definition is included in the case tree*.  This is usually what you want.

A constant defined by a case tree does not compute unless the tree can be followed all the way down to a leaf.  In particular, a match or comatch is never exposed as part of a term.  Moreover, this means that when defining a constant to equal a given term, by putting the abstractions into the case tree rather than the term we ensure that it must be applied to all its arguments in order to compute, rather than immediately evaluating to an abstraction.  Again, this is usually what you want.

As noted, case trees can include fields (copatterns) as well as matches against other constants (patterns).  Thus it is also possible to define constructors of records by case trees, in addition to as structures.  These have the advantage that they synthesize, but the disadvantage that they must be applied explicitly to all the parameters.  For example, Sigma-types also come with a `pair` constructor defined in this way; one can write `pair A B a b` instead of `{ fst ≔ a; snd ≔ b }` or `(a,b)`.

There is currently no parsing or typechecking for definitions of records and datatypes: the programmer is required and trusted to write them by hand in abstract syntax with De Bruijn indices.  In particular, there is no positivity checking.  There is also no termination or productivity checking for recursive and corecursive functions, although there is coverage checking: you can write infinite loops, but your programs shouldn't get stuck.

Note that case trees are the internal implementation of pattern-matching definitions, e.g. Agda compiles its definitions internally to case trees.  I believe it is better to expose the case tree to the user explicitly.  In some cases, this can make code more concise, since all the arguments of the function no longer have to be written again in every branch and sub-branch.  But more importantly, the order in which matches are performed, and hence the way in which the function actually computes, is this way obvious to the reader, and can be specified explicitly by the programmer, in particular eliminating the confusion surrounding Agda's `--exact-split` option.  So I have no plans to implement Agda-style pattern matching syntax.

There are other enhancements to matching that could be done, however.  One current limitation is that when matching against an indexed datatype, the indices must all be distinct free variables, as in the eliminator.  It would be possible to generalize away from this using a unification algorithm as in Agda-style `--without-K` matching.  It should also be possible to allow matches inside arbitrary terms by lifting them to toplevel and defining a new internal constant.  And it might be possible to implement a version of Coq/ML-style simultaneous matches like `match x, y with ...`, since the order of the variables indicates the order in which they are matched.


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

This applies also to corecursive record types, whose identity/bridge types are thus coinductive types of bisimulations.  Such bisimulations can be defined using corecursion, with a copattern-matching case tree.  (Note that anonymous structures can only construct bisimulations that become trivial after a finite number of steps, and since bisimulation types are *indexed* coinductive types it does not seem possible to formulate a generic corecursor for them by postulating a single typed constant with a case tree.  Thus nontrivial bisimulations require direct copattern-matching case trees.)

The identity/bridge type of a datatype is currently itself another datatype, with constructors applied at higher elements to construct their elements (with the boundary treated like indices).  Case trees are allowed internally to discriminate on them, but currently the user-facing syntax doesn't know how to typecheck such higher case trees.  It's also unclear whether they should be allowed, so this might change.

Internal parametricity is implemented by the constant `Gel`, defined with `Types.Gel.install ()`, whose type is
```
(A : Type) (B : Type) (R : (x:A) (y:B) → Type) → Id Type A B
```
As above, since `Gel A B R` is an identification in the universe, it can be further instantiated at elements `a : A` and `b : B` to obtain a type `Gel A B R a b`.  This type is isomorphic to the original `R a b`.  In fact, `Gel` is declared as a special kind of "one-dimensional record type" (in contrast to the usual zero-dimensional ones) with eta-conversion, with a single field `ungel` of type `R a b`.  Thus the isomorphism is implemented by, on the one hand, accessing this field `M .ungel`, and on the other by building a record `{ ungel ≔ M }`.  (The code actually allows for record types of arbitrary dimension, but in practice Gel is the only one expected to be needed.)


## Remarks on implementation

As is common for normalization-by-evaluation, the implementation uses De Bruijn *indices* for syntactic terms and De Bruijn *levels* for semantic values.  A little more unusually, however, the De Bruijn indices are intrinsically well-scoped.  This means that the type of terms is parametrized by the length of the context (as a type-level natural number, using GADTs), so that the OCaml compiler ensures *statically* that De Bruijn indices never go out of scope.  Other consistency checks are also ensured statically in a similar way, such as the matching of dimensions for certain types and operators.

This approach does have the drawback that it requires a fair amount of arithmetic on the natural numbers to ensure well-typedness, which is not only tedious but some of it also ends up happening at run-time.  Since type-level natural numbers are represented in unary, this could be a source of inefficiency in the future.
