# Narya

Narya is eventually intended to be a proof assistant implementing Multi-Modal, Multi-Parametric, Higher Observational Type Theory.  However, a formal type theory combining all those adjectives has not yet been specified.  At the moment, Narya implements a normalization-by-evaluation algorithm and typechecker for an observational-style theory with binary Id/Bridge types, with Gel types for internal parametricity as an option.  The alternative option of transport and univalence is not yet implemented, nor are any other modalities included.

Narya is very much a work in progress.  Expect breaking changes, including even in fundamental aspects of the syntax.  But on the other side of the coin, feedback on anything and everything is welcome.


## Compilation

Narya requires OCaml version 5.1.0 and various libraries, including currently a pre-release version of fmlib.

```
opam switch create 5.1.0
opam install zarith uuseg bwd algaeff asai yuujinchou react lwt lambda-term

git clone git@github.com:hbr/fmlib.git
cd fmlib
git checkout parse
opam install js_of_ocaml js_of_ocaml-ppx
dune build
dune install

cd ../narya
dune build @install
dune runtest
dune install
```

This will make the executable `narya` available in a directory such as `~/.opam/5.1.0/bin`, which should be in your `PATH`.  Alternatively, instead of `dune install` you can also run the executable directly with `dune exec bin/narya.exe`.  In this case, to pass arguments to the executable, put them after a `--`.  For instance, `dune exec bin/narya.exe -- test.ny -i` loads the file `test.ny` and then enters interactive mode.


## Parsing

The parser supports arbitrary mixfix operations with associativities and precedences, although at present these have to be defined using the OCaml interface.  We prefer to say "tightness" instead of "precedence", to make it clear that higher numbers bind more tightly.  Tightnesses are *dyadic rational numbers*, including ω and −ω that are reserved for internal use.  Notations can be either left-closed or left-open, and either right-closed or right-open, and tightness and associativity are only relevant on the open side(s).  An infix notation is one that is open on both sides; a prefix notation is closed on the left and open on the right; a postfix notation is open on the left and closed on the right; and a "closed" or "outfix" notation is closed on both sides.  The built-in notations are:

- `( M )` – Parentheses for grouping (a closed notation).
- `Type` – The unique universe (currently we have type-in-type).
- `M N` – Function application (left-associative).
- `x ↦ M` – Lambda-abstraction.  The unicode ↦ can be replaced by ASCII `|->`.
- `x y z ↦ M` – Iterated lambda-abstraction.
- `x ⤇ M` – Higher-dimensional lambda-abstraction (see below).
- `(x : M) → N` – Pi-type.  The unicode → can be replaced by ASCII `->`.
- `(x : M) (y z : N) (w : P) → Q` – Multivariable Pi-type.
- `M → N` – Non-dependent function-type (right-associative).
- `M .fld` – Field access of a record (left-associative).
- `( fld1 ≔ M, fld2 ≔ N )` – Anonymous record (structure).  The unicode ≔ can be replaced by ASCII `:=`.  Checks, doesn't synthesize.
- `( M, N )` – Record with unlabeled fields.  Labeled and unlabeled fields can also be mixed.
- `constr. M N` – Constructor of a datatype, applied to arguments (but not parameters).  Checks, doesn't synthesize.  The postfix period is admittedly unusual; the intent is to emphasize the duality between constructors of a datatype and destructors (fields) of a codatatype/record.
- `M : N` – Type ascription.  Necessary if you want to apply an abstraction to an argument (i.e. manually write a beta-redex) or similarly apply a field to a structure, since the typechecker is bidirectional.
- `let x ≔ M in N` – Local binding.  Computationally equivalent to `(x ↦ N) M`, but also binds `x` to `M` while typechecking `N`, which is stronger in the presence of dependent types.  As before, ≔ can be replaced by `:=`, and `let x ≔ (M : A) in N` (commonly needed since `M` must synthesize) can be abbreviated `let x : A ≔ M in N`.
- `[ x | constr1. a b ↦ M | constr2. c d ↦ N ]` – Match against datatype constructors.  Only valid in a top-level case tree when `x` is a variable (see below).  This syntax is tentative and might change if I get negative feedback from users.
- `[ constr1. a b ↦ M | constr2. c d ↦ N ]` – Abstract over a variable and immediately match against it, i.e. pattern-matching lambda.  Essentially a notational variant of `x ↦ [ x | constr1. a b ↦ M | constr2. c d ↦ N ]` without needing to choose a dummy name for the variable.  The initial `|` after the empty variable location can also be included.
- `[ .fld1 ↦ M | .fld2 ↦ N ]` – Copattern match against a codatatype.
- `Id M X Y` – Homogeneous identity/bridge type.  In fact this is equivalent to `refl M X Y`, and `Id` is just a synonym for `refl`.
- `refl M` – Reflexivity term.
- `sym M` – Symmetry of a two-dimensional square.
- `M ^{ 102 }` – General degeneracy (combination of higher reflexivities and symmetries).

Function application and field access can be thought of as left-associative infix operations with zero infix symbols and tightness +ω (although they are implemented specially internally).  In particular, a nonassociative prefix notation of tightness +ω, say `@`, will bind tighter than application, so that `@ f x` parses as `(@ f) x`.  There are no such notations currently, but future possibilities include explicification of implicit functions and universe lifting.

Abstraction, ascription, and let-bindings have tightness −ω, so they bind more loosely than anything except each other.  Type ascription is non-associative, so `M : N : P` is a parse error.  Abstraction and let-binding are right-associative, so that `x ↦ y ↦ M` parses correctly (though it can also be abbreviated as `x y ↦ M`).  In particular, this means that `x ↦ M : A` parses as `x ↦ (M : A)`, and similarly `let x ≔ M in N : A` parses as `let x ≔ M in (N : A)`.  Pi-types and function-types have tightness 0, and are right-associative.

The coexistence of type ascription and NuPRL/Agda-style dependent function-types leads to a potential ambiguity: `(x : A) → B` could be a dependent function type, but it could also be a *non-dependent* function type whose domain `x` is ascribed to type `A`.  Narya resolves this in favor of the dependent function type, which is nearly always what is intended; if you really mean the other you can write it as `((x : A)) → B` or `((x) : A) → B`.

A line comment starts with a backquote \` and extends to the end of the line.  A block comment starts with {\` and ends with \`}.  Block comments can be nested.

As in Agda, mixfix notations can involve arbitrary Unicode characters (a source file is expected to be UTF-8), most of which must be surrounded by spaces to prevent them from being interpreted as part of an identifier.  However, in Narya this has the following exceptions:

- The characters `( ) [ ] { } → ↦ ⤇ ≔ ⩴ ⩲ …`, which either have built-in meaning or are reserved for future built-in meanings, are always treated as single tokens.  Thus, they do not need to be surrounded by whitespace.  This is the case for parentheses and braces in Agda, but the others are different: in Narya you can write `A→B` without spaces.  The non-ASCII characters in this group all have ASCII-sequence substitutes that are completely interchangeable: `-> |-> |=> := ::= += ...`.
- A nonempty string consisting of the characters `~ ! @ # $ % ^ & * / ? = + \ | , < > : ; -` is always treated as a single token, and does not need to be surrounded by whitespace.  Note that this is most of the non-alphanumeric characters that appear on a standard US keyboard except for parentheses (grouping), curly braces (structures and, later, implicit arguments), backquote (comments), period (fields, constructors, and namespaces), underscore (allowed in identifiers, and for unnamed variables and, later, inferred arguments), double quote (later, string literals) and single quote (allowed in identifiers, for primes on variable names).  In particular:
  - Ordinary algebraic operations like `+` and `*` can be defined so that `x+y` and `x*y` are valid.
  - This includes the colon, so you can write `(x:A) → B`, and similarly for the comma `,` in a record and the bar `|` in a match or comatch.  But the user can also use these characters in other operators, such as `::` for list cons.  (Or you can use the Unicode ∷ and require spacing around it.)
  - The ASCII substitutes for the single-token Unicode characters also fall into this category, so you can write for instance `A->B`.
  - The ASCII hyphen `-` is in this category; in addition to its being part of `->` and `|->`, this allows a subtraction operator `x-y` to be written without spaces.  (Note, though, that the current parser does not permit a binary subtraction to coexist with a unary negation using the same character.)  Therefore, unlike in Agda, the hyphen is not allowed in identifiers.

  This rule is intended to be a compromise, allowing the user to define plenty of infix operators that don't require spacing but also arbitrary unicode operators, while keeping the lexer rules simple and unchanging as new operators are defined.  If it turns out to be too unintuitive, it may be changed.

Numerals are strings consisting of digits, possibly containing a period but *not* starting or ending with one.  You must write `0.5` rather than `.5`, since the latter could be mistaken for a field projection.  (Although currently only natural number numerals are implemented.)  Identifiers (variables and constant names) can be any other string of non-whitespace characters that does not start or end with a period or an underscore.  (In particular, identifiers may start with a digit.)  Field names, which must be identifiers, are prefixed a period when accessed, and dually constructor names are postfixed a period when applied.  Internal periods in identifiers denote namespace qualifiers on constants; thus they cannot appear in local variable names, field names, or constructor names, none of which are namespaced.

## Files and commands

A Narya file is a sequence of commands.  Conventionally each command begins on a new line, but this is not technically necessary since each command begins with a keyword that has no other meaning.  Indentation is not significant, but a standard reformatter (like `ocamlformat`) is planned so that the default will be to enforce a uniform indentation style.  So far, the available commands are:

1. `def NAME : TYPE ≔ TERM` – Define a global constant called `NAME` having type `TYPE` and value `TERM`.  Thus `NAME` must be a valid identifier, while `TYPE` must parse and typecheck at type `Type`, and `TERM` must parse and typecheck at type `TYPE`.  In addition, `TERM` can be a case tree (see below).

2. `axiom NAME : TYPE` – Assert a global constant called `NAME` having type `TYPE`, without any definition (an axiom).

3. `echo TERM` – Normalize `TERM` and print its value to standard output.  Note that `TERM` must synthesize a type; if it is a checking term you must ascribe it. 

When the Narya executable is run, it executes all the files given on its command line, in order.  As usual, the special filename `-` refers to standard input.  It then executes any strings supplied on the command line with `-e`.  Finally, if `-i` was given, it enters interactive mode.

## Interactive mode

In interactive mode, commands typed by the user are executed as they are entered.  Since many commands span multiple lines, Narya waits for a blank line before parsing and executing the command(s) being entered.  The result of the commands is printed (more verbosely than is usual when loading a file) and then the user can enter more commands.  Type Control+D to exit.

In addition, in interactive mode you can enter a term instead of a command, and Narya will assume you mean to `echo` it.

## Records, datatypes, and codatatypes

The three basic families of "canonical" types are records, datatypes, and codatatypes.  When a type family is declared, instead of being defined or assumed as an axiom it can be given a definition as one of these three kinds of type.  (Currently, this is only possible with direct OCaml coding, not yet by commands in an ordinary file.  The programmer is thus required and trusted to write these definitions by hand in abstract syntax with De Bruijn indices.)

### Record types and tuples

A constant that is a type family can be declared to be a *record type*, by giving a list of its fields with their types.  The fields themselves are *not* constants; they belong to a separate name domain.  (They can be thought of as analogous to "methods" in an object-oriented programming language.)  Then an element of an instance of that family can have its fields projected out with the postfix syntax `M .fld`.  For instance, Σ-types are implemented as a record: the type `Σ A B`, also written `(x : A) × B x`, has two fields `fst : A` and `snd : B fst`.  The unicode × can be replaced by the ASCII `><`, and in the non-dependent case we can write `A × B` or `A >< B`.

Elements of a record type (i.e. records) are constructed as tuples, inside parentheses and with field values separated by commas.  The elements of a tuple can be either unlabeled, as in `(a,b)`, or labeled, as in the equivalent `( fst ≔ a, snd ≔ b)`.  Note that the labels in a tuple omit the initial period in a field name.  In the unlabeled case, the values are assigned to fields in the order they were declared in the record, while in the labeled case they can be given in any order, e.g. `( snd ≔ b, fst ≔ a)` is equivalent to `( fst ≔ a, snd ≔ b)`.  It is also possible to label some values and not others; in this case the unlabeled values are assigned to the fields of the record type that don't have a labeled value, in the order they were declared in the record.  For instance, `(a,b)` can also be written as `( fst ≔ a, b)`, `( a, snd ≔ b)`, or even `( snd ≔ b, a)`.

Tuples are an "outfix" notation that includes the parentheses, rather than an infix meaning of the comma; thus the parentheses are always required.  Tuples are not associative: neither `(a, (b, c))` nor `((a, b), c)` can be written as `(a,b,c)`.  The latter is applicable only to a record type with three fields, whereas the former two apply to a record type with two fields, one of which is itself a record type with two fields.

A record type can have zero fields, yielding a unit type.  Its unique element is thus written `()`.  A record type can also have exactly one field, in which case it is isomorphic to the type of that field.  However, the element of a 1-tuple must be labeled, since an unlabeled 1-tuple `(a)` would look just like `a` inside ordinary parentheses.

Tuples are checking, not synthesizing: the same term `(a,b)` can check at many different record types.  Since the argument of a field projection is synthesizing, this means that a tuple must be ascribed in order to immediately project out a field: `(a,b) .fst` doesn't typecheck, but `((a,b) : A × B) .fst` does.  Note in particular that different record types can share the same field names, so from `x .fst` or `(fst ≔ a, snd ≔ b)` the typechecker can't even guess what record type family we are talking about without knowing the type of `x`, in the first case, or the type being checked at, in the second case.

Record types satisfy eta-conversion, meaning that two elements of the type are equal if all their fields are equal, even if they are not both syntactically tuples.

### Datatypes and pattern-matching

A constant that is a type family can also be declared to be a *datatype*, by giving a list of its constructors with their types.  Like fields, constructors belong to a separate name domain, and they are always written with an ending period.  (This use of a separate syntax can be compared with functional programming languages such as Haskell and OCaml, where datatype constructors also have a separate syntax — beginning with a capital letter is common.)  The type of each constructor must be a function-type whose codomain is an instance of the datatype, and whose domain can involve instances of the datatype itself.  The latter occurrences ought to be strictly positive, but currently there is no check for that.

The arguments of a datatype family are divided into parameters and indices, the difference being that the output of each constructor must be fully general in the parameters.  (This includes the case of so-called "non-uniform parameters" for which the recursive *inputs* need not be fully general.)  Accordingly, when constructors are applied like functions to their arguments, we omit the parameters; instead the typechecker takes the parameters from the type at which the constructor is being checked.  For example, a sum-type `sum A B` contains elements `inl. a` and `inr. b`, where we don't write `A` and `B` as arguments of the constructors since they are parameters.  Note that this means constructors don't synthesize: from `inl. a` the typechecker can't guess what the type `B` should be unless it is ascribed or in a context where the type is known.  (In fact it's even worse than that: because all constructors inhabit the same flat name domain, and different datatypes can have constructors with the same name, the typechecker can't even guess what datatype family `inl. a` should belong to.)

Definitions of datatypes currently available in the library include an empty type, binary sum-types, natural numbers, lists, and length-indexed vectors.  Natural number numerals are parsed automatically into applications of the natural number constructors `zero.` and `suc.`; this also means they can automatically also be typechecked at any other datatype having constructors with those names.

When a new constant is defined as a function containing datatypes in its domain, it can pattern-match on such an argument.  For instance, a function of a variable `x` of type `sum A B` can be defined as `[ x | inl. a ↦ M | inr. b ↦ N ]`, where `a:A` and `b:B` are new variables bound in `M` and `N` respectively.  At present, at least, it is only possible to match on a variable argument of the function, not on an arbitrary term; this allows the output type of the function to be refined in each branch without additional annotations.  It is also only possible to match on one argument at a time; but each branch of the match can proceed to match again on a different argument, or on one of the pattern variables (arguments of the constructor).  When matching against a datatype with indices, the indices in the type of the match variable must currently also be distinct free variables (this is even less general than Agda's `--without-K` matching and hence also ensures consistency with univalence).  Finally, a function defined by pattern-matching can also be recursive, calling itself on smaller arguments in each branch.

(Actually, currently there is no termination-checking, so the arguments don't even have to be smaller.  But there is coverage-checking: all the constructors of a datatype must be present in the match.  So you can write infinite loops, but your programs shouldn't get stuck.)

### Codatatypes and copattern-matching

A *codatatype* is superficially similar to a record type: it has a list of fields (which in this case we sometimes call *methods*), each with a type, which are projected out using the same syntax `x .fld`.  The primary differences are:

1. Codatatypes can be (co)recursive: the output type of each method can involve the codatatype itself.  (Such occurrences ought to be strictly positive, but currently there is no check for that.)
2. Codatatypes do not satisfy eta-conversion (this being undecidable in the recursive case).
3. Elements of codatatypes are defined by copattern-matching rather than with tuples.

Copattern-matching is similar to tupling, but the syntax is different (more like pattern-matching); all the methods must be labeled, including their initial periods; and a constant defined by copattern-matching can be corecursive, referring to itself in the (co)branches.  As an example, the type `Stream A` (where `A` is a parameter) has two methods, `head` of type `A`, and `tail` of type `Stream A`.  The infinite stream `nats n` of all natural numbers starting at `n` can then be defined by copattern-matching as `[ .head ↦ n | .tail ↦ nats (suc. n) ]`.

### Case trees

Tuples can occur anywhere in a term, but pattern-matches and copattern-matches can (currently) only occur at a top level definition of a constant.  However, all three (as well as lambda-abstractions) can be arbitrarily deeply nested in a top-level definition: we can start with a pattern-match, then in one branch (where the output type is a codatatype) proceed to a copattern-match, while another branch proceeds to match on a different argument belonging to another datatype, and so on.  This is called a *case tree*: it is composed of nested abstractions, tuples, pattern matches against constructors, and copattern comatches against fields, until it reaches a "leaf" which is an arbitrary term (in the context of the variables introduced so far by the abstractions and pattern matches).  A degenerate version of a case tree is just a leaf, which simply defines the constant to equal some given term.

This means that defining a constant to equal something like "`x y ↦ ( fld1 ≔ M, fld2 ≔ N )`" appears ambiguous as to whether it is just a leaf or whether it is a case tree involving abstractions and a tuple.  The rule to resolve this ambiguity is that *as much as possible of a definition is included in the case tree*.  This is usually what you want.

A constant defined by a case tree does not compute unless the tree can be followed all the way down to a leaf.  In particular, a match or comatch is never exposed as part of a term.  Moreover, this means that when defining a constant to equal a given term, by putting the abstractions into the case tree rather than the term we ensure that it must be applied to all its arguments in order to compute, rather than immediately evaluating to an abstraction.  Again, this is usually what you want.

As noted, case trees can include tuples as well as matches and comatches.  Thus it is also possible to define constructors of records by case trees, in addition to as tuples.  These have the advantage that they synthesize, but the disadvantage that they must be applied explicitly to all the parameters.  For example, Sigma-types also come with a `pair` constructor defined in this way; one can write `pair A B a b` instead of `( fst ≔ a, snd ≔ b ) : Σ A B` or `(a,b) : Σ A B`.

Note that case trees are generally considered the internal implementation of pattern-matching definitions, e.g. Agda compiles its definitions internally to case trees.  I believe it is better to expose the case tree to the user explicitly.  In some cases, this can make code more concise, since all the arguments of the function no longer have to be written again in every branch and sub-branch.  But more importantly, the order in which matches are performed, and hence the way in which the function actually computes, is this way obvious to the reader, and can be specified explicitly by the programmer, in particular eliminating the confusion surrounding Agda's `--exact-split` option.  So I have no plans to implement Agda-style pattern matching syntax.

There are other enhancements to matching that could be done, however, such as implementing something closer to Agda's `--without-K` unification-based matching.  It should also be possible to allow matches inside arbitrary terms by lifting them to toplevel and defining a new internal constant.  And it might be possible to implement a version of Coq/ML-style simultaneous matches like `match x, y with ...`, since the order of the variables indicates the order in which they are matched.  Similarly, some kind of deep matching such as `[ zero. ↦ ... | suc. zero. ↦ ... | suc. (suc. n) ↦ ... ]` may be possible.


## Parametric Observational Type Theory

Every type `A` has a binary identity/bridge type denoted `Id A x y`, and each term `x:A` has a reflexivity term `refl x : Id A x x`.  (The argument of `refl` must synthesize.)  Elements of the identity type of the universe include, at least, a binary correspondence, which is instantiated by application syntax; so from `A₂ : Id Type A₀ A₁`, if `a₀:A₀` and `a₁:A₁` we have `A₂ a₀ a₁ : Type`.  In particular, `Id A x y` is an instance of this syntax, as we have `Id A : Id Type A A`, and indeed `Id A` is just a notational variant of `refl A`.

Iterating `Id` or `refl` multiple times produces higher-dimensional cube types and cubes.  There is a symmetry operation `sym` that acts on at-least-two dimensional cubes, swapping or transposing the last two dimensions; its argument must also synthesize.  Combining versions of `refl` and `sym` yields arbitrary higher-dimensional "degeneracies" (from the BCH cube category).  There is also a generic syntax for such degeneracies: `M ^{ 201 }` where inside the braces is a string of digits representing the degeneracy, with `0` denoting a degenerate dimension and the other digits denoting a permutation.

The identity/bridge type of a pi-type computes to another pi-type.  In Narya this computation is "up to definitional isomorphism", meaning that the following two types are isomorphic:
```
id ((x:A) → B) f g
(x₀ : A) (x₁ : A) (x₂ : id A x₀ x₁) → id B (f x₀) (g x₁)
```
However, in most cases we can pretend that these two types are literally the same, because the typechecker allows lambda-abstractions matching the structure of the second to also typecheck at the first, and likewise elements of the first can be applied to arguments as if they were functions belonging to the second.

There is no unifier yet, so such an abstraction or application must include both endpoints `x₀` and `x₁` explicitly as well as the identity `x₂`.  However, there is a shorthand syntax for such higher-dimensional abstractions: instead of `x₀ x₁ x₂ ↦ M` you can write `x ⤇ M` (or `x |=> M` in ASCII).  This binds `x` as a "family" or "cube" of variables whose names are suffixed with face names in ternary notation: `x.0` and `x.1` and `x.2`, or in higher dimensions `x.00` through `x.22` and so on.  (The dimension is inferred from the type at which the abstraction is checked.)  Note that this is a *purely syntactic* abbreviation: there is no object "`x`", but rather there are really *three different variables* that just happen to have the names `x.0` and `x.1` and `x.2`.  (There is no potential for collision with user-defined names, since ordinary local variable names cannot contain internal periods.)

There is no primitive `ap`; instead it is accessed by applying `refl` to a function.  That is, if `f : (x:A) → B`, then `refl f x₀ x₁ x₂` relates `f x₀` to `f x₁` in `B`.  Likewise, identity types can be obtained by applying `refl` to a type: `Id M X Y` is just a convenient abbreviation of `refl M X Y`.

Heterogeneous identity/bridge types are similarly obtained from `refl` of a type family: if `B : A → Type`, then `refl B x₀ x₁ x₂` is a identification/bridge in `Type` between `B x₀` and `B x₁`.  Given elements `y₀ : B x₀` and `y₁ : B x₁`, we can "instantiate" this identification at them to obtain a type of heterogeneous identifications.  This is also written as function application, `refl B x₀ x₁ x₂ y₀ y₁`.

The identity/bridge type of a record type is another record type, which uses the same field names as the original.  For instance, `Id ((x:A) × B) X Y` is a record type with fields `fst` and `snd`, where for `s : Id ((x:A) × B) X Y` we have
```
s .fst  :  Id A (X .fst) (Y .fst)
s .snd  :  refl B (X .fst) (Y .fst) (s .fst) (X .snd) (Y .snd)
```
Since it also satisfies eta-conversion, this record is definitionally isomorphic (but not equal) to another Sigma-type
```
(p : Id A (X .fst) (Y .fst)) × refl B (X .fst) (Y .fst) p (X .snd) (Y .snd)
```
Similarly to the case with function-types, since the fields of `Id ((x:A) × B) X Y` are again named `fst` and `snd`, in most cases one can pretend it is actually equal to the latter Sigma-type, including constructing elements of it with `( fst ≔ P, snd ≔ Q )`.

Codatatypes behave similarly: their identity/bridge types are thus coinductive types of bisimulations.  Such bisimulations can be defined using corecursion, with a copattern-matching case tree.

The identity/bridge type of a datatype is itself another datatype, with constructors of the same name applied to higher-dimensional elements to construct their elements (with the boundary treated like indices).  Case trees are also allowed to match on these higher constructors, binding "cubes" of variables as above.

Internal parametricity is implemented by the constant `Gel`, defined with `Types.Gel.install ()`, whose type is
```
(A : Type) (B : Type) (R : (x:A) (y:B) → Type) → Id Type A B
```
As above, since `Gel A B R` is an identification in the universe, it can be further instantiated at elements `a : A` and `b : B` to obtain a type `Gel A B R a b`.  This type is isomorphic to the original `R a b`.  In fact, `Gel` is declared as a special kind of "one-dimensional record type" (in contrast to the usual zero-dimensional ones) with eta-conversion, with a single field `ungel` of type `R a b`.  Thus the isomorphism is implemented by, on the one hand, accessing this field `M .ungel`, and on the other by building a record `( ungel ≔ M )`.  (The code actually allows for record types of arbitrary dimension, but in practice Gel is the only one expected to be needed.)


## Remarks on implementation

As is common for normalization-by-evaluation, the implementation uses De Bruijn *indices* for syntactic terms and De Bruijn *levels* for semantic values.  A little more unusually, however, the De Bruijn indices are "intrinsically well-scoped".  This means that the type of terms is parametrized by the length of the context (as a type-level natural number, using GADTs), so that the OCaml compiler ensures *statically* that De Bruijn indices never go out of scope.  Other consistency checks are also ensured statically in a similar way, such as the matching of dimensions for certain types and operators, and scoping and associativity for notations.  (The latter is the reason why tightnesses are dyadic rationals: they are represented internally as type-level finite surreal-number sign-sequences, this being a convenient way to inductively define a dense linear order.)

This approach does have the drawback that it requires a fair amount of arithmetic on the natural numbers to ensure well-typedness, which is not only tedious but some of it also ends up happening at run-time.  Since type-level natural numbers are represented in unary, this could be a source of inefficiency in the future.  However, it has so far proven very effective at avoiding bugs!
