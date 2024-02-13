# Narya

Narya is eventually intended to be a proof assistant implementing Multi-Modal, Multi-Parametric, Higher Observational Type Theory.  However, a formal type theory combining all those adjectives has not yet been specified.  At the moment, Narya implements a normalization-by-evaluation algorithm and typechecker for an observational-style theory with binary Id/Bridge types, with Gel types for internal parametricity as an option.  The alternative option of transport and univalence is not yet implemented, nor are any other modalities included.

Narya is very much a work in progress.  Expect breaking changes, including even in fundamental aspects of the syntax.  But on the other side of the coin, feedback on anything and everything is welcome.


## Compilation

Narya requires OCaml version 5.1.0 (or later) and various libraries.

```
opam switch create 5.1.0
opam install zarith uuseg bwd algaeff asai yuujinchou react lwt lambda-term fmlib

cd ../narya
dune build @install
dune runtest
dune install
```

This will make the executable `narya` available in a directory such as `~/.opam/5.1.0/bin`, which should be in your `PATH`.  Alternatively, instead of `dune install` you can also run the executable directly with `dune exec narya`.  In this case, to pass arguments to the executable, put them after a `--`.  For instance, `dune exec narya -- test.ny -i` loads the file `test.ny` and then enters interactive mode.


## Parsing

The parser supports arbitrary mixfix operations with associativities and precedences.  We prefer to say "tightness" instead of "precedence", to make it clear that higher numbers bind more tightly.  Tightnesses are *dyadic rational numbers*, including ω and −ω that are reserved for internal use.  Notations can be either left-closed or left-open, and either right-closed or right-open, and tightness and associativity are only relevant on the open side(s).  An infix notation is one that is open on both sides; a prefix notation is closed on the left and open on the right; a postfix notation is open on the left and closed on the right; and a "closed" or "outfix" notation is closed on both sides, and has no tightness.  The built-in notations are:

- `( M )` – Parentheses for grouping (outfix).
- `Type` – The unique universe (currently we have type-in-type).
- `M N` – Function application (left-associative).
- `x ↦ M` – Lambda-abstraction.  The unicode ↦ can be replaced by ASCII `|->`.
- `x y z ↦ M` – Iterated lambda-abstraction.
- `x ⤇ M` – Higher-dimensional lambda-abstraction (see below).
- `(x : M) → N` – Pi-type.  The unicode → can be replaced by ASCII `->`.
- `(x : M) (y z : N) (w : P) → Q` – Multivariable Pi-type.
- `M → N` – Non-dependent function-type (right-associative).
- `M .fld` – Field access of a record (left-associative), or method call on a codatatype.
- `(fld1 ≔ M, fld2 ≔ N)` – Anonymous record (structure).  The unicode ≔ can be replaced by ASCII `:=`.  Checks, doesn't synthesize.
- `(M, N)` – Record with unlabeled fields.  Labeled and unlabeled fields can also be mixed (see below).
- `constr. M N` – Constructor of a datatype, applied to arguments (but not parameters).  Checks, doesn't synthesize.  The postfix period is admittedly unusual; the intent is to emphasize the duality between constructors of a datatype and destructors (fields) of a codatatype/record.
- `M : N` – Type ascription.  Necessary if you want to apply an abstraction to an argument (i.e. manually write a beta-redex) or similarly access a field of a tuple, since the typechecker is bidirectional.
- `let x ≔ M in N` – Local binding.  Computationally equivalent to `(x ↦ N) M`, but also binds `x` to `M` while typechecking `N`, which is stronger in the presence of dependent types.  As before, ≔ can be replaced by `:=`, and `let x ≔ (M : A) in N` (commonly needed since `M` must synthesize) can be abbreviated `let x : A ≔ M in N`.
- `[ x | constr1. a b ↦ M | constr2. c d ↦ N ]` – Match against datatype constructors.  Only valid in a top-level case tree when `x` is a variable (see below).  This syntax is tentative and might change if we get negative feedback from users.
- `[ constr1. a b ↦ M | constr2. c d ↦ N ]` – Abstract over a variable and immediately match against it, i.e. pattern-matching lambda.  Essentially a notational variant of `x ↦ [ x | constr1. a b ↦ M | constr2. c d ↦ N ]` without needing to choose a dummy name for the variable.  The initial `|` after the empty variable location can also be included.
- `[ .fld1 ↦ M | .fld2 ↦ N ]` – Copattern match against a codatatype.
- `"string"` – Quoted string.  Currently only used when specifying new notations.
- `Id M X Y` – Homogeneous identity/bridge type.  In fact this is equivalent to `refl M X Y`, and `Id` is just a synonym for `refl`.
- `refl M` – Reflexivity term.
- `sym M` – Symmetry of a two-dimensional square.
- `M⁽¹⁰²⁾` – General degeneracy (combination of higher reflexivities and symmetries).  Can also be written `M^(102)`.

Function application and field access can be thought of as left-associative infix operations with zero infix symbols and tightness +ω (although they are implemented specially internally).  In particular, a nonassociative prefix notation of tightness +ω, say `@`, will bind tighter than application, so that `@ f x` parses as `(@ f) x`.  There are no such notations currently, but future possibilities include explicification of implicit functions and universe lifting.

Abstraction, ascription, and let-bindings have tightness −ω, so they bind more loosely than anything except each other.  Type ascription is non-associative, so `M : N : P` is a parse error.  Abstraction and let-binding are right-associative, so that `x ↦ y ↦ M` parses correctly (though it can also be abbreviated as `x y ↦ M`).  In particular, this means that `x ↦ M : A` parses as `x ↦ (M : A)`, and similarly `let x ≔ M in N : A` parses as `let x ≔ M in (N : A)`.  Pi-types and function-types have tightness 0, and are right-associative.

The coexistence of type ascription and NuPRL/Agda-style dependent function-types leads to a potential ambiguity: `(x : A) → B` could be a dependent function type, but it could also be a *non-dependent* function type whose domain `x` is ascribed to type `A` (which would therefore have to be a type universe).  Narya resolves this in favor of the dependent function type, which is nearly always what is intended.  If you really mean the other you can write it as `((x : A)) → B` or `((x) : A) → B`, but you should never need to do this since the only possible ambiguity is when `x` is a variable (or a list of variables), and variables and constants (and application spines of such) always synthesize their type anyway and thus don't need to be ascribed.

A line comment starts with a backquote \` and extends to the end of the line.  A block comment starts with {\` and ends with \`}.  Block comments can be nested.

As in Agda, mixfix notations can involve arbitrary Unicode characters (a source file is expected to be UTF-8), most of which must be surrounded by spaces to prevent them from being interpreted as part of an identifier.  However, in Narya this has the following exceptions:

- The characters `( ) [ ] { } → ↦ ⤇ ≔ ⩴ ⩲ …`, which either have built-in meaning or are reserved for future built-in meanings, are always treated as single tokens.  Thus, they do not need to be surrounded by whitespace.  This is the case for parentheses and braces in Agda, but the others are different: in Narya you can write `A→B` without spaces.  The non-ASCII characters in this group all have ASCII-sequence substitutes that are completely interchangeable: `-> |-> |=> := ::= += ...`.
- A nonempty string consisting of the characters `~ ! @ # $ % & * / ? = + \ | , < > : ; -` is always treated as a single token, and does not need to be surrounded by whitespace.  Note that this is most of the non-alphanumeric characters that appear on a standard US keyboard except for parentheses (grouping), curly braces (structures and, later, implicit arguments), backquote (comments), period (fields, constructors, and namespaces), underscore (allowed in identifiers, and for unnamed variables and, later, inferred arguments), double quote (later, string literals) and single quote (allowed in identifiers, for primes on variable names).  In particular:
  - Ordinary algebraic operations like `+` and `*` can be defined so that `x+y` and `x*y` are valid.
  - This includes the colon, so you can write `(x:A) → B`, and similarly for the comma `,` in a record and the bar `|` in a match or comatch.  But the user can also use these characters in other operators, such as `::` for list cons.  (Or you can use the Unicode ∷ and require spacing around it.)
  - The ASCII substitutes for the single-token Unicode characters also fall into this category, so you can write for instance `A->B`.
  - The ASCII hyphen `-` is in this category; in addition to its being part of `->` and `|->`, this allows a subtraction operator `x-y` to be written without spaces.  (Note, though, that the current parser does not permit a binary subtraction to coexist with a unary negation using the same character.)  Therefore, unlike in Agda, the hyphen is not allowed in identifiers.

  This rule is intended to be a compromise, allowing the user to define plenty of infix operators that don't require spacing but also arbitrary unicode operators, while keeping the lexer rules simple and unchanging as new operators are defined.  If it turns out to be too unintuitive, it may be changed.

- A nonempty string consisting of the Unicode superscript symbols `ᵃᵇᶜᵈᵉᶠᵍʰⁱʲᵏˡᵐⁿᵒᵖ𐞥ʳˢᵗᵘᵛʷˣʸᶻ⁽⁰¹²³⁴⁵⁶⁷⁸⁹⁾⁺⁻⁼` is treated as a single token and applied as a "superscript" operator to whatever immediately precedes it, binding more tightly than anything (tightness of "ω+1").  At present the only meaning of this is generic degeneracies (see below).  In addition, a caret `^` followed by a nonempty string of the corresponding ASCII characters `abcdefghijklmnopqrstuvwxyz(0123456789)+-=` (no internal spaces!) has exactly the same meaning.


Identifiers (variables and constant names) can be any string of non-whitespace characters, other than the ASCII operators and superscript characters listed above, that does not start or end with a period or an underscore.  In particular, identifiers may start with a digit, or even consist entirely of digits (thereby shadowing a numeral notation).  Field names, which must be identifiers, are prefixed a period when accessed, and dually constructor names are postfixed a period when applied.  Internal periods in identifiers denote namespace qualifiers on constants; thus they cannot appear in local variable names, field names, or constructor names, none of which are namespaced.

Numerals are strings consisting of digits, possibly containing a period but *not* starting or ending with one.  You must write `0.5` rather than `.5`, since the latter could be mistaken for a field projection.  Currently, only natural number numerals are implemented, and are parsed into applications of the constructors `suc` and `zero`, e.g. `3` becomes `suc. (suc. (suc. zero.))`.  They therefore typecheck (but don't synthesize) at any datatype (see below) having a nullary constructor `zero` and a unary recursive constructor `suc`, including of course the usual natural numbers.

Similarly, the forwards list notation `[> 1, 2, 3 >]` is automatically parsed as `cons. 1 (cons. 2 (cons. 3 nil.))`, while the backwards list notation `[< 1, 2, 3 <]` is parsed as `snoc. (snoc. (snoc. emp. 1) 2) 3`.  Thus, the first typechecks at any datatype having suitably typed constructors `nil` and `cons`, while the latter typechecks at any datatype having suitably typed constructors `emp` and `snoc`.  Of course, these include the usual types of forwards and backwards lists respectively.  (Since `[` and `]` are always their own tokens, it is also possible to put spaces in it like `[ > 1, 2, 3 > ]`, but this is not recommended.)  The infix binary operators `:>` and `<:` are also bound to `cons` and `snoc`, respectively, the first right-associative and the latter left-associative; thus `[> 1, 2, 3 >]` is also `1 :> 2 :> 3:> nil.`, and `[< 1, 2, 3 <]` is also `emp. <: 1 <: 2 <: 3`.

## Files and commands

A Narya file is a sequence of commands.  Conventionally each command begins on a new line, but this is not technically necessary since each command begins with a keyword that has no other meaning.  Indentation is not significant, but a standard reformatter (like `ocamlformat`) is planned so that the default will be to enforce a uniform indentation style.  So far, the available commands are:

1. `def NAME : TYPE ≔ TERM`

   Define a global constant called `NAME` having type `TYPE` and value `TERM`.  Thus `NAME` must be a valid identifier, while `TYPE` must parse and typecheck at type `Type`, and `TERM` must parse and typecheck at type `TYPE`.  In addition, `TERM` can be a case tree (see below).

2. `axiom NAME : TYPE`

   Assert a global constant called `NAME` having type `TYPE`, without any definition (an axiom).

3. `echo TERM`

   Normalize `TERM` and print its value to standard output.  Note that `TERM` must synthesize a type; if it is a checking term you must ascribe it. 

4. `notation [TIGHTNESS] NAME : […] PATTERN […] ≔ HEAD ARGUMENTS`

   Declare a new mixfix notation.  The `TIGHTNESS` must be a finite dyadic rational number, written in decimal notation; it must be present for infix, prefix, and postfix notations, and absent for outfix notations (those that both start and end with a symbol).  Every notation must then have a `NAME`, which is an identifier like the name of a constant and is entered in the global namespace as `notation.NAME`; this is used to identify it in error messages, and will eventually be used for importing and exporting notations.

   The `PATTERN` of a notation is a list of interspersed distinct local variable names and double-quoted symbols, such as `x "+" y` for addition or `Γ "⊢" x "⦂" A` for a typing judgment.  Each quoted symbol must be exactly one token; any two variables must be separated by a symbol (but two symbols can follow each other without a variable in between); and there must be at least one symbol.  If a pattern starts with a variable, it may be preceded by an ellipsis, indicating that it is left-associative; and dually if it ends with a variable, it may be followed by an ellipsis, indicating that it is right-associative (but not both).
   
   The value of a notation consists of a `HEAD`, which is either a previously defined constant or a constructor, followed by the `ARGUMENTS` that must consist of exactly the variables appearing in the pattern, in some order.  This restriction ensures that the notation can be used for printing as well as parsing; in the future it may be relaxed.

When the Narya executable is run, it executes all the files given on its command line, in order.  As usual, the special filename `-` refers to standard input.  It then executes any strings supplied on the command line with `-e`.  Finally, if `-i` was given, it enters interactive mode.

## Interactive mode

In interactive mode, commands typed by the user are executed as they are entered.  Since many commands span multiple lines, Narya waits for a blank line before parsing and executing the command(s) being entered.  The result of the commands is printed (more verbosely than is usual when loading a file) and then the user can enter more commands.  Type Control+D to exit.

In addition, in interactive mode you can enter a term instead of a command, and Narya will assume you mean to `echo` it.

## Records, datatypes, and codatatypes

The three basic families of "canonical" types are records, datatypes, and codatatypes.  When a type family is declared, instead of being defined or assumed as an axiom it can be given a definition as one of these three kinds of type.  (Currently, this is only possible with direct OCaml coding, not yet by commands in an ordinary file.  The programmer is thus required and trusted to write these definitions by hand in abstract syntax with De Bruijn indices.)

### Record types and tuples

A constant that is a type family can be declared to be a *record type*, by giving a list of its fields with their types.  The fields themselves are *not* constants; they belong to a separate name domain.  (They can be thought of as analogous to "methods" in an object-oriented programming language.)  Then an element of an instance of that family can have its fields projected out with the postfix syntax `M .fld`.  For instance, Σ-types are implemented as a record: the type `Σ A B`, also written `(x : A) × B x`, has two fields `fst : A` and `snd : B fst`.  The unicode × can be replaced by the ASCII `><`, and in the non-dependent case we can write `A × B` or `A >< B`.

Elements of a record type (i.e. records) are constructed as tuples, inside parentheses and with field values separated by commas.  The elements of a tuple can be either unlabeled, as in `(a,b)`, or labeled, as in the equivalent `(fst ≔ a, snd ≔ b)`.  Note that the labels in a tuple omit the initial period in a field name.  In the unlabeled case, the values are assigned to fields in the order they were declared in the record, while in the labeled case they can be given in any order, e.g. `(snd ≔ b, fst ≔ a)` is equivalent to `(fst ≔ a, snd ≔ b)`.  It is also possible to label some values and not others; in this case the unlabeled values are assigned to the fields of the record type that don't have a labeled value, in the order they were declared in the record.  For instance, `(a,b)` can also be written as `(fst ≔ a, b)`, `(a, snd ≔ b)`, or even `(snd ≔ b, a)`.  An field labeled with an underscore is treated the same as an unlabeled field, e.g. `(_ ≔ a, b)` is the same as `(a,b)`.

Field accesses can also be positional rather than named: `M .0` refers to the zeroth field, `M .1` to the next one and so on.  However, it's important to note that this is in reference to the order in which fields were declared in the record *type*, not in the tuple, even if labels were used in the tuple to give the components in a different order.  For instance, `((snd ≔ b, fst ≔ a) : A × B) .0` equals `a`.

Tuples are an "outfix" notation that includes the parentheses, rather than an infix meaning of the comma; thus the parentheses are always required.  Tuples are not associative: neither `(a, (b, c))` nor `((a, b), c)` can be written as `(a,b,c)`.  The latter is applicable only to a record type with three fields, whereas the former two apply to a record type with two fields, one of which is itself a record type with two fields.  (This aligns with the behavior of functional programming languages such as Haskell and OCaml.)

A record type can have zero fields, yielding a unit type.  Its unique element is thus written `()`.  A record type can also have exactly one field, in which case it is isomorphic to the type of that field.  However, the element of a 1-tuple must be labeled, since an unlabeled 1-tuple `(a)` would look just like `a` inside ordinary parentheses.  Note that you can still write `(_ ≔ a)` to avoid naming the field in a 1-tuple, and `M .0` to access the unique field.

Tuples are checking, not synthesizing: the same term `(a,b)` can check at many different record types.  Since the argument of a field projection is synthesizing, this means that a tuple must be ascribed in order to immediately project out a field: `(a,b) .fst` doesn't typecheck, but `((a,b) : A × B) .fst` does.  Note in particular that different record types can share the same field names, so from `x .fst` or `(fst ≔ a, snd ≔ b)` the typechecker can't even guess what record type family we are talking about without knowing the type of `x`, in the first case, or the type being checked at, in the second case.

Record types satisfy eta-conversion, meaning that two elements of the type are equal if all their fields are equal, even if they are not both syntactically tuples.

### Datatypes and pattern-matching

A constant that is a type family can also be declared to be a *datatype*, by giving a list of its constructors with their types.  Like fields, constructors belong to a separate name domain, and they are always written with an ending period.  (This use of a separate syntax can be compared with functional programming languages such as Haskell and OCaml, where datatype constructors also have a separate syntax — beginning with a capital letter is common.)  The type of each constructor must be a function-type whose codomain is an instance of the datatype, and whose domain can involve instances of the datatype itself.  The latter occurrences ought to be strictly positive, but currently there is no check for that.

The arguments of a datatype family are divided into parameters and indices, the difference being that the output of each constructor must be fully general in the parameters.  (This includes the case of so-called "non-uniform parameters" for which the recursive *inputs* need not be fully general.)  Accordingly, when constructors are applied like functions to their arguments, we omit the parameters; instead the typechecker takes the parameters from the type at which the constructor is being checked.  For example, a sum-type `sum A B` contains elements `inl. a` and `inr. b`, where we don't write `A` and `B` as arguments of the constructors since they are parameters.  Note that this means constructors don't synthesize: from `inl. a` the typechecker can't guess what the type `B` should be unless it is ascribed or in a context where the type is known.  (In fact it's even worse than that: because all constructors inhabit the same flat name domain, and different datatypes can have constructors with the same name, the typechecker can't even guess what datatype family `inl. a` should belong to.)

There is not yet a syntax for the user to define new datatypes; they have to be done in OCaml code, as for record types.  Datatypes currently available include an empty type `∅`, binary sum-types `sum A B` with constructors `inl` and `inr`, natural numbers `ℕ` or `Nat` with constructors `zero` and `suc`, forwards lists `List A` with constructors `nil` and `cons`, backwards lists `Bwd A` with constructors `emp` and `snoc`, and length-indexed vectors `Vec A n` with constructors `nil` and `cons`.  (Since implicit arguments are not yet implemented, the `cons` of `Vec` has to take the previous length as an additional argument, so we have to write `cons. 2 a (cons. 1 b (cons. 0 c nil.))` and the syntax `[> a, b, c >]` is not yet available for vectors.)

When a new constant is defined as a function containing datatypes in its domain, it can pattern-match on such an argument.  For instance, the function that swaps the elements of a binary sum can be written as
```
def swap : (A B : Type) → sum A B → sum B A
  ≔ A B x ↦
  [ x
    | inl. a ↦ inr. a
    | inr. b ↦ inl. b
  ]
```
By omitting the variable name, it is possible to abstract over a variable and simultaneously match against it (pattern-matching lambda abstraction).  Thus, the above can equivalently be written
```
def swap : (A B : Type) → sum A B → sum B A ≔ A B ↦
  [ | inl. a ↦ inr. a
    | inr. b ↦ inl. b
  ]
```

At present, at least, it is only possible to match on a variable argument of the function, not on an arbitrary term; this allows the output type of the function to be refined in each branch without additional annotations.  It is also only possible to match on one argument at a time; but each branch of the match can proceed to match again on a different argument, or on one of the pattern variables (arguments of the constructor).  When matching against a datatype with indices, the indices in the type of the match variable must currently also be distinct free variables (this is even less general than Agda's `--without-K` matching and hence also ensures consistency with univalence).

Finally, a function defined by pattern-matching can also be recursive, calling itself on smaller arguments in each branch.  (Actually, currently there is no termination-checking, so the arguments don't even have to be smaller.  But there is coverage-checking: all the constructors of a datatype must be present in the match.  So you can write infinite loops, but your programs shouldn't get stuck.)

### Codatatypes and copattern-matching

A *codatatype* is superficially similar to a record type: it has a list of fields (which in this case we sometimes call *methods*), each with a type, which are projected out using the same syntax `x .fld`.  The primary differences are:

1. Codatatypes can be (co)recursive: the output type of each method can involve the codatatype itself.  (Such occurrences ought to be strictly positive, but currently there is no check for that.)
2. Codatatypes do not satisfy eta-conversion (this being undecidable in the recursive case).
3. Elements of codatatypes are defined by copattern-matching rather than with tuples.

Copattern-matching is similar to tupling, but the syntax is different (more like pattern-matching); all the methods must be labeled, including their initial periods; and a constant defined by copattern-matching can be corecursive, referring to itself in the (co)branches.  As an example, the type `Stream A` (where `A` is a parameter) has two methods, `head` of type `A`, and `tail` of type `Stream A`.  For example, the infinite stream `nats n` of all natural numbers starting at `n` can then be defined by copattern-matching as
```
def nats : ℕ → Stream ℕ
  ≔ n ↦ [
  | .head ↦ n
  | .tail ↦ nats (suc. n)
]
```
The empty (co)match `[ ]` is ambiguous: it could denote a pattern-matching lambda on a datatype with no constructors, or a copattern-match into a codatatype with no methods.  Fortunately, since both possibilities are checking rather than synthesizing, the ambiguity is resolved by bidirectional typechecking.

Computationally, it is suggested to think of a codatatype as an object-oriented *interface*, and a function defined by copattern-matching as an (immutable) *object* that implements that interface, with the arguments of the function being its "member variables".  In particular, an "object" of this sort does not compute to anything until a field is accessed (method is called).  For instance, `nats 0 .tail .tail .tail .head` evaluates to `3`, but `nats 0` itself does not evaluate to anything.  This is very different from a tuple, which should be thought of as a *data structure* that contains a collection of values; in particular, it explains why records have eta-conversion and codatatypes do not.

### Case trees

Tuples can occur anywhere in a term, but pattern-matches and copattern-matches can (currently) only occur at a top level definition of a constant.  However, all three (as well as lambda-abstractions) can be arbitrarily deeply nested in a top-level definition: we can start with a pattern-match, then in one branch (where the output type is a codatatype) proceed to a copattern-match, while another branch proceeds to match on a different argument belonging to another datatype, and so on.  This is called a *case tree*: it is composed of nested abstractions, tuples, pattern matches against constructors, and copattern comatches against fields, until it reaches a "leaf" which is an arbitrary term (in the context of the variables introduced so far by the abstractions and pattern matches).  A degenerate version of a case tree is just a leaf, which simply defines the constant to equal some given term.

This means that defining a constant to equal something like "`x y ↦ ( fld1 ≔ M, fld2 ≔ N )`" appears ambiguous as to whether it is just a leaf or whether it is a case tree involving abstractions and a tuple.  The rule to resolve this ambiguity is that *as much as possible of a definition is included in the case tree*.  This is usually what you want.

A constant defined by a case tree does not compute unless the tree can be followed all the way down to a leaf.  In particular, a match or comatch is never exposed as part of a term.  Moreover, this means that when defining a constant to equal a given term, by putting the abstractions into the case tree rather than the term we ensure that it must be applied to all its arguments in order to compute, rather than immediately evaluating to an abstraction.  Again, this is usually what you want.  It more or less aligns with the behavior of functions defined by (co)pattern-matching in Agda, whereas Coq has to mimic it with `simpl nomatch` annotations.

As noted, case trees can include tuples as well as matches and comatches.  Thus it is also possible to define constructors of records by case trees, in addition to as tuples.  These have the advantage that they synthesize, but the disadvantage that they must be applied explicitly to all the parameters.  For example, with Σ-types we can define
```
def pair : (A : Type) (B : A → Type) (a : A) (b : B a) → Σ A B
  ≔ A B a b ↦ (a,b)
```
and then we can write `pair A B a b` instead of `(a,b) : Σ A B`.

Note that case trees are generally considered the internal implementation of pattern-matching definitions, e.g. Agda compiles its definitions internally to case trees.  I believe it is better to expose the case tree to the user explicitly.  In some cases, this can make code more concise, since all the arguments of the function no longer have to be written again in every branch and sub-branch.  But more importantly, the order in which matches are performed, and hence the way in which the function actually computes, is this way obvious to the reader, and can be specified explicitly by the programmer, in particular eliminating the confusion surrounding Agda's `--exact-split` option.  So I have no plans to implement Agda-style pattern matching syntax.

There are other enhancements to matching that could be done, however, such as implementing something closer to Agda's `--without-K` unification-based matching.  It should also be possible to allow matches inside arbitrary terms by lifting them to toplevel and defining a new internal constant.  And it might be possible to implement a version of Coq/ML-style simultaneous matches like `match x, y with ...`, since the order of the variables indicates the order in which they are matched.  Similarly, some kind of deep matching such as `[ zero. ↦ ... | suc. zero. ↦ ... | suc. (suc. n) ↦ ... ]` may be possible.


## Parametric Observational Type Theory

Every type `A` has a binary identity/bridge type denoted `Id A x y`, and each term `x:A` has a reflexivity term `refl x : Id A x x`.  (The argument of `refl` must synthesize.)  Elements of the identity type of the universe include, at least, a binary correspondence, which is instantiated by application syntax; so from `A₂ : Id Type A₀ A₁`, if `a₀:A₀` and `a₁:A₁` we have `A₂ a₀ a₁ : Type`.  In particular, `Id A x y` is an instance of this syntax, as we have `Id A : Id Type A A`, and indeed `Id A` is just a notational variant of `refl A`.

Iterating `Id` or `refl` multiple times produces higher-dimensional cube types and cubes.  There is a symmetry operation `sym` that acts on at-least-two dimensional cubes, swapping or transposing the last two dimensions; its argument must also synthesize.  Combining versions of `refl` and `sym` yields arbitrary higher-dimensional "degeneracies" (from the BCH cube category).  There is also a generic syntax for such degeneracies: `M⁽¹⁰²⁾` or `M^(102)` where  the string of digits represents the degeneracy, with `0` denoting a degenerate dimension and the other digits denoting a permutation.  In the unlikely event you are working with dimensions greater than nine, you can separate multi-digit numbers in a permutation with a hyphen, e.g. `M⁽¹⁻²⁻³⁻⁴⁻⁵⁻⁶⁻⁷⁻⁸⁻⁹⁻¹⁰⁾` or `M^(0-1-2-3-4-5-6-7-8-9-10)`.

The identity/bridge type of a pi-type computes to another pi-type.  In Narya this computation is "up to definitional isomorphism", meaning that the following two types are isomorphic:
```
id (A → B) f g
(x₀ : A) (x₁ : A) (x₂ : Id A x₀ x₁) → Id B (f x₀) (g x₁)
```
However, in most cases we can pretend that these two types are literally the same, because the typechecker allows lambda-abstractions matching the structure of the second to also typecheck at the first, and likewise elements of the first can be applied to arguments as if they were functions belonging to the second.

There is no unifier yet, so such an abstraction or application must include both endpoints `x₀` and `x₁` explicitly as well as the identity `x₂`.  However, there is a shorthand syntax for such higher-dimensional abstractions: instead of `x₀ x₁ x₂ ↦ M` you can write `x ⤇ M` (or `x |=> M` in ASCII).  This binds `x` as a "family" or "cube" of variables whose names are suffixed with face names in ternary notation: `x.0` and `x.1` and `x.2`, or in higher dimensions `x.00` through `x.22` and so on.  (The dimension is inferred from the type at which the abstraction is checked.)  Note that this is a *purely syntactic* abbreviation: there is no object "`x`", but rather there are really *three different variables* that just happen to have the names `x.0` and `x.1` and `x.2`.  (There is no potential for collision with user-defined names, since ordinary local variable names cannot contain internal periods.)

There is no need for an additional primitive `ap`; it is accessed by applying `refl` to a function.  That is, if `f : A → B`, then `refl f x₀ x₁ x₂` relates `f x₀` to `f x₁` in `B`.  Likewise, identity types can be obtained by applying `refl` to a type: `Id A X Y` is just a convenient abbreviation of `refl A X Y`.

Heterogeneous identity/bridge types are similarly obtained from `refl` of a type family: if `B : A → Type`, then `refl B x₀ x₁ x₂` is a identification/bridge in `Type` between `B x₀` and `B x₁`.  Given elements `y₀ : B x₀` and `y₁ : B x₁`, we can "instantiate" this identification at them to obtain a type of heterogeneous identifications.  This is also written as function application, `refl B x₀ x₁ x₂ y₀ y₁`.  Such heterogeneous identity/bridge types are used in the computation (up to definitional isomorphism) of dependent function types: the following type types are isomorphic.
```
id ((x:A) → B x) f g
(x₀ : A) (x₁ : A) (x₂ : Id A x₀ x₁) → refl B x₀ x₁ x₂ (f x₀) (g x₁)
```

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

Internal parametricity is currently implemented by a constant `Gel`, defined with `Types.Gel.install ()`, whose type is
```
(A : Type) (B : Type) (R : (x:A) (y:B) → Type) → Id Type A B
```
As above, since `Gel A B R` is a bridge in the universe, it can be further instantiated at elements `a : A` and `b : B` to obtain a type `Gel A B R a b`.  This type is isomorphic to the original `R a b`.  In fact, `Gel` is declared as a special kind of "one-dimensional record type" (in contrast to the usual zero-dimensional ones) with eta-conversion, with a single field `ungel` of type `R a b`.  Thus the isomorphism is implemented by, on the one hand, accessing this field `M .ungel`, and on the other by building a record `(ungel ≔ M)`.  As with other unary records, these can also be written `M .0` and `(_ ≔ M)`.


## Remarks on implementation

As is common for normalization-by-evaluation, the implementation uses De Bruijn *indices* for syntactic terms and De Bruijn *levels* for semantic values.  A little more unusually, however, the De Bruijn indices are "intrinsically well-scoped".  This means that the type of terms is parametrized by the length of the context (as a type-level natural number, using GADTs), so that the OCaml compiler ensures *statically* that De Bruijn indices never go out of scope.  Other consistency checks are also ensured statically in a similar way, such as the matching of dimensions for certain types and operators, and scoping and associativity for notations.  (The latter is the reason why tightnesses are dyadic rationals: they are represented internally as type-level finite surreal-number sign-sequences, this being a convenient way to inductively define a dense linear order.)

This approach does have the drawback that it requires a fair amount of arithmetic on the natural numbers to ensure well-typedness, which is not only tedious but some of it also ends up happening at run-time.  Since type-level natural numbers are represented in unary, this could be a source of inefficiency in the future.  However, it has so far proven very effective at avoiding bugs!
