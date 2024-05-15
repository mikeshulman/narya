# Narya: A proof assistant for higher-dimensional type theory

Narya is eventually intended to be a proof assistant implementing Multi-Modal, Multi-Directional, Higher/Parametric/Displayed Observational Type Theory, but a formal type theory combining all those adjectives has not yet been specified.  At the moment, Narya implements a normalization-by-evaluation algorithm and typechecker for an observational-style theory with Id/Bridge types satisfying parametricity, of variable arity and internality.  There is a parser with user-definable mixfix notations, and user-definable record types, inductive datatypes and type families, and coinductive codatatypes, with functions definable by matching and comatching case trees.

Narya is very much a work in progress.  Expect breaking changes, including even in fundamental aspects of the syntax.  But on the other side of the coin, feedback on anything and everything is welcome.  In particular, please report all crashes, bugs, unexpected errors, and other unexpected, surprising, or unintuitive behavior.


## Top level interface

### Compilation

Narya requires OCaml version 5.1.0 (or later) and various libraries.  After installing any version of OCaml and its package manager Opam, you can install Narya with its dependencies as follows:

```
opam switch create 5.1.0
opam install zarith uuseg bwd algaeff asai yuujinchou react lwt lambda-term fmlib

cd ../narya
dune build @install
dune runtest
dune install
```

This will make the executable `narya` available in a directory such as `~/.opam/5.1.0/bin`, which should be in your `PATH`.  Alternatively, instead of `dune install` you can also run the executable directly from the `narya/` directory with `dune exec narya`.  In this case, to pass flags to the executable, put them after a `--`.  For instance, `dune exec narya -- test.ny -i` loads the file `test.ny` and then enters interactive mode.


### Command-line flags

The Narya executable accepts at least the following command-line flags.

#### Execution behavior

- `-interactive` or `-i`: Enter interactive mode (see below)
- `-exec STRING` or `-e STRING`: Execute a string argument (see below)
- `-no-check`: Don't typecheck and execute code (only parse it)

#### Formatting output

- `-verbose` or `-v`: Show verbose messages
- `-unicode` and `-ascii`: Display and reformat code using Unicode (default) or ASCII
- `-noncompact` and `-compact`: Select reformatting mode
- `-reformat`: Display reformatted code on stdout after parsing

#### Controlling parametricity

These options are discussed further below.

- `-arity N`: Set the arity of parametricity to N (1 ≤ N ≤ 9)
- `-direction X`: Set the symbol and names for reflexivity
- `-internal` and `-external`: Set whether parametricity is internal (default) or external
- `-dtt`: Poor man's dTT mode (`-arity 1 -direction d -external`)

### Execution

When the Narya executable is run, it loads and typechecks all the files given on its command line, in order.  As usual, the special filename `-` refers to standard input.  It then does the same for any strings supplied on the command line with `-e`.  Finally, if `-i` was given, it enters interactive mode.

There is currently no importing or exporting: all definitions from all sources go into the same flat namespace, so for instance in interactive mode you can refer to definitions made in files that were loaded previously.  There is also no compilation or caching: everything must be typechecked and loaded anew at every invocation.

In interactive mode, commands typed by the user are executed as they are entered.  Since many commands span multiple lines, Narya waits for a blank line before parsing and executing the command(s) being entered.  Make sure to enter a blank line before starting a new command; interactive commands must be entered and executed one at a time.  The result of the command is printed (more verbosely than is usual when loading a file) and then the user can enter more commands.  Type Control+D to exit interactive mode.  In addition, in interactive mode you can enter a term instead of a command, and Narya will assume you mean to `echo` it (see below).


### Commands

In a file, conventionally each command begins on a new line, but this is not technically necessary since each command begins with a keyword that has no other meaning.  Indentation is not significant, but a standard reformatter (like `ocamlformat`) is planned so that the default will be to enforce a uniform indentation style.  (Experimental output of this reformatter-in-progress is available with the `-reformat` command-line option.)  So far, the available commands are:

1. `def NAME [PARAMS] [: TYPE] ≔ TERM [and ...]`

   Define a global constant called `NAME` having type `TYPE` and value `TERM`.  Thus `NAME` must be a valid identifier (see below), while `TYPE` must parse and typecheck as a type, and `TERM` must parse and typecheck at type `TYPE`.  If `TYPE` is omitted, then `TERM` must synthesize a type (see below).  In addition, if `TYPE` is specified, then `TERM` can also be a case tree or canonical type declaration (see below).  The optional `PARAMS` is a list of parameters of the form `(x : PTY)`, or more generally `(x y z : PTY)`, with the effect that the actual type of the constant `NAME` is the Π-type of `TYPE` (or the synthesized type of `TERM`) over these parameters, and its value is the λ-abstraction of `TERM` over them.  That is, `def foo (x:A) : B ≔ M` is equivalent to `def foo : A → B ≔ x ↦ M`.  Finally, a family of constants can be defined mutually by using the `and` keyword to introduce the second and later ones (see below).

2. `axiom NAME [PARAMS] : TYPE`

   Assert a global constant called `NAME` having type `TYPE`, without any definition (an axiom).  Parameters are treated as for `def`.

3. `echo TERM`

   Normalize `TERM` and print its value and its type to standard output.  Note that `TERM` must synthesize a type (see below); if it is a checking term you must ascribe it.  In interactive mode, if you enter a term instead of a command, Narya assumes you mean to `echo` that term.

4. `notation [TIGHTNESS] NAME : […] PATTERN […] ≔ HEAD ARGUMENTS`

   Declare a new mixfix notation.  Every notation must have a `NAME`, which is an identifier like the name of a constant, and a `TIGHTNESS` unless it is outfix (see below).  The `PATTERN` of a notation is discussed below.  The value of a notation consists of a `HEAD`, which is either a previously defined constant or a datatype constructor (see below), followed by the `ARGUMENTS` that must consist of exactly the variables appearing in the pattern, once each, in some order.
   

## Built-in types

### The universe

Currently there is only one universe `Type` that contains all types, including itself, making the type theory inconsistent.  In the future it is planned to incorporate universe levels using [mugen](https://github.com/redPRL/mugen).


### Functions and function-types

Apart from the universe, the only predefined type is a dependent function-type, written `(x:A) → B x` as in NuPRL and Agda.  As usual, if `B` does not depend on `x` one can simplify this to `A → B`, and iterated function-types can be combined, including combining multiple variables with the same type, as in `(x y : A) (z : B x y) → C x y z`.  Also as usual, this notation is right-associative, so `A → B → C` means `A → (B → C)`.  The unicode → appearing here is interchangeable with the ASCII `->`.

Again as usual, functions are applied by juxtaposition; if `f : (x:A) → B x` and `a : A` then `f a : B a`.  And this is left-associative, so if `f : A → B → C` then `f a b : C`.

Functions are introduced by abstraction, which in Narya is written (somewhat unusually) as `x ↦ M`, or `x y z ↦ M` to abstract multiple variables at once.  The unicode ↦ is interchangeable with the ASCII `|->`.

The variable in a function-type or an abstraction can be replaced by an underscore `_`, indicating that that variable is not used and thus needs no name.  For types this is equivalent to a non-dependent function-type: `(_ : A) → B` means the same as `A → B`.  For abstractions, `_ ↦ M` defines a constant function, whose value doesn't depend on its input.

In addition, there is a built-in constant called `Π` that represents dependent function-types.  The type of `Π` is `(X : Type) → (X → Type) → Type`, and `Π A B` reduces to `(x : A) → B x`.  In other words, it behaves as if defined by
```
def Π (A : Type) (B : A → Type) : Type ≔ (x : A) → B x
```
This is mainly useful for writing and printing higher-dimensional function-types (see below).


## Names and notations

### Mixfix notations

The parser supports arbitrary mixfix operations with associativities and precedences, although we prefer to say "tightness" instead of "precedence", to make it clear that higher numbers bind more tightly.  Tightnesses are *dyadic rational numbers* (i.e. having denominator a power of 2), written in decimal notation.  Tightnesses +ω and −ω also exist, but are reserved for internal use.  Some notations are built in, but the user can also declare new notations with the `notation` command mentioned above.

The `PATTERN` of a notation is a list of interspersed distinct local variable names and double-quoted symbols, such as `x "+" y` for addition or `Γ "⊢" x "⦂" A` for a typing judgment.  Each quoted symbol must be exactly one token (see below); any two variables must be separated by a symbol (but two symbols can follow each other without a variable in between); and there must be at least one symbol.  If the pattern starts with a variable, it may be preceded by an ellipsis `…`, indicating that it is left-associative; and dually if it ends with a variable, it may be followed by an ellipsis, indicating that it is right-associative (but not both).

A notation which starts and ends with a variable is called "infix"; one that starts with a symbol and ends with a variable is called "prefix"; one that starts with a variable and ends with a symbol is called "postfix"; and one that starts and ends with a symbol is called "outfix".  An outfix notation *may not* have a tightness (it always behaves as if it has tightness +ω).  All other notations must have a tightness, which is relevant only on the side(s) where they are "open" (both sides for an infix notation, the right for a prefix one, and the left for a postfix one).

We have already mentioned the right-associative function-type notation `A → B`; this has tightness 0.  Function abstraction `x ↦ M` is also right-associative, so you can write `x ↦ y → M` (which can also be abbreviated as `x y ↦ M`), and has tightness −ω.  Application `M N` is implemented specially since an ordinary notation cannot have two variables next to each other without a symbol in between, but it behaves as though it is left-associative with tightness +ω.  (In particular, a nonassociative prefix notation of tightness +ω, say `@`, will bind tighter than application, so that `@ f x` parses as `(@ f) x`.  However, there are no such notations yet.)

In addition, parentheses `( M )` are defined as an outfix notation, hence with effective tightness +ω.  This emphasizes that notations of any tightness, even −ω, can appear in "internal" locations of a notation, meaning those with notation symbols on both sides.  Tightness and associativity only control what other notations can appear in the "external" locations that are only delimited by a notation symbol on one side.


### Comments and strings

There are two kinds of comments.  A line comment starts with a backquote `` ` `` and extends to the end of the line.  A block comment starts with `` {` `` and ends with `` `} ``.  Block comments can be nested and can contain line comments, but cannot start inside a line comment.

String literals are surrounded by double-quotes, as in `"hello, world"`.  At present the only use of string literals is in the `notation` command for defining user notations.


### Tokens

A Narya source file is expected to be UTF-8 encoded and can contain arbitrary Unicode.  As usual, the code is first *lexed* by separating it into "tokens", and then the sequence of tokens is *parsed* into an abstract syntax tree of notations.  Both identifiers (variable and constant names) and the symbols in a mixfix notation are tokens.  Whitespace (including comments) always creates a token boundary.  And since notation symbols can be made of the same characters that might be in an identifier, whitespace is sometimes necessary to separate identifiers from symbols.  For instance, if `⋆` is defined as a binary operator, we cannot write `x⋆y` (or even `1⋆1`) since that would be lexed as a single token.

However, in Narya there are the following exceptions to this, where whitespace is not needed to separate tokens:

- The characters `( ) [ ] { } ? → ↦ ⤇ ≔ ⩴ ⩲ …`, which either have built-in meaning or are reserved for future built-in meanings, are always treated as single tokens.  Thus, they do not need to be surrounded by whitespace.  This is the case for parentheses and braces in most languages, but in Narya you can also write, e.g., `A→B` without spaces.  The non-ASCII characters in this group all have ASCII-sequence substitutes that are completely interchangeable: `-> |-> |=> := ::= += ...`.  Additional characters may be added to this list in the future.
- A nonempty string consisting of the characters `~ ! @ # $ % & * / = + \ | , < > : ; -` is always treated as a single token, and does not need to be surrounded by whitespace.  Moreover, such tokens may only be notation symbols, not identifiers.  Note that this is most of the non-alphanumeric characters that appear on a standard US keyboard except for those that already have another meaning (parentheses, backquote, double quote, curly braces) or are allowed in identifiers (period, underscore, and single quote).  In particular:
  - Ordinary algebraic operations like `+` and `*` can be defined so that `x+y` and `x*y` are valid.
  - This includes the colon, so you can write `(x:A) → B`, and similarly for the comma `,` in a tuple and the bar `|` in a match or comatch (see below).  But the user can also use these characters in other operators.
  - The ASCII substitutes for the single-token Unicode characters also fall into this category, so you can write for instance `A->B`.
  - The ASCII hyphen `-` is in this category; in addition to its being part of `->` and `|->`, this allows a subtraction operator `x-y` to be written without spaces.  (Note, though, that the current parser does not permit a binary subtraction to coexist with a unary negation using the same character.)  Therefore, unlike in Agda, the hyphen is not allowed in identifiers.

  This rule is intended to be a compromise, allowing the user to define plenty of infix operators that don't require spacing but also arbitrary unicode operators, while keeping the lexer rules simple and unchanging as new operators are defined.  However, feedback is welcome!

- A nonempty string such as `⁽¹ᵉ³⁾` consisting of Unicode superscript letter, digit, and hyphen characters, `ᵃᵇᶜᵈᵉᶠᵍʰⁱʲᵏˡᵐⁿᵒᵖ𐞥ʳˢᵗᵘᵛʷˣʸᶻ⁰¹²³⁴⁵⁶⁷⁸⁹⁻`, in between Unicode superscript parentheses, `⁽` and `⁾`, is treated as a single token and applied as a "superscript" operator to whatever immediately precedes it.  This is used for generic degeneracies (see below).  It binds more tightly than anything (tightness of "ω+1"), including function application, so that `f⁽ᵉ⁾ x` means `(f⁽ᵉ⁾) x` and `f x⁽ᵉ⁾` means `f (x⁽ᵉ⁾)`.  In addition, a caret `^` followed by a nonempty string of the corresponding ASCII characters `abcdefghijklmnopqrstuvwxyz0123456789-` (no internal spaces!) in between ordinary parentheses `(` and `)` has exactly the same meaning with the same tightness: `f^(e) x` means the same as `f⁽ᵉ⁾ x`.  (Unicode subscript characters are not treated specially; thus they may appear freely in identifiers or symbols.)


### Identifiers

Identifiers (variables and constant names) can be any string of non-whitespace characters, other than those mentioned above as special, that does not start or end with a period or an underscore, and is not a reserved word.  Currently the reserved words are
```
let in def and axiom echo notation match sig data codata
```
In particular, identifiers may start with a digit, or even consist entirely of digits (thereby shadowing a numeral notation, see below).  Internal periods in identifiers denote namespace qualifiers on constants; thus they cannot appear in local variable names.


### Namespaces

Narya uses [yuujinchou](https://redprl.org/yuujinchou/yuujinchou/) for hierarchical namespacing, with periods to separate namespaces.  Thus `nat.plus` is a potential name for a constant in the `nat` namespace, which can be defined directly with `def nat.plus` or could, in theory, be defined with `def plus` inside a "section" named `nat`, and would become available as simply `plus` if `nat` were imported.  However, Narya does not yet expose the import, export, and sectioning operations of yuujinchou to the user.


## Typechecking details

### Bidirectionality

Narya's typechecker is bidirectional.  This means that some terms *synthesize* a type, and hence can be used even in a place where the "expected" type of a term is not known, whereas other terms *check* against a type, and hence can only be used where there is an "expected" type for them to check against.  Of the terms we have mentioned so far:

- Function application `M N` synthesizes, by first requiring `M` to synthesize a function-type `(x:A) → B`, then checking `N` against the input type `A`, and finally synthesizing the corresponding output `B[N/x]`.

- Function abstraction `x ↦ M` checks against a function-type `(x:A) → B` by checking `M` against `B` in a context extended by a variable `x:A`.  In particular, this means that the same abstraction term can mean different things depending on what type it is checked against.  For instance, `x ↦ x` checks against *any* endo-function type `A → A`.

- Type-forming operators such as `Type` and `(x:A) → B` synthesize, after requiring their inputs to synthesize.  This might be modified later after universe levels are introduced.

- Variables and constants synthesize their declared types.


### Ascription

If you want to use a checking term in a synthesizing position, you have to *ascribe* it to a particular type by writing `M : A` (or `M:A` by the lexer rules discussed above).  This *checks* `M` against the supplied type `A`, and then itself *synthesizes* that type.  For example, you cannot directly apply an abstraction to an argument to create a redex as in `(x ↦ M) N`, since the abstraction only checks whereas a function being applied must synthesize, but you can if you ascribe it as in `((x ↦ M) : A → B) N`.  In general, ascription tends only to be needed when explicitly writing a redex or something similar.

The ascription notation has tightness −ω, and is non-associative, so that `M : N : P` is a parse error.  However, the right-associativity of `↦` and the fact that they share the same tightness means that `x ↦ M : A` is parsed as `x ↦ (M : A)`, hence the placement of parentheses in the above example redex.

*Side note:* The coexistence of type ascription and NuPRL/Agda-style dependent function-types leads to a potential ambiguity: `(x : A) → B` could be a dependent function type, but it could also be a *non-dependent* function type whose domain `x` is ascribed to type `A` (which would therefore have to be a type universe).  Narya resolves this in favor of the dependent function type, which is nearly always what is intended.  If you really mean the other you can write it as `((x : A)) → B` or `((x) : A) → B`; but I can't imagine why you would need to do this, since the only possible ambiguity is when `x` is a variable (or a list of variables), and variables and constants (and application spines of such) always synthesize their type anyway and thus don't need to be ascribed.


### Let-binding

Writing `let x ≔ M in N` binds the local variable `x` to the value `M` while typechecking and evaluating `N`.  The unicode ≔ is interchangeable with the ASCII `:=`.  Computationally, `let x ≔ M in N` is equivalent to `(x ↦ N) M`, but it also binds `x` to the value `M` while typechecking `N`, which in a dependent type theory is stronger.

Both `M` and `N` are required to synthesize, and the let-binding then synthesizes the same type as `N`.  The idiom `let x ≔ M : A in N` can be written alternatively as `let x : A ≔ M in N`.  The let-binding notation is right-associative with tightness −ω.


### Eta-conversion and function constants

Functions satisfy undirected η-conversion as well as directed β-reduction.  That is, while neither of `x ↦ f x` or `f` simplifies to the other, they are considered equal for the purposes of typechecking (they are "convertible").

In addition, constants defined as functions do not reduce until they are applied to all of their arguments, including both those declared as parameters and those not so declared.  (This behavior is a special case of "case trees", discussed below.)  For instance, if we define addition of Church numerals as
```
def cplus (A:Type) (m n : (A → A) → (A → A)) : (A → A) → (A → A) ≔
  f x ↦ m f (n f x)
```
then `cplus A (f x ↦ f x) (f x ↦ f x)` (i.e. "1 + 1") doesn't reduce to `(f x ↦ f (f x))` because it is not fully applied, whereas `cplus A (f x ↦ f x) (f x ↦ f x) f x` does reduce to `f (f x)`.  However, `cplus A (f x ↦ f x) (f x ↦ f x)` is still *convertible* with `(f x ↦ f (f x))` because equality-checking does η-conversion.  If you want to display the body of a constant defined as a function, you must manually η-expand it, which means it has to be ascribed as well:
```
echo (A f x ↦ cplus A (f x ↦ f x) (f x ↦ f x) f x)
  : (A:Type) → (A → A) → (A → A)
  
A f x ↦ f (f x)
  : (A : Type) → (A → A) → A → A
```
If there is significant demand for displaying function bodies, we may add an option to ask for η-expansion.


## Interactive proof

There is no truly interactive proof or term-construction mode yet, but there is the ability to leave *holes* in terms.  A hole is indicated by the character `?`, which is always its own token.  A hole does not synthesize, but checks against any type whatsoever, and emits a message showing the type it is being checked against, and all the variables in the context with their types (and definitions, if any).  There is not yet any way to go back and fill a hole *after* it is created, but you can get something of the same effect by just editing the source code to replace the `?` by a term (perhaps containing other holes) and reloading the file.

A command containing one or more holes will succeed as long as the term typechecks without knowing anything about the contents of the holes, i.e. treating the holes as axioms generalized over their contexts.  In other words, it will succeed if the term would be well-typed for *any* value of the hole having its given type.  If there are equality constraints on the possible fillers of the hole, then the command will fail; a hole is not equal to anything except itself.  (This will be improved in the future.)

If a command containing one or more holes succeeds, you can continue to issue other commands afterwards, and each hole will continue to be treated like an axiom.  When a term containing a hole is printed, the hole displays as `?N` where `N` is the sequential number of the hole.  Unlike the printing of most terms, this is *not* a re-parseable notation.  Moreover, if the hole has a nonempty context, then occurrences of that hole in other terms may have other terms substituted for the variables in its context and these substitutions *are not indicated* by the notation `?N`.  This may be improved in future, but it is ameliorated somewhat by the fact that "case tree holes" (see below) never appear in terms.

Note that even if no holes appear explicitly when you print a term, it might still depend implicitly on the values of holes if it involves constants whose definition contain holes.

When Narya reaches the end of a file (or command-line `-e` string) in which any holes were created, it issues an error.  In the future this might become configurable, but it aligns with the behavior of most other proof assistants that each file must be complete before it can be loaded into another file.  Of course, this doesn't happen in interactive mode.


## Record types and tuples

### Defining record types

A record type is defined by a number of *fields*, each with a declared type.  A constant of type `Type` can be defined to be a record type in a `def` statement by using the keyword `sig` and listing the fields with their types in parentheses, separated by commas.  For instance, we could bundle a type with an operation on it:
```
def Magma : Type ≔ sig (
  t : Type,
  op : t → t → t,
)
```
The trailing comma after the last field is optional.  (By the lexing rules above, no space is required around the commas, unless they follow a type that is expressed using a notation that ends with another special ASCII character.)  Note that later fields can depend on the values of previous fields, by name.  The names of fields must be identifiers, except that they may not contain periods.

Although this command may look like it is defining `Magma` to equal a pre-existing type denoted `sig (t:Type, op:t→t→t)`, in fact it declares `Magma` to be a *new* type that didn't previously exist and doesn't reduce to anything else.  In particular, therefore, declaring another identical-looking type:
```
def Magma' : Type ≔ sig (
  t : Type,
  op : t → t → t,
)
```
will yield a different result: `Magma` and `Magma'` are not convertible.

Like any definition, record types can have parameters.  For example, Σ-types are just a record type that can be defined by the user, if you wish:
```
def Σ (A : Type) (B : A → Type) : Type ≔ sig (
  fst : A,
  snd : B fst,
)
```
However, we consider it better style in general to use specialized record types rather than generic Σ-types, as it provides better error-checking and documentation of the meaning of the fields.  It is also probably more efficient to use one record type with a lot of fields than an iterated Σ-type.  In the future we plan to implement metaprogramming-like capabilities for proving theorems about arbitrary record types, so that using them in preference to generic Σ-types does not entail a loss of expressivity.

Currently user notations cannot bind variables, so it is not possible to define a binding notation such as `(x : A) × B x` for Σ-types.  But if we define a non-dependent product type, we can give it an infix notation:
```
def prod (A B : Type) : Type ≔ sig (
  fst : A,
  snd : B,
)

notation 1 prod : A "×" B ≔ prod A B
```

The fact that parameters can equivalently be abstracted over in the type and the term applies also to record type declarations.  That is, the above definition of Σ-types is entirely equivalent to
```
def Σ : (A:Type) → (A → Type) → Type ≔ A B ↦ sig (
  fst : A,
  snd : B fst,
)
```

A record type can have only one field:
```
def wrapped_nat : Type ≔ sig ( unwrap : ℕ )
```
or even zero fields:
```
def ⊤ := Type ≔ sig ()
```


### Tuples

To define an element of a record type we use a *tuple*, which consists of components separated by commas inside parentheses.  The most explicit kind of tuple labels each component by name, for instance:
```
def nat.magma : Magma ≔ (
  t ≔ ℕ,
  op ≔ plus,
)
```
Again, the trailing comma is optional, the Unicode ≔ can be replaced by ASCII `:=`, and neither of them normally requires surrounding space.  In this explicit version, the order of the fields doesn't matter: the above is equivalent to
```
def nat.magma : Magma ≔ (
  op ≔ plus,
  t ≔ ℕ,
)
```
Note that whatever order they are written in a tuple, the fields will always be *typechecked* in the order specified in the *record type declaration*.  This is necessary because the types of later fields can depend on the values of earlier ones.

The names of the fields in a tuple can also be replaced by underscores or omitted entirely, and in this case the fields are taken from the type definition *in the order given there*.  If some fields are named and others are not, the unnamed fields are matched up with the fields in the type that aren't named explicitly in the tuple, again in order.  Thus, we can also write the above tuple as any of the following:
```
(ℕ, plus)
(_ ≔ ℕ, _ ≔ plus)
(ℕ, op ≔ plus)
(t ≔ ℕ, plus)
(op ≔ plus, ℕ)
(plus, t ≔ ℕ)
```
but not, of course, `(plus, ℕ)` since that would try to interpret `plus` as the value of the field `t`.  Unlabeled tuples are convenient for small examples, including familiar cases such as `(0,0) : ℝ × ℝ`, but for records with large numbers of fields they are discouraged as being hard to understand and brittle.  (But some mathematicians do like to write, for instance, `(G,m,e,i,a,l,r,v) : Group`, and that is allowed.)

As this discussion suggests, tuples *check*, and do not synthesize.  In particular, this means the same tuple can mean different things when checked at different types.  An unlabeled tuple `(a,b)` can check at *any* record type with two fields for which `a` checks at the type of the first field and `b` at the type of the second (possibly depending on the value of `a`).  A labeled tuple such as `(fst ≔ a, snd ≔ b)` can likewise check at any such record type for which the names of the two fields are `fst` and `snd`.  *Field names are not scoped or namespaced*: they belong to a flat global name domain, distinct from that of constants and variables.

Like record types, tuples can have zero fields:
```
def ⋆ : ⊤ ≔ ()
```
They can also have only one field, although in this case the field must be labeled (if only with an underscore), since an unlabeled 1-tuple would look just like an ordinary parenthesized term:
```
def wrapped_zero : wrapped_nat ≔ (_ ≔ zero)
```

Syntactically, tuples are an outfix notation that includes the parentheses, rather than an infix meaning of the comma; thus the parentheses are always required.  Tuples are not associative: neither `(a, (b, c))` nor `((a, b), c)` can be written as `(a,b,c)`.  The latter belongs to a record type with three fields, whereas the former two belong to a record type with two fields, one of which is itself a record type with two fields.  (This aligns with the behavior of functional programming languages such as Haskell and OCaml.)


### Accessing fields

If `M` belongs to a record type that has a field named `fld`, then `M .fld` extracts the value of this field.  In particular, if `M` is a tuple, then this reduces to the corresponding component.  Note the space in `M .fld`, which distinguishes it from a single identifier named `M.fld` in the namespace `M`.

It is sometimes helpful to think of an element of a record type as a "function" and of `M .fld` as "applying" it to the field name as an "argument".  Syntactically, at least, they are parsed exactly the same way, except that the field name is prefixed by a period.  That is, field projections behave like a symbol-free left-associative infix operator of tightness +ω, and can therefore be interspersed with ordinary applications: `f a .fld b` means `((f a) .fld) b`.

A field projection `M .fld` requires `M` to synthesize a record type, and then synthesizes the value of the field `fld` in that record type (with any earlier fields that it depends on replaced by the corresponding fields of `M`).  Thus, if you want to write a "record redex" that creates a tuple and then immediately projects out one of its fields, you need to ascribe the tuple: `((a, b) : Σ A B) .fst`.

Finally, like unlabeled tuples that default to the order in which fields were declared in the record type, fields can also be projected out by index: `M .0` means the zeroth field declared in the record type, `M .1` means the first field, and so on.  It's important to note that this is in reference to the order in which fields were declared in the record *type*, not in any tuple, even if labels were used in the tuple to give the components in a different order.  For instance, `((snd ≔ b, fst ≔ a) : Σ A B) .0` equals `a`.  As with tuples, positional field access is convenient for small examples (especially when using positional tuples as well), but confusing and brittle when there are many fields.


### Eta-conversion and reduction

Records satisfy η-conversion: two elements of a record type whose components are field-wise convertible are themselves convertible.  For instance, if `M : Σ A B`, then `M` is convertible with `(M .fst, M .snd)`, although neither reduces to the other.  In particular, if a record type has zero fields, then it has a unique element `()` up to convertibility; and if it has only one field, it is definitionally isomorphic to the type of that field.

In addition, a constant that is defined to directly equal a tuple, or an abstracted tuple, does not *reduce* to that tuple directly: it only reduces when a field is projected.  For instance, if we have
```
def pair (a:A) (b:B a) : Σ A B ≔ (a,b)
```
then `pair a b` doesn't reduce to `(a,b)`.  But `pair a b .fst` does reduce to `a` and `pair a b .snd` does reduce to `b`, which in turn means (by η-conversion) that `pair a b` is *convertible* with `(a,b)`.  (This behavior is a special case of "case trees", discussed below.)  It does not apply (indeed, it cannot) to tuples that appear more deeply nested inside a term, such as the `(a,b)` in
```
def curry (f : A × B → C) (a:A) (b:B) : C ≔ f (a,b)
```


## Inductive datatypes and matching

### Defining datatypes

An inductive datatype is defined by a number of *constructors*, each with a declared type that must be an iterated function-type whose eventual codomain is the datatype itself.  A constant of type `Type` can be defined to be a datatype in a `def` statement by using the keyword `data` and listing the constructors with their types in square brackets, separated by bars.  For instance, we can define the booleans:
```
def Bool : Type ≔ data [
| true. : Bool
| false. : Bool
]
```
The `|` before the first constructor is optional, and no spaces are required around the brackets and bar (unless, as usual, they are adjacent to a notation involving other special ASCII symbols).

Note that each constructor ends with a period.  This is intentionally dual to the fact that record fields and codata methods (see below) *begin* with a period, and reminds us that constructors, like fields and records, are not namespaced but belong to a separate flat name domain.  (OCaml programmers should think of polymorphic variants, not regular variants, although there is no subtyping yet.)  The use of separate syntax distinguishing constructors from variables and functions is also familiar from functional programming, although the specific use of a dot suffix is novel (capitalization is more common).

Also as with record types, this is not defining `Bool` to equal a pre-existing thing, but declaring it to be a new type that didn't previously exist and doesn't reduce to anything else.

Datatypes can have parameters:
```
def Sum (A B : Type) : Type ≔ data [
| inl. : A → Sum A B
| inr. : B → Sum A B
]
```
As with records, this is equivalent to
```
def Sum : Type → Type → Type ≔ A B ↦ data [
| inl. : A → Sum A B
| inr. : B → Sum A B
]
```
When there are parameters, the output type must be the datatype applied to those same parameters.

The arguments of each constructor can also be written as parameters before its colon:
```
def Sum (A B : Type) : Type ≔ data [
| inl. (a : A) : Sum A B
| inr. (b : B) : Sum A B
]
```
When all the arguments (if any) are written this way, the output type can be omitted since we know what it must be (the datatype being defined):
```
def Sum (A B : Type) : Type ≔ data [
| inl. (a : A)
| inr. (b : B)
]
```

Datatypes can be recursive, meaning the inputs of a constructor can involve the datatype itself.  For instance, we have the natural numbers:
```
def ℕ : Type ≔ data [
| zero.
| suc. (_ : ℕ)
]
```
and the type of lists:
```
def List (A:Type) : Type ≔ data [
| nil.
| cons. (x : A) (xs: List A)
]
```
For consistency, such occurrences should be strictly positive, but this is not yet checked.  The parameters of a recursive datatype can be "non-uniform", meaning that occurrences of the datatype in the inputs of a constructor (as opposed to the output) can be applied to different parameters.

A datatype can have zero constructors, yielding an empty type:
```
def ∅ : Type ≔ data [ ]
```

Finally, a datatype can also have *indices*, which are arguments of its type that are not abstracted over (either as parameters or after the ≔) before issuing the `data` keyword.  In this case, all the constructors must include an explicit output type that specifies the values of the indices for that constructor (and also includes all the parameters explicitly, although these cannot differ between constructors).  For instance, we have vectors (length-indexed lists):
```
def Vec (A:Type) : ℕ → Type ≔ data [
| nil. : Vec A zero.
| cons. : (n:ℕ) → A → Vec A n → Vec A (suc. n)
]
```
As always for parameters of `def`, this is equivalent to 
```
def Vec : Type → ℕ → Type ≔ A ↦ data [
| nil. : Vec A zero.
| cons. : (n:ℕ) → A → Vec A n → Vec A (suc. n)
]
```
In particular, in the latter case `A` is still a parameter in the datatype sense, even though it does not appear to the left of the typing colon for `Vec`, because it is abstracted over before the `data` keyword.

The other classic example of a datatype with an index is the "Jdentity" type, in either Martin-Löf style:
```
def Jd (A:Type) : A → A → Type ≔ data [
| rfl. (a:A) : Jd A a a
]
```
or Paulin-Möhring style:
```
def Jd (A:Type) (a:A) : A → Type ≔ data [
| rfl. : Jd A a a
]
```


### Applying constructors

A constructor, meaning an identifier ending with a period but containing no internal periods, can be applied to some number of arguments like a function, and then typechecked at a datatype that contains such a constructor.  For instance, `zero.` and `suc. zero.` and `suc. (suc. zero.)` all typecheck at `ℕ`.

Constructors check rather than synthesizing.  As usual with checking terms, one constructor application can check at many different datatypes.  As a simple and common example, `nil.` typechecks at `List A` for *any* type `A`.  This makes it clear that, unlike an ordinary function application, a constructor application cannot synthesize, as there is no way to guess from `nil.` what the type `A` should be.  Moreover, unlike in some other languages, the parameter `A` is not even an "implicit argument" of the constructor; the only way to make `nil.` synthesize is to ascribe it as `nil. : List A`.  Similarly, `inl. a` typechecks at `Sum A B` for any type `B`.

Constructors must always be applied to all of their arguments.  For instance, one cannot write `cons. x : List A → List A`.  You have to η-expand it: `(xs ↦ cons. x xs) : List A → List A`.


### Numeral and list notations

Natural number literals such as `0`, `7`, and `23` are expanded at parse time into applications of the constructors `suc.` and `zero.`.  There is no built-in datatype with these constructors, but of course the user can define `ℕ` as above, in which case for instance `3 : ℕ` is equivalent to `suc. (suc. (suc. zero.))`.  But numerals will also typecheck at any other datatype having constructors of the same name.

There is a similar syntax for lists that expands to applications of the constructors `nil.` and `cons.`: a list like `[> x, y, z >]` expands to `cons. x (cons. y (cons. z nil.))`.  Thus this typechecks at `List A`, as defined above, if `x`, `y`, and `z` belong to `A`.

The arrows `>` in the notation indicate that this is a "forwards" list.  There is a dual notation `[< x, y, z <]` for backwards lists that expands to `snoc. (snoc. (snoc. emp. x) y) z`, which therefore typechecks at a type of [backwards lists](https://github.com/RedPRL/ocaml-bwd) defined as
```
def Bwd (A:Type) : Type ≔ data [
| emp.
| snoc. (xs : Bwd A) (x : A)
]
```
(Since `[` and `]` are always their own tokens, it is also possible to put spaces in these notations, such as `[ > 1, 2, 3 > ]`, but this is not recommended.)

### Matching

When a new constant is defined as a function with arguments that belong to datatypes, it can match on such an argument.  For instance, the function that swaps the elements of a binary sum can be written as
```
def Sum.swap (A B : Type) (x : Sum A B) : Sum B A ≔ match x [
| inl. a ↦ inr. a
| inr. b ↦ inl. b
]
```
The `|` before the first branch is optional.  Each branch is determined by one of the constructors of the datatype applied to distinct new "pattern variables" that are then bound in the body of that branch.  The body can then proceed to match again on these variables or on other variables.  For instance, we have associativity of sums:
```
def Sum.assoc (A B C : Type) (x : Sum (Sum A B) C) : Sum A (Sum B C) ≔ match x [
| inl. y ↦ match y [
  | inl. a ↦ inl. a
  | inr. b ↦ inr. (inl. b)
  ]
| inr. c ↦ inr. (inr. c)
]
```
By omitting the keyword `match` and the variable name, it is possible to abstract over a variable and simultaneously match against it (pattern-matching lambda abstraction).  Thus, `Sum.swap` can equivalently be defined as
```
def Sum.swap (A B : Type) : Sum A B → Sum B A ≔ [
| inl. a ↦ inr. a
| inr. b ↦ inl. b 
]
```

However, even with the explicit `match` syntax, it is only possible to match against a *variable*, not an arbitrary term; and matching can only occur at top level in a definition, or inside abstractions, tuples, or other matches (or comatches, see below).  This aligns with the behavior of pattern-matching definitions in Haskell and Agda, although languages such as Coq and ML that have an explicit `match` keyword usually allow matching against arbitrary terms and in arbitrary places in a term.  One advantage of matching against variables only is that then the output type of the function can be refined automatically in each branch without additional annotations.  To match against an arbitrary term, define a helper function.

It is also only possible to match on one argument at a time: the definition of `Sum.assoc` cannot be condensed to have branches like `inl. (inl. a) ↦ inl. a`.  This makes the syntax a little more verbose, but it also eliminates any ambiguity regarding the order in which matching occurs, preventing issues such as those surrounding Agda's `--exact-split` flag.

A function defined by matching can also be recursive, calling itself in each branch.  For instance, we have addition of natural numbers (in one of the possible ways):
```
def ℕ.plus (m n : ℕ) : ℕ ≔ match m [
| zero. ↦ n
| suc. m ↦ suc. (ℕ.plus m n)
]
```
For termination and consistency, the recursive calls should be on structurally smaller arguments.  But currently there is no checking for this, so it is possible to write infinite loops.  In fact this is possible even without matching:
```
def oops : ∅ ≔ oops
```
However, there is coverage-checking: all the constructors of a datatype must be present in the match.  So while you can write infinite loops, your programs shouldn't get stuck.

When matching against a datatype with indices, the indices in the type of the match variable must also be *distinct free variables* that don't occur in any parameters.  Thus, for instance, we can define appending of vectors:
```
def Vec.append (A : Type) (m n : ℕ) (v : Vec A m) (w : Vec A n) : Vec A (ℕ.plus m n) ≔ match v [
| nil. ↦ w
| cons. k a u ↦ cons. (ℕ.plus k n) a (Vec.append A k n u w)
]
```
Here the match against `v` is allowed because the index `m` of its type `Vec A m` is a free variable.  Then in the two branches, that variable `m` is specialized to the index value associated to that constructor, namely `zero.` in the first branch and `suc. k` in the second.  (Note that the body of the second branch typechecks because `ℕ.plus (suc. k) n` reduces to `suc. (ℕ.plus k n)`, which is why we defined addition of natural numbers as we did.  The other addition of natural numbers, by recursion on the second argument, instead matches appending of *backwards* vectors.)

The fact that the indices cannot occur in the parameters prevents us, for instance, from proving Axiom K.  Thus it is even less general than Agda's `--without-K` matching, and hence also ensures consistency with univalence.  In the future we may implement a more general unification-based condition like Agda's.

## Case trees

### Functions defined by case trees

Functions defined by matching do not reduce unless enough of their arguments are constructors to make it all the way through all the matches.  For instance, `Sum.swap x` does not reduce unless `x` is a constructor, and similarly for `Sum.assoc (inl. x)`.  Thus, functions defined by matching are not equal to each other even if their definitions are identical.  For instance, if we define
```
def neg : Bool → Bool ≔ [ true. ↦ false. | false. ↦ true. ]
def neg' : Bool → Bool ≔ [ true. ↦ false. | false. ↦ true. ]
```
then `neg` and `neg'` are not convertible.  By η-expansion, when trying to convert them we do automatically introduce a new variable `x` and try to compare `neg x` with `neg' x`, but neither of these terms reduce since `x` is not a constructor.  (In particular, datatypes do not satisfy any kind of η-conversion themselves.)

In fact, there is nothing that these terms *could* reduce to, because `match` is not actually syntax for any kind of *term* at all.  Instead, it represents a node in a *case tree*.  A case tree is built out of abstractions, matches, and tuples (and comatches, see below), eventually reaching ordinary terms in the innermost bodies.  In fact *every* defined constant in Narya is actually defined to equal a case tree, which in degenerate cases might only consist of some abstractions or even only a single body.  The general rule, subsuming the others mentioned above for abstractions, tuples, and matching, is that a constant defined as a case tree does not reduce to anything until it is applied to enough arguments or field projections, and enough of the arguments are constructor forms, to ensure that it can reduce to one of the innermost body terms.

The fact that abstractions and tuples (unlike matches) *can* also occur at arbitrary positions in a term means that there is some potential ambiguity in a definition containing only those: are they part of the case tree, or part of a unique body term?  The rule to resolve this is that the case tree includes *as much as possible*; this gives rise to the rules for reduction of functions and tuples mentioned above.

This is usually what you want.  It more or less aligns with the behavior of functions defined by pattern-matching in Agda, whereas Coq has to mimic it with `simpl nomatch` annotations.  However, if you really want to define a constant that reduces to an abstraction before it receives an argument, or a tuple before a field is projected out, you can wrap it in a no-op redex:
```
def swap (A B : Type) : A × B → B × A ≔
  ((x ↦ x) : (A × B → B × A) → (A × B → B × A)) (u ↦ (u .snd, u .fst))
```
Since a function application cannot be part of a case tree, it goes into the body term, including the abstraction over `u`.  Thus `swap A B` will reduce to `u ↦ (u .snd, u .fst)`.  If there is significant demand for it, we may implement a less kludgy way to force an abstraction or tuple to lie in the body rather than the case tree.

Note that case trees are generally considered the internal implementation of Agda-style pattern-matching definitions.  The philosophy of Narya is that it is better to expose the case tree to the user explicitly.  Sometimes this makes the code more verbose; but other times it actually makes it more concise, since all the arguments of the function no longer have to be written again in every branch and sub-branch.  But more importantly, the order in which matches are performed, and hence the way in which the function actually computes, is this way obvious to the reader, and can be specified explicitly by the programmer.  So we have no plans to implement Agda-style pattern matching syntax.


### Canonical types defined by case trees

By a *canonical type* we mean a universe, function-type, record type, datatype, or codatatype (see below), of which the first two are built in and the latter three are all user-defined.  So far, all our definitions of new canonical types (record types and datatypes) may have been abstracted over parameters, but otherwise the keyword `sig` or `data` has occurred immediately after the ≔.

However, in fact a canonical type declaration can appear anywhere in a case tree!  For example, here is another definition of length-indexed lists, which we call "covectors".  Now instead of the length being an index, it is a *parameter* over which we recurse:
```
def Covec (A:Type) (n:ℕ) : Type ≔ match n [
| zero. ↦ sig ()
| suc. n ↦ sig (
  car : A,
  cdr : Covec A n
)]
```
Thus, `Covec A 0` is a unit type, `Covec A 1` is isomorphic to `A` (definitionally! since record types have η-conversion), `Covec A 2` is isomorphic to `A × A`, and so on.

This is very similar, but subtly different from, the following definition that could be given in Coq or Agda:
```
def Covec' (A:Type) (n:ℕ) : Type ≔ match n [
| zero. ↦ ⊤
| suc. n ↦ A × Covec' A n
]
```
The two are definitionally isomorphic.  The difference is that `Covec' A n` reduces when `n` is a constructor, while `Covec A n` is already a canonical type no matter what `n` is; it's just that when `n` is a constructor we know how it *behaves*.  For instance, `Covec' A 2` reduces to `A × (A × ⊤)`, whereas `Covec A 2` does not reduce but we can still typecheck `(a, (b, ()))` at it.  This sort of "recursively defined canonical type" helps maintain information about the meaning of a type, just like using a custom record type rather than a nested Σ-type; eventually we hope it will be helpful for unification and typeclass inference.

As another example, once we have an identity type `Id` (which could be `Jd`) we can define the homotopy-theoretic tower of truncation levels:
```
def trunc_index : Type ≔ data [ minustwo. | suc. (_ : trunc_index) ]

def IsTrunc (n:ℕ) (A:Type) : Type ≔ match n [
| minustwo. ↦ sig ( center : A, contr : (x:A) → Id A center x )
| suc. n ↦ sig ( trunc_id : (x y : A) → IsTrunc n (Id A x y) )
]
```

### Holes in case trees

A hole `?` left in a place where a case tree would be valid to continue is a "case tree hole", and is treated a bit differently than an ordinary hole.  Obviously, once it is possible to "fill" holes, a case tree hole will be fillable with a case tree rather than just a term.  But currently, the main difference is that evaluation of a function does not reduce when it reaches a case tree hole, and thus a case tree hole will never appear when printing terms: instead the function in which it appears as part of the definition.  This may be a little surprising, but it has the advantage of being a re-parseable notation, and also explicitly indicating all the arguments of the function (which would be the substitution applied to a term hole, and hence not currently printed).


## Codatatypes and comatching

A *codatatype* is superficially similar to a record type: it has a list of fields (which in this case we sometimes call *methods*), each with a type, which are projected out (or "called") using the same syntax `x .method`.  The primary differences are:

1. Codatatypes can be (co)recursive: the output type of each method can involve the codatatype itself.  (Such occurrences ought to be strictly positive, but currently there is no check for that.  In fact, there is not yet even a check that rules out recursion in record types, but there will be.)
2. Codatatypes do not satisfy η-conversion (this being undecidable in the recursive case).
3. To emphasize these differences, the syntax for defining codatatypes and their elements (the latter called "comatching") is more akin to that of datatypes and pattern-matching than to that of records and tuples.

### Defining codatatypes

Here is a corecursive definition of the codatatype of infinite streams:
```
def Stream (A:Type) : Type ≔ codata [
| x .head : A
| x .tail : Stream A
]
```
That is, we use brackets and bars instead of parentheses and commas.  Moreover, instead of writing field names like variables as in a record type, we write them as method calls *applied to a variable*.  This variable is then bound in the body to belong to the codatatype, and the values of previous fields are be accessed through it.  For instance, a codata version of Σ-types would be written
```
def codata-Σ (A : Type) (B : A → Type) : Type ≔ codata [
| x .fst : A
| x .snd : B (x .fst)
]
```

It is often helpful to think of a codatatype as akin to an *interface* in an object-oriented programming language, in which case the variable `x` is like the `this` or `self` pointer by which an object refers to itself.  Of course an interface in a simply-typed language does not need a self-pointer to specify the *types* of its methods, but in a dependently typed language it does.  In higher-dimensional type theories, the presence of this variable can be used in other ways than simply accessing previously declared methods, such as in the coinductive definition of semi-simplicial types (see below).

### Copattern matching

Elements of coinductive types are introduced by comatches, which are like tuples except for the syntax and the fact that they can be (co)recursive:
```
def Fibonacci (a b : ℕ) : Stream ℕ ≔ [
| .head ↦ a
| .tail ↦ Fibonacci b (ℕ.plus a b)
]
```
In addition, unlike tuples, comatches are a part of case trees but not of ordinary terms.  Thus, they never evaluate to anything until a method is called.  This is essential to ensure termination in the presence of corecursion; otherwise `Fibonacci 1 1` would spin forever computing the entire infinite sequence.  (It is also why codatatypes do not have [η-conversion](http://strictlypositive.org/Ripley.pdf).)  It is often helpful to think of a constant defined by comatching as an ([immutable](https://dev.realworldocaml.org/objects.html)) *object* implementing an interface, with the parameters of that constant being its "private member variables".

(As a bit of syntactic trivia, note that `[]` is ambiguous: it could denote either a pattern-matching lambda on a datatype with no constructors, or a copattern-match into a codatatype with no methods.  Fortunately, since both possibilities are checking rather than synthesizing, the ambiguity is resolved by bidirectional typechecking.)


## Mutual definitions

A block of constants can be defined mutually.  This means that first all of their *types* are checked, in order, so that the types of later constants in the block may refer to earlier constants (but using only their types, not their definitions).  Then their definitions are checked, again in order, so that the definitions of later constants may use the definitions of earlier ones (as well as the types of arbitrary ones).  Because datatypes are just a kind of definition, the same syntax for mutual definitions encompasses mutually recursive functions, mutually inductive types, inductive-inductive types, and even inductive-recursive types and functions.  Furthermore, all these kinds of mutual definitions can be encoded as single definitions using record-types (but the explicit mutual syntax is usually more congenial).

The syntax for a mutual block of definitions looks just like a sequence of ordinary `def` commands, except that the second and later ones use the keyword `and` instead of `def`.  This is similar to the syntax of ML-like programming languages and Coq, and in contrast to Agda's style in which declarations and definitions can be mixed arbitrarily as long as each constant is declared before it is defined.  We prefer to keep the declaration of the type of each constant next to its definition, and make it clear textually which blocks of constants are defined mutually, at the price of allowing the definition of a constant to refer to others whose type is declared later textually in the same block.

An entire mutual block constitutes a single command, since it is impossible to typecheck any part of it individually.  It is nevertheless usual to put a blank line in between the definitions in a mutual block, although note that this cannot be done in interactive mode since a blank line ends the command.

Like any definition, the constants in a mutual block can be defined using the synthesizing form of `def` that omits their type.  However, this is of limited usefulness, since then they cannot be used while typechecking other constants in the block, as their types are not yet known at that point.

We now give a few examples to illustrate the possibilities of mutual definitions, along with their encodings using records.


### Mutual recursion

We can define the Boolean predicates `even` and `odd` on the natural numbers:
```
def even : ℕ → Bool ≔ [
| zero.  ↦ true.
| suc. n ↦ odd n
]

and odd : ℕ → Bool ≔ [
| zero.  ↦ false.
| suc. n ↦ even n
]
```
Thus, for instance, `even 4` reduces to `true.`

Encoded as a single definition, this looks like the following.
```
def even_odd : (ℕ → Bool) × (ℕ → Bool) ≔ (
  [ zero. ↦ true.  | suc. n ↦ even_odd .1 n ],
  [ zero. ↦ false. | suc. n ↦ even_odd .0 n ])
```
Here we have used a binary product type, but in more complicated cases when doing such encoding, it may be helpful to define a custom record-type first in which the bundled family of mutually recursive functions lives.


### Mutual induction

The Type-valued predicates `Even` and `Odd` can be defined similarly:
```
def Even : ℕ → Type ≔ data [
| even_zero. : Even zero.
| even_suc. : (n:ℕ) → Odd n → Even (suc. n)
]

and Odd : ℕ → Type ≔ data [
| odd_suc. : (n:ℕ) → Even n → Odd (suc. n)
]
```
Now `Even 4` doesn't reduce to anything, but it belongs to an indexed inductive type family, and can be inhabited by the term `even_suc. 3 (odd_suc. 2 (even_suc. 1 (odd_suc. 0 even_zero.)))`.

The fact that canonical type declarations can appear as part of case trees means that these can also be encoded as a single definition:
```
def Even_Odd : (ℕ → Type) × (ℕ → Type) ≔ (
  data [
  | even_zero. : Even_Odd .0 zero.
  | even_suc. : (n:ℕ) → Even_Odd .1 n → Even_Odd .0 (suc. n) ],
  data [
  | odd_suc. : (n:ℕ) → Even_Odd .0 n → Even_Odd .1 (suc. n) ])
```

Recall that in Narya a third possibility is a recursive definition of families of canonical types:
```
def Even' : ℕ → Type ≔ [
| zero. ↦ sig ()
| suc. n ↦ sig (even_suc : Odd' n)
]
and Odd' : ℕ → Type ≔ [
| zero. ↦ data []
| suc. n ↦ sig (odd_suc : Even' n)
]
```
In this case, `Even' 4` doesn't reduce to anything, but it is definitionally a singleton, with unique inhabitant `(_ ≔ (_ ≔ (_ ≔ (_ ≔ ()))))`.


### Inductive-inductive families

Here is a definition of the bare bones of the syntax of type theory (contexts and types) that often appears as an example of induction-induction:
```
def ctx : Type ≔ data [
| empty.
| ext. (Γ : ctx) (A : ty Γ)
]

and ty (Γ : ctx) : Type ≔ data [
| base.
| pi. (A : ty Γ) (B : ty (ext. Γ A))
]
```
Note that the context Γ is a non-uniform parameter of the datatype `ty`.  And its encoding:
```
def ctx_ty : Σ Type (X ↦ (X → Type)) ≔ (
  ctx ≔ data [
  | empty.
  | ext. (Γ : ctx_ty .0) (A : ctx_ty .1 Γ) ],
  ty ≔ Γ ↦ data [
  | base.
  | pi. (A : ctx_ty .1 Γ) (B : ctx_ty .1 (ext. Γ A)) ])
```


### Inductive-recursive definitions

Finally, because a case tree can include canonical type declarations in some branches and ordinary (co)recursive definitions in other branches, we can also encode inductive-recursive definitions.  For instance, here is an inductive-recursive universe that contains the Booleans and is closed under Π-types:
```
def uu : Type ≔ data [
| bool.
| pi. (A : uu) (B : el A → uu)
]

and el : uu → Type ≔ [
| bool. ↦ Bool
| pi. A B ↦ (x : el A) → el (B x)
]
```
and its encoding:
```
def uu_el : Σ Type (X ↦ (X → Type)) ≔ (
  uu ≔ data [
  | bool.
  | pi. (A : uu_el .0) (B : uu_el .1 A → uu_el .0) ],
  el ≔ [
  | bool. ↦ Bool
  | pi. A B ↦ (x : uu_el .1 A) → uu_el .1 (B x) ])
```


### Here be dragons

As can be seen from these examples, Narya's facility for mutual definitions is comparable to Agda's in flexibility and power.  Also like Agda, Narya currently permits even more radical things such as nested datatypes:
```
def Bush (A:Type) : Type ≔ data [
| leaf.
| cons. (_ : A) (_ : Bush (Bush A))
]
```
and poorly understood things such as mutual families of definitions including both inductive and coinductive types and both recursive and corecursive functions.  As noted above, we have not yet implemented positivity, termination, or productivity checkers, so it is easy to create inconsistencies even without these more radical features.  Eventually, we intend the default to be a "safe mode" that restricts mutual definitions to combinations that are known to be consistent and have understood semantics, although this could be turned off by a flag.


## Parametric Observational Type Theory

There are many ways in which a type theory can be "higher-dimensional", by which we include homotopy type theory (specifically, Higher Observational Type Theory), internally parametric type theories, and [displayed type theory](https://arxiv.org/abs/2311.18781).  The internal architecture of Narya is set up to eventually permit the user to mix and match multiple such "directions" of higher-dimensionality, but currently this is not realized.  At the moment, therefore, there is only one built-in direction, although its behavior is somewhat customizable.  We will first describe the current default behavior of this direction, which is *binary internal parametricity*, and then how it can be modified.

### Identity/bridge types of canonical types

Every type `A` has a binary identity/bridge type denoted `Id A x y`, and each term `x:A` has a reflexivity term `refl x : Id A x x`.  (The argument of `refl` must synthesize.)  There is no "transport" for these types (hence "bridge" is really a more appropriate name).  But they are "observational" in the sense that the identity/bridge type of a canonical type is another canonical type of the same sort.

For example, `Id (A → B) f g` is a function-type `(x₀ x₁ : A) (x₂ : Id A x₀ x₁) → Id B (f x₀) (g x₁)`.  In particular, `refl f` is a function of a type `(x₀ x₁ : A) (x₂ : Id A x₀ x₁) → Id B (f x₀) (f x₁)`, witnessing that all functions preserve "equalities" or "relatedness".  Thus the operation traditionally denoted `ap` in homotopy type theory is just `refl` applied to a function (although since the argument of `refl` must synthesize, if the function is an abstraction it must be ascribed).  Similarly, `Id (A × B) u v` is a type of pairs of identities, so if we have `p : Id A (u .fst) (v .fst)` and `q : Id B (u .snd) (v .snd)` we can form `(p,q) : Id (A × B) u v`, and so on for other record types, datatypes, and codatatypes.

However, in Narya `Id (A → B) f g` does not *reduce* to the *ordinary* function-type `(x₀ x₁ : A) (x₂ : Id A x₀ x₁) → Id B (f x₀) (g x₁)`: instead it simply *behaves* like it, in the sense that its elements can be applied like functions and we can define elements of its as abstractions.  This should be compared with how `Covec A 2` doesn't reduce to `A × (A × ⊤)` but behaves like it in terms of what its elements are and what we can do with them.  In particular, `Id (A → B) f g` and `(x₀ x₁ : A) (x₂ : Id A x₀ x₁) → Id B (f x₀) (g x₁)` are definitionally isomorphic, with the functions in both directions being η-expansions `f ↦ (x₀ x₁ x₂ ↦ f x₀ x₁ x₂)`.  For most purposes this behavior is just as good as a reduction, and it retains more information about the type, which, as before, is useful for many purposes.  (In fact, with our current understanding, it appears to be *essential* for Narya's normalization and typechecking algorithms.)

The same is true for other canonical types, e.g. `Id (A × B) u v` does not reduce to `Id A (u .fst) (v .fst) × Id B (u .snd) (v .snd)`, but it is *a* record type that is definitionally isomorphic to it.  Similarly, identity types of codatatypes behave like types of bisimulations: `Id (Stream A) s t` is a codatatype that behaves as if it were defined by
```
codata [
| _ .head : Id A (s .head) (t .head)
| _ .tail : Id (Stream A) (s. tail) (t .tail)
]
```
Individual bisimulations, i.e. elements of `Id (Stream A) s t`, can then be constructed by comatching and corecursion.

In general, the fields, constructors, or methods of the identity/bridge type of a record type, datatype, or codatatype have the *same names* as those of the original type, and their types are the identity/bridge types of those of the original.

In the case of datatypes, the boundary (endpoints) of the identity/bridge type behave like *indices*.  Thus, for instance, `Id ℕ` behaves like an indexed datatype defined by
```
data [
| zero. : Id ℕ zero. zero.
| suc. : (n₀ n₁ : ℕ) (n₂ : Id ℕ n₀ n₁) → Id ℕ (suc. n₀) (suc. n₁)
]
```


### Identity/bridge types of the universe

According to internal parametricity, we morally think of `Id Type A B` as being the type `A → B → Type` of correspondences.  (We avoid the word "relation" since it erroneously suggests proposition-valued.)  However, according to the above principles, we should expect `Id Type A B` to only *behave* like `A → B → Type`, in that we can apply its elements to a pair of arguments in `A` and `B` to get a type, and define its elements by similarly abstracting.

The first is literally true: given `R : Id Type A B` and `a:A`, `b:B` we have `R a b : Type`.  We refer to this as *instantiating* the higher-dimensional type `R`.  In fact, `Id A x y` itself is an instantiation, as we have `Id A : Id Type A A`, which moreover is really just a notational variant of `refl A`.

For the second there is another wrinkle: we can define elements of `Id Type A B` by abstracting, but the body of the abstraction must be a *newly declared canonical type* rather than a pre-existing one.  This also seems to be essential to deal with symmetries (see below) in the normalization and typechecking algorithm.  Moreover, the current implementation allows this body to be a *record type* or *codatatype*, but not a *datatype*, and it does not permit other case tree operations in between such as pattern-matching.

For record types, there is a syntax that reflects this restriction: instead of the expected `x y ↦ sig (⋯)` we write `sig x y ↦ (⋯)`, explicitly binding all the boundary variables as part of the record type syntax.  For example, here is the universal 1-dimensional record type, traditionally called "Gel":
```
def Gel (A B : Type) (R : A → B → Type) : Id Type A B ≔ sig a b ↦ ( ungel : R a b )
```
For codatatypes, we simply use the ordinary syntax, but the "self" variable automatically becomes a cube variable of the appropriate dimension (see below).

We plan to lift this restriction in the future, but in practice it is not very onerous.  For most applications, the above "Gel" record type can simply be defined once and used everywhere, rather than declaring new higher-dimensional types all the time.  Note that because record-types satisfy η-conversion, `Gel A B R a b` is definitionally isomorphic to `R a b`.  Thus, `Id Type A B` contains `A → B → Type` as a "retract up to definitional isomorphism".  This appears to be sufficient for all applications of internal parametricity.  (`Id Type` does not itself satisfy any η-conversion rule.)


### Heterogeneous identity/bridge types

If `B : A → Type`, then `refl B x₀ x₁ x₂ : Id Type (B x₀) (B x₁)`.  Thus, given `y₀ : B x₀` and `y₁ : B x₁`, we can instantiate this identification at them to obtain a type `refl B x₀ x₁ x₂ y₀ y₁`. of *heterogeneous* identifications/bridges relating `y₀` and `y₁` "along" or "over" `x₂`.

Such heterogeneous identity/bridge types are used in the computation (up to definitional isomorphism) of identity/bridge types of *dependent* function types.  Specifically, `Id ((x:A) → B x) f g` acts like a function-type `(x₀ x₁ : A) (x₂ : Id A x₀ x₁) → refl B x₀ x₁ x₂ (f x₀) (g x₁)`.  They also appear in identity/bridge types of other canonical types, such as when one field of a record type depends on previous ones.  For instance, `Id (Σ A B) u v` behaves like a record type
```
sig (
  fst : Id A (u .fst) (v .fst),
  snd : refl B (u .fst) (v .fst) fst (u .snd) (v .snd),
)
```
More generally, since `Σ : (A : Type) (B : A → Type) → Type`, we have `refl Σ` whose type is isomorphic to
```
(A₀ : Type) (A₁ : Type) (A₂ : Id Type A₀ A₁) (B₀ : A₀ → Type) (B₁ : A₁ → Type)
  (B₂ : refl ((X ↦ X → Type) : Type → Type) A₀ A₁ A₂ B₀ B₁)
  (u₀ : Σ A₀ B₀) (u₁ : Σ A₁ B₁) → Type
```
and `refl Σ A₀ A₁ A₂ B₀ B₁ B₂ u₀ u₁` behaves like a record type
```
sig (
  fst : A₂ (u₀ .fst) (u₁ .fst),
  snd : B₂ (u₀ .fst) (u₁ .fst) fst (u₀ .snd) (u₁ .snd),
)
```
Here we have used the fact that the type of `B₂` is similarly isomorphic to
```
(x₀ : A₀) (x₁ : A₁) (x₂ : A₂ x₀ x₁) (y₀ : B₀ x₀) (y₁ : B₁ x₁) → Type
```
The ascription in the type of `B₂` is necessary since the argument of `refl` must synthesize, which abstractions do not.  This can be annoying to write, so an alternative is to use the built-in constant `Π`:
```
B₂ : refl Π A₀ A₁ A₂ (x₀ ↦ Type) (x₁ ↦ Type) (x₀ x₁ x₂ ↦ refl Type) B₀ B₁
```
In particular, this is what Narya uses when printing higher-dimensional function-types (although it also uses cube variables, see below).


### Higher-dimensional cubes and degeneracies

Iterating `Id` or `refl` multiple times produces higher-dimensional cube types and cubes.  For instance, since `Id A` acts like a function `A → A → Type`, *its* identity type or reflexivity type `Id (Id A)` acts as a function-type
```
(x₀₀ : A) (x₀₁ : A) (x₀₂ : Id A x₀₀ x₀₁)
  → (x₁₀ : A) (x₁₁ : A) (x₁₂ : Id A x₁₀ x₁₁)
  → (x₂₀ : Id A x₀₀ x₁₀) (x₂₁ : Id A x₀₁ x₁₁) → Type
```
We can view this as assigning to any boundary for a 2-dimensional square a type of fillers for that square.  Similarly, `Id (Id (Id A))` yields a type of 3-dumensional cubes, and so on.

There is a symmetry operation `sym` that acts on at-least-two dimensional cubes, swapping or transposing the last two dimensions.  Like `refl`, the argument of `sym` must also synthesize, but in this case it must synthesize a "2-dimensional" type.  (The need to be able to "detect" 2-dimensionality here is roughly what imposes the requirements on our normalization/typechecking algorithm mentioned above.)

Combining versions of `refl` and `sym` yields arbitrary higher-dimensional "degeneracies" (from the BCH cube category).  There is also a generic syntax for such degeneracies: `M⁽¹ᵉ²⁾` or `M^(1e2)` where the superscript represents the degeneracy, with `e` denoting a degenerate dimension and nonzero digits denoting a permutation.  (The `e` stands for "equality", since our `Id` is eventually intended to be the identity type of Higher Observational Type Theory.)  In the unlikely event you are working with dimensions greater than nine, you can separate multi-digit numbers and letters with a hyphen, e.g. `M⁽¹⁻²⁻³⁻⁴⁻⁵⁻⁶⁻⁷⁻⁸⁻⁹⁻¹⁰⁾` or `M^(0-1-2-3-4-5-6-7-8-9-10)`.

Degeneracies can be extended by identities on the right.  For instance, the two degeneracies taking a 1-dimensional object to a 2-dimensional one are denoted `1e` and `e1`, and of these `e1` can be written as simply `e` and coincides with ordinary `refl` applied to an object that happens to be 1-dimensional.

Degeneracy operations are functorial.  For pure symmetries, this means composing permutations.  For instance, the "Yang-Baxter equation" holds, equating `M⁽²¹³⁾⁽¹³²⁾⁽²¹³⁾` with `M⁽¹³²⁾⁽²¹³⁾⁽¹³²⁾`, as both reduce to `M⁽³²¹⁾`.  Symmetries also compose with permutations in a fairly straightforward way, e.g. `M⁽ᵉ¹⁾⁽²¹⁾` reduces to `M^⁽¹ᵉ⁾`.

The principle that the identity/bridge types of a canonical type are again canonical types of the same sort applies also to higher degeneracies, with one exception.  Ordinary canonical types are "intrinsically" 0-dimensional, and therefore any operations on them reduce to a "pure degeneracy" consisting entirely of `e`s, e.g. `M⁽ᵉᵉ⁾⁽²¹⁾` reduces to simply `M⁽ᵉᵉ⁾`.  These pure degeneracies of canonical types are again canonical types of the same form, as discussed for `Id` and `refl` above.  However, an intrinsically higher-dimensional canonical type like `Gel` admits some degeneracies that permute the intrinsic dimension with some of the additional dimensions; the simplest of these is `1e`.  These degeneracies of a higher-dimensional canonical type are *not* any longer canonical; but they are isomorphic to a canonical type by the action of a pure symmetry.  For instance, `(Gel A B R a b)⁽¹ᵉ⁾` is not canonical, and in particular not a record type, so given `M : (Gel A B R a b)⁽¹ᵉ⁾` you cannot write `M .ungel`.  But we do have `M⁽²¹⁾ : (Gel A B R a b)⁽ᵉ¹⁾`, which doesn't permute the intrinsic dimension `1` with the degenerate dimension `e` and is therefore a record type, and so you can write `M⁽²¹⁾ .ungel`.


### Cubes of variables

Since there is no unifier and no implicit arguments yet, all the arguments of higher-dimensional cubes and functions must be given explicitly.  However, there is a shorthand syntax for higher-dimensional abstractions: instead of `x₀ x₁ x₂ ↦ M` you can write `x ⤇ M` (or `x |=> M` in ASCII).  This binds `x` as a "family" or "cube" of variables whose names are suffixed with face names in ternary notation: `x.0` and `x.1` and `x.2`, or in higher dimensions `x.00` through `x.22` and so on.  (The dimension is inferred from the type at which the abstraction is checked.)  Note that this is a *purely syntactic* abbreviation: there is no object "`x`", but rather there are really *three different variables* that just happen to have the names `x.0` and `x.1` and `x.2`.  (There is no potential for collision with user-defined names, since ordinary local variable names cannot contain internal periods.  Of course, `x.0` can shadow a global definition of a constant `0` in namespace `x`.)

These "cube variables" also appear automatically when matching against a higher-dimensional version of a datatype.  For instance, we can do an encode-decode proof for the natural numbers by matching directly on `Id ℕ` (using pattern-matching abstractions):
```
def code : ℕ → ℕ → Type ≔
[ zero. ↦ [ zero. ↦ sig ()
          | suc. n ↦ data [] ]
| suc. m ↦ [ zero. ↦ data []
           | suc. n ↦ sig ( uncode : code m n ) ]]

def decode : (m n : ℕ) → code m n → Id ℕ m n ≔
[ zero. ↦ [ zero. ↦ _ ↦ zero.
          | suc. n ↦ [] ]
| suc. m ↦ [ zero. ↦ []
           | suc. n ↦ p ↦ suc. (decode m n (p .0)) ]]

def encode (m n : ℕ) : Id ℕ m n → code m n ≔
[ zero. ↦ ()
| suc. p ↦ (_ ≔ encode p.0 p.1 p.2)]
```
Here in the definition of `encode`, the pattern variable `p` of the `suc.` branch is automatically made into a 1-dimensional cube of variables since we are matching against an element of `Id ℕ`, so in the body we can refer to `p.0`, `p.1`, and `p.2`.  In the future, we may implement a dual syntax for simultaneously *applying* a function to a whole cube of variables of this sort as well.

Similarly, when defining a codatatype lying in a higher universe, the "self" variable automatically becomes a cube variable, so that the boundary of the type is accessible through its faces.  For instance, here is a codatatype version of Gel:
```
def Gel (A B : Type) (R : A → B → Type) : Id Type A B ≔ codata [ x .ungel : R x.0 x.1 ]
```


### Varying the behavior of parametricity

The parametricity described above, which is Narya's default, is *binary* in that the identity/bridge type `Id A x y` takes *two* elements of `A` as arguments.  However, a different "arity" can be specified with the `-arity` command-line flag.  For instance, under `-arity 1` we have bridge types `Id A x`, and under `-arity 3` they look like `Id A x y z`.  Everything else also alters according, e.g. under `-arity 1` the type `Id (A → B) f` is isomorphic to `(x : A) (x' : Id A x) → Id B (f x)`, and a cube variable has pieces numbered with only `0`s and `1`s.

In principle, the arity could be any natural number, but for syntactic reasons Narya currently requires it to be between 1 and 9 inclusive.  The problem with arities greater than 9 is that the syntax `x.10` for cube variables would become ambiguous: does `10` mean "one-zero" or "ten"?  But if you have an application of such a type theory, let us know and we can work out a syntax (although at present we are unaware of any applications of n-ary parametricity for n>2).  The problem with arity 0 is that then `Id A` would belong to `Id Type` and also be instantiatable to an element of `Type`, but since this requires no arguments it's not clear what syntax should indicate whether the instantiation has happened.  We do expect to solve this problem somehow, since 0-ary parametricity does have potential applications (it is related to nominal type theory).

It is also possible to rename or remove the primitives `refl` and `Id` (which, recall, is just another notation for `refl`), as well as change the letter `e` used in generic degeneracies.  The default behavior is equivalent to the command-line argument `-direction e,refl,Id`; in general the argument of `-direction` is a comma-separated list of names, where the first must be a single lowercase letter to be used in generic degeneracies, and the others (if any) are names for the basic degeneracy.  For instance, in unary parametricity we might write `-arity 1 -direction r,red` and think of `red x` as "`x` is reducible".

The name of `sym` cannot be changed or removed, and likewise for the digits used in generic degeneracies to indicate permuted dimensions.

Finally, parametricity can be set to be *internal* (the default) or *external*.  Setting it to external instead means that dimension-changing degeneracies (including `refl`, but not `sym`) can only be applied to *closed terms*.  Since degeneracies also compute fully on closed terms (at least in the "up-to-definitional-isomorphism" sense), we can then more or less think of these operations as meta-operations on syntax rather than intrinsic aspects of the theory.  This is the usual meaning of "external parametricity", although Narya's is of course at least partially internalized.  (Semantically, what Narya calls "external parametricity" is modeled in a diagram of *semi-cubical* types, in contrast to internal parametricity which is modeled in *cubical* types.)

In addition, under external parametricity, *axioms* are not permitted to be used inside of dimension-changing degeneracies either.  The reasoning behind this is that we may want to assume axioms that are inconsistent with parametricity, such as excluded middle, while still making use of external parametricity on other types.  (Note that *internal* parametricity is nonclassical, actively contradicting excluded middle.)  It also maintains the principle that assuming an axiom of type `A` is equivalent to working in a context extended by a variable of type `A`.  However, in the future it may be possible to declare a special kind of "parametric axiom" that does have higher-dimensional versions.

The combination `-arity 1 -direction d -external` is a version of [displayed type theory](https://arxiv.org/abs/2311.18781) (dTT), and as such can be selected with the single option `-dtt`.  The primary differences between `narya -dtt` and the original dTT of the paper are:

1. Narya currently has no modalities, so display can only be applied to closed terms rather than to the more general □-modal ones.
2. Narya has symmetries, which in particular (as noted in the paper) makes `SST⁽ᵈ⁾` (see below) actually usable.
3. As noted above, display in Narya computes only up to isomorphism, and in the case of `Type` only up to retract up to isomorphism.
4. (A syntactic difference only) Generic degeneracies in Narya must be parenthesized, so we write `A⁽ᵈ⁾` instead of `Aᵈ`.

### Higher datatypes and codatatypes

There are many possible kinds of datatypes and codatatypes that make use of higher-dimensional structure.  Narya does not yet implement Higher Inductive Types, in which the output of a constructor can be a higher-dimensional version of the datatype, nor the dual sort of "higher coinductive type" in which the *input* of a method is a higher-dimensional version of the codatatype.  However, it does permit the *displayed coinductive types* of dTT and their generalization to other kinds of parametricity, in which the *output* of a corecursive *method* is a higher-dimensional version of the codatatype.  This permits, for example, the definition of the type of semi-simplicial types from the dTT paper:
```
def SST : Type ≔ codata [
| X .z : Type
| X .s : (X .z) → SST⁽ᵈ⁾ X
]
```


## Remarks on implementation

As is common for normalization-by-evaluation, the implementation uses De Bruijn *indices* for syntactic terms and De Bruijn *levels* for semantic values.  A little more unusually, however, the De Bruijn indices are "intrinsically well-scoped".  This means that the type of terms is parametrized by the length of the context (as a type-level natural number, using GADTs), so that the OCaml compiler ensures *statically* that De Bruijn indices never go out of scope.  Other consistency checks are also ensured statically in a similar way, such as the matching of dimensions for certain types and operators, and scoping and associativity for notations.  (The latter is the reason why tightnesses are dyadic rationals: they are represented internally as type-level finite surreal-number sign-sequences, this being a convenient way to inductively define a dense linear order.)

This approach does have the drawback that it requires a fair amount of arithmetic on the natural numbers to ensure well-typedness, which is not only tedious but some of it also ends up happening at run-time.  Since type-level natural numbers are represented in unary, this could be a source of inefficiency in the future.  However, it has so far proven very effective at avoiding bugs!

Another interesting tool used in the implementation is a technique for writing generic traversal functions for data structures.  With heterogeneous type-indexed lists, we can write a single traversal function that can be called with arbitrarily many data structures as input and arbitrarily many as output, thus including in particular `map`, `map2`, `iter` (the 0-output case), `iter2`, and so on.  If this generic traversal is parametrized over a monad, or more generally an applicative functor, then it also includes both left and right folds, possibly combined with maps, and so on.  For a simple data structure like lists this is overkill, of course, but for some of the complicated data structures we use (like n-dimensional cubes that are statically guaranteed to have exactly the right number of elements, accessed by giving a face) it saves a lot of work to be able to implement only one traversal.

The source code is organized in directories as follows:

* [lib/](lib/): Most of the code
  * [lib/util/](lib/util/): Utilities that could in principle be generic libraries
  * [lib/dim/](lib/dim/): Definition of the dimension theory (cube category)
  * [lib/core/](lib/core/): Syntax, normalization, type-checking, etc.
  * [lib/parser/](lib/parser/): Parsing and printing
* [bin/](bin/): The main executable
* [test/](test/): Unit tests
  * [test/testutil/](test/testutil/): Utilities used only for white-box testing
  * [test/white/](test/white/): White-box tests of the core
  * [test/parser/](test/parser/): White-box tests of parsing and printing
  * [test/black/](test/black/): Black-box tests of the executable
