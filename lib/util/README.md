# Utilities for Narya

This directory contains a number of utilities used in Narya that in principle could be generic libraries.  Many of them are inspired by the following fundamental ideas.

1. As much as can be statically ensured should be.  This means we take advantage of OCaml's features like GADTs to approximate dependent types, e.g. by defining a type-level notion of natural numbers and using it to index the lengths of lists ("vectors") statically.  We also implement lists *of types* as additional types, which can then be used to index "heterogeneous lists", as well as type-level dyadic rationals (a convenient dense linear ordering).

1. Respect the textual order.  This comes from the library [Bwd](https://github.com/redPRL/ocaml-bwd).  We take it to an extreme with forward and backward lists of types, forward and backward vectors, and even forward and backward natural numbers!

1. Unify all kinds of traversals.  With a trick involving heterogeneous lists, it is possible to define a single generic traversal function for a data structure, which can then be specialized to a map, a left or right fold, or an iterator of arbitrarily many inputs and outputs.  (This is particularly useful for more complicated data structures defined elsewhere in the library; the instances defined here are mainly for demonstration.)

1. Remain purely functional as much as possible.  In particular, nothing in this directory produces any side effects.  We instead incorporate monads in appropriate places, e.g. in the generic traversal functions.

Here is a listing of the files in this directory, as of May 2, 2024, with brief descriptions:

## Generic utilities

- [List_extra](list_extra.ml): Extra utility functions involving (forward) lists
- [Bwd_extra](bwd_extra.ml): Extra utility functions involving bwds (backward lists)
- [Abwd](abwd.ml): Backward association lists, i.e. bwds of pairs used to look up their first element and return their second element.  Use instead of Map when retaining the order of entries matters.
- [Signatures](signatures.ml): Module types for intrinsically well-typed maps.
- [Monad](monad.ml): Module signatures and implementations for monads and monadic operations.
- [Applicative](applicative.ml): Similarly, signatures and implementations for applicative (a.k.a. lax monoidal) functors.
- [Sorry](sorry.ml): A generic way to leave a "hole" in an unfinished function and still allow the file to compile (but throw an exception when executed).

## Generic traversals

- [Mlist](mlist.ml): An illustration of the generic traversal method in the case of lists, where it is fairly unnecessary.
- [Mbwd](mbwd.ml): Another illustration in the case of bwds.  We sometimes use this in place of the library-supplied `Bwd.map` since ours iterates in textual order from left to right.

## Type-level arithemtic

- [Eq](eq.ml): Type equality.
- [Monoid](monoid.ml): Module signatures for type-level monoids.
- [N](n.ml): Type-level natural numbers.
- [Fwn](fwn.ml): Type-level "forward" natural numbers.  We call the usual ones "backward" because they are the natural lengths of backward lists, while the forward ones are the natural lengths of forward lists.  (The difference is in which argument the definition of addition recurses on.)
- [Nmap](nmap.ml): Intrinsically well-typed maps over `N`.
- [No](no.ml): Type-level dyadic rationals plus ±ω, represented as surreal numbers, including an intrinsically well-typed map.
- [Word](word.ml): Type-level free monoids on an arbitrary set of generators, including an intrinsically well-typed map.

## Lists and vectors

- [Tlist](tlist.ml): Forward lists of types
- [Tbwd](tbwd.ml): Backward lists of types
- [Hlist](hlist.ml): Heterogeneous (forward) lists, indexed by a tlist.
- [Vec](vec.ml): Forward lists indexed by a forward natural number length ("vectors")
- [Bwv](bwv.ml): Backward vectors indexed by a backward natural number length
