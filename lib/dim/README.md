# Dimension theory for Narya

This directory contains all definitions and code that depends on the definition of the category of dimensions with faces and degeneracy operators.  The definition of this category is shared throughout this directory, but abstract outside of it.

As of May 5, 2024, this category is the n-ary semicartesian cube category, with arity specified by the user on the command-line.  But in the future, it will be generalized to allow multiple simultaneous "directions" of dimension, e.g. for parametricity, univalence, and display, of variable arity.

We make as many things as possible intrinsically well-typed.  In particular, dimensions are represented by types satisfying a predicate, so that cubical operators are parametrized by their domains and codomains.  We also implement general data structures for cubes and tubes of objects that accept faces as indices.  As of May 5, 2024, this enables us to completely avoid ever "counting" the number of faces possessed by a cube, or deciding on an "ordering" of those faces other than implicitly by the order of traversal defined for cube data structures.

Here is a listing of the files in this directory, as of May 5, 2024, with brief descriptions:

## Basic properties of dimensions

* [D](d.ml): Repackage type-level naturals as dimensions.
* [Endpoints](endpoints.ml): Dynamically control the arity of cubes.
* [Arith](arith.ml): Arithmetic properties of dimensions like factorization and cancellation.

## Cubical operators

* [Deg](deg.ml): Cubical degeneracies, including permutations.
* [Sface](sface.ml): Strict faces (not including permutations).
* [Face](face.ml): General faces (a strict face plus a permutation).
* [Op](op.ml): General cubical operators.
* [Bwsface](bwsface.ml): Same as strict faces, but recorded backwards.
* [Tface](tface.ml): A strict face restricted to lie in a certain tube.
* [Bwtface](bwtface.ml): Backwards version of tface.
* [Insertion](insertion.ml): A restricted permutation that preserves the relative order of part of its codomain.

## Data structures

* [Cube](cube.ml): A data structure storing arbitrary objects indexed by the strict faces of a cube.
* [Icube](icube.ml): Similar, but with extra type parameters.  This allows us to track extra dependencies, but limits the available operations.
* [Tube](tube.ml): Similar, but indexed only by tube faces.

## Interface

* [Dim.ml](dim.ml) and [Dim.mli](dim.mli): Imports everything and chooses what to export.
