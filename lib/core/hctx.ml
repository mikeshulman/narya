open Util
open Dim

(* An hctx is a type-level backwards list of dimensions.  It describes the structure of a context of "cube variables", each of which has a dimension and represents an entire cube of actual variables. *)

type emp = Dummy_emp
type ('xs, 'x) ext = Dummy_ext
type _ hctx = Emp : emp hctx | Ext : 'xs hctx * 'x D.t -> ('xs, 'x) ext hctx

(* ('a, 'b, 'n, 'ab) exts means that 'a is an hctx (although this isn't enforced -- it could be any type), 'b is a N.t, and 'ab is the result of adding 'b copies of the dimension 'n at the end of 'a. *)
type (_, _, _, _) exts =
  | Zero : ('a, N.zero, 'n, 'a) exts
  | Suc : ('a, 'b, 'n, 'ab) exts -> ('a, 'b N.suc, 'n, ('ab, 'n) ext) exts

let rec exts_ext : type a b c n. (a, b, n, c) exts -> ((a, n) ext, b, n, (c, n) ext) exts = function
  | Zero -> Zero
  | Suc ab -> Suc (exts_ext ab)

(* This is named by analogy to N.suc_plus. *)
let exts_suc : type a b c n. (a, b N.suc, n, c) exts -> ((a, n) ext, b, n, c) exts = function
  | Suc ab -> exts_ext ab

let rec exts_right : type a b c n. (a, b, n, c) exts -> b N.t = function
  | Zero -> Nat Zero
  | Suc ab ->
      let (Nat b) = exts_right ab in
      Nat (Suc b)

type (_, _, _) has_exts = Exts : ('a, 'b, 'n, 'ab) exts -> ('a, 'b, 'n) has_exts

let rec exts : type a b n. b N.t -> (a, b, n) has_exts =
 fun b ->
  match b with
  | Nat Zero -> Exts Zero
  | Nat (Suc b) ->
      let (Exts p) = exts (Nat b) in
      Exts (Suc p)

(* A typechecked De Bruijn index is a well-scoped natural number together with a definite strict face (the top face, if none was supplied explicitly).  Unlike a raw De Bruijn index, the scoping is by an hctx rather than a type-level nat.  This allows the face to also be well-scoped: its codomain must be the dimension appearing in the hctx at that position. *)
type 'a index =
  | Top : ('k, 'n) sface -> ('a, 'n) ext index
  | Pop : 'xs index -> ('xs, 'x) ext index

(* A De Bruijn level is a pair of integers: one for the position (counting in) of the cube-variable-bundle in the context, and one that counts through the faces of that bundle. *)
type level = int * int
