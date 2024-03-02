open Util
open Dim

(* An hctx is a type-level backwards list of dimensions.  It describes the structure of a context of "cube variables", each of which has a dimension and represents an entire cube of actual variables. *)

type emp = Dummy_emp
type ('xs, 'x) ext = Dummy_ext
type _ hctx = Emp : emp hctx | Ext : 'xs hctx * 'x D.t -> ('xs, 'x) ext hctx

(* ('a, 'b, 'n, 'ab) exts means that 'a is an hctx (although this isn't enforced -- it could be any type), 'b is a Fwn.t, and 'ab is the result of adding 'b copies of the dimension 'n at the end of 'a. *)
type (_, _, _, _) exts =
  | Zero : ('a, Fwn.zero, 'n, 'a) exts
  | Suc : ('a, 'b, 'n, 'ab) exts -> ('a, 'b Fwn.suc, 'n, ('ab, 'n) ext) exts

let rec exts_ext : type a b c n. (a, b, n, c) exts -> ((a, n) ext, b, n, (c, n) ext) exts = function
  | Zero -> Zero
  | Suc ab -> Suc (exts_ext ab)

(* This is named by analogy to N.suc_plus. *)
let exts_suc : type a b c n. (a, b Fwn.suc, n, c) exts -> ((a, n) ext, b, n, c) exts = function
  | Suc ab -> exts_ext ab

let rec exts_right : type a b c n. (a, b, n, c) exts -> b Fwn.t = function
  | Zero -> Zero
  | Suc ab -> Suc (exts_right ab)

type (_, _, _) has_exts = Exts : ('a, 'b, 'n, 'ab) exts -> ('a, 'b, 'n) has_exts

let rec exts : type a b n. b Fwn.t -> (a, b, n) has_exts =
 fun b ->
  match b with
  | Zero -> Exts Zero
  | Suc b ->
      let (Exts p) = exts b in
      Exts (Suc p)

(* A typechecked De Bruijn index is a well-scoped natural number together with a definite strict face (the top face, if none was supplied explicitly).  Unlike a raw De Bruijn index, the scoping is by an hctx rather than a type-level nat.  This allows the face to also be well-scoped: its codomain must be the dimension appearing in the hctx at that position. *)
type 'a index =
  | Top : ('k, 'n) sface -> ('a, 'n) ext index
  | Pop : 'xs index -> ('xs, 'x) ext index

(* A De Bruijn level is a pair of integers: one for the position (counting in) of the cube-variable-bundle in the context, and one that counts through the faces of that bundle. *)
type level = int * int

(* We also have a forwards version. *)

type nil = Dummy_nil
type ('x, 'xs) cons = Dummy_cons
type _ fwhctx = Nil : nil fwhctx | Cons : 'x D.t * 'xs fwhctx -> ('x, 'xs) cons fwhctx

(* As with lists and backwards lists, a forward hctx can naturally be appended to a backward one. *)

type (_, _, _) append =
  | Append_nil : ('a, nil, 'a) append
  | Append_cons : (('a, 'x) ext, 'b, 'c) append -> ('a, ('x, 'b) cons, 'c) append

(* Change a backwards hctx into a forwards one. *)

type _ hctx_to_fw = To_fw : 'a fwhctx * (emp, 'a, 'b) append -> 'b hctx_to_fw

let hctx_to_fw : type c. c hctx -> c hctx_to_fw =
 fun c ->
  let rec hctx_to_fw : type a b c. a hctx -> b fwhctx -> (a, b, c) append -> c hctx_to_fw =
   fun a b abc ->
    match a with
    | Emp -> To_fw (b, abc)
    | Ext (a, x) -> hctx_to_fw a (Cons (x, b)) (Append_cons abc) in
  hctx_to_fw c Nil Append_nil
