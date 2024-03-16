(* The postprocessor records the variables lexically in scope and their binding to intrinsically well-scoped (raw) De Bruijn indices in a Bwv.  For parsing record-types, we also allow a De Bruijn index to expose its fields as many lexical variables.  This module should not be opened, but used qualified. *)

open Util
open Core

type 'n t = (string option * (string, Field.t) Abwd.t, 'n) Bwv.t

let empty : 'n t = Emp
let ext (ctx : 'n t) (x : string option) : 'n N.suc t = Snoc (ctx, (x, Emp))

let ext_fields (ctx : 'n t) (x : string option) (flds : (string, Field.t) Abwd.t) : 'n N.suc t =
  Snoc (ctx, (x, flds))

let rec find : type n. string -> n t -> [ `Var of n N.index | `Field of n N.index * Field.t | `None ]
    =
 fun x ctx ->
  let lift = function
    | `Var i -> `Var (N.Pop i)
    | `Field (i, fld) -> `Field (N.Pop i, fld)
    | `None -> `None in
  match ctx with
  | Snoc (ctx, (y, flds)) -> (
      if y = Some x then `Var Top
      else
        match Abwd.find_opt x flds with
        | Some fld -> `Field (Top, fld)
        | None -> lift (find x ctx))
  | Emp -> `None

let top : type n. n N.suc t -> n t * string option = function
  | Snoc (ctx, (x, _)) -> (ctx, x)

(* Versions of Bwv.append_plus.  Unfortunately we currently need two of them, for appending a Vec and a Bwv.  It should really be only Vec, like Bwv.append_plus, but that would require converting some more things to Fwns. *)

type _ bappend_plus =
  | Bappend_plus : ('n, 'm, 'nm) Fwn.bplus * (string option, 'm) Vec.t * 'nm t -> 'n bappend_plus

let rec bappend_plus : type n. n t -> string option list -> n bappend_plus =
 fun ctx vars ->
  match vars with
  | [] -> Bappend_plus (Zero, [], ctx)
  | x :: xs ->
      let (Bappend_plus (nm, ys, ctx)) = bappend_plus (ext ctx x) xs in
      Bappend_plus (Suc nm, x :: ys, ctx)

type _ append_plus =
  | Append_plus : ('n, 'm, 'nm) N.plus * (string option, 'm) Bwv.t * 'nm t -> 'n append_plus

let append_plus : type n. n t -> string option list -> n append_plus =
 fun ctx vars ->
  let rec go :
      type n m nm.
      (n, m, nm) N.plus -> (string option, m) Bwv.t -> nm t -> string option list -> n append_plus =
   fun nm xs ctx vars ->
    match vars with
    | [] -> Append_plus (nm, xs, ctx)
    | x :: rest -> go (Suc nm) (Snoc (xs, x)) (ext ctx x) rest in
  go Zero Emp ctx vars
