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

(* Given a list of variable names, we can append them to a Varscope while simultaneously extracting them into a vector whose (Fwn) length is the change in the length of the Varscope.  More generally, we can *prepend* them to a supplied vector, and record any needed arithmetic relations between the lengths. *)

type (_, _) append_plus =
  | Append_plus :
      (* These aren't currently needed. *)
      (* ('m, 'k, 'mk) Fwn.fplus * ('n, 'm, 'nm) N.plus * *)
      ('nm, 'k, 'nmk) Fwn.bplus
      * ('n, 'mk, 'nmk) Fwn.bplus
      * (string option, 'mk) Vec.t
      * 'nm t
      -> ('n, 'k) append_plus

let rec append_plus :
    type n k. (string option, k) Vec.t -> n t -> string option list -> (n, k) append_plus =
 fun last ctx vars ->
  match vars with
  | [] ->
      let (Bplus nmk) = Fwn.bplus (Vec.length last) in
      Append_plus ((*Zero, Zero, *) nmk, nmk, last, ctx)
  | x :: xs ->
      let (Append_plus ((* mk, nm,*) nm_k, n_mk, xs, ctx)) = append_plus last (ext ctx x) xs in
      Append_plus ((*Fwn.suc_fplus mk, N.plus_suc nm, *) nm_k, Suc n_mk, x :: xs, ctx)
