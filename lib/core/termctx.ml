(* This module should not be opened, but used qualified. *)

open Util
open Tbwd
open Dim
open Dimbwd
open Reporter
open Syntax
open Term

(* Here we define a data structure analogous to Ctx.t, but using terms rather than values.  This is used to store the context of a metavariable, as the value context containing level variables is too volatile to store in the Galaxy.  We also define a function to evaluate a Termctx into a Ctx.  (We can also read back a Ctx into a Termctx, but we wait to define that operation until readback.ml for dependency reasons.) *)

type 'b binding = { ty : ('b, kinetic) term; tm : ('b, kinetic) term option }

type (_, _, _) entry =
  | Vis : {
      dim : 'm D.t;
      plusdim : ('m, 'n, 'mn) D.plus;
      vars : (N.zero, 'n, string option, 'f1) NICubeOf.t;
      (* The reason for the "snoc" here is so that some of the terms and types in these bindings can refer to other ones.  Of course it should really be only the *later* ones that can refer to the *earlier* ones, but we don't have a way to specify that in the type parameters. *)
      bindings : ('mn, ('b, 'mn) snoc binding) CubeOf.t;
      hasfields : ('m, 'f2) Ctx.has_fields;
      fields : (Field.t * string * (('b, 'mn) snoc, kinetic) term, 'f2) Bwv.t;
      fplus : ('f1, 'f2, 'f) N.plus;
    }
      -> ('b, 'f, 'mn) entry
  | Invis : ('n, ('b, 'n) snoc binding) CubeOf.t -> ('b, N.zero, 'n) entry

let dim_entry : type b f n. (b, f, n) entry -> n D.t = function
  | Vis { bindings; _ } | Invis bindings -> CubeOf.dim bindings

module Ordered = struct
  type (_, _) t =
    | Emp : (N.zero, emp) t
    | Snoc : ('a, 'b) t * ('b, 'x, 'n) entry * ('a, 'x, 'ax) N.plus -> ('ax, ('b, 'n) snoc) t
    | Lock : ('a, 'b) t -> ('a, 'b) t

  let rec dbwd : type a b. (a, b) t -> b Dbwd.t = function
    | Emp -> Word Zero
    | Snoc (ctx, e, _) ->
        let (Word b) = dbwd ctx in
        Word (Suc (b, dim_entry e))
    | Lock ctx -> dbwd ctx

  let ext_let :
      type a b.
      (a, b) t -> string option -> (b, D.zero) snoc binding -> (a N.suc, (b, D.zero) snoc) t =
   fun ctx x b ->
    Snoc
      ( ctx,
        Vis
          {
            dim = D.zero;
            plusdim = D.plus_zero D.zero;
            vars = NICubeOf.singleton x;
            bindings = CubeOf.singleton b;
            hasfields = No_fields;
            fields = Emp;
            fplus = Zero;
          },
        Suc Zero )
end

type ('a, 'b) t = Permute : ('a, 'i) N.perm * ('i, 'b) Ordered.t -> ('a, 'b) t

let dbwd (Permute (_, ctx)) = Ordered.dbwd ctx

let ext_let (Permute (p, ctx)) xs b =
  let ctx = Ordered.ext_let ctx xs b in
  Permute (Insert (p, Top), ctx)

(* When printing a hole we also use a Termctx, since that's what we store anyway, and we would also have to read back a value context anyway in order to unparse it. *)
type printable += PHole : (string option, 'a) Bwv.t * ('a, 'b) t * ('b, kinetic) term -> printable
