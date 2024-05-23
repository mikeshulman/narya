(* This module should not be opened, but used qualified. *)

open Util
open Tbwd
open Dim
open Reporter
open Syntax
open Term
open Value
module Binding = Ctx.Binding

(* Here we define a data structure analogous to Ctx.t, but using terms rather than values.  This is used to store the context of a metavariable, as the value context containing level variables is too volatile to store in the Galaxy.  We also define a function to evaluate a Termctx into a Ctx.  (We can also read back a Ctx into a Termctx, but we wait to define that operation until readback.ml for dependency reasons.) *)

type 'b binding = { ty : ('b, kinetic) term; tm : ('b, kinetic) term option }

type (_, _, _) entry =
  | Vis : {
      dim : 'm D.t;
      plusdim : ('m, 'n, 'mn) D.plus;
      vars : (N.zero, 'n, string option, 'f1) NICubeOf.t;
      bindings : ('mn, ('b, 'mn) snoc binding) CubeOf.t;
      hasfields : ('m, 'f2) Ctx.has_fields;
      fields : (Field.t * string * (('b, 'mn) snoc, kinetic) term, 'f2) Bwv.t;
      fplus : ('f1, 'f2, 'f) N.plus;
    }
      -> ('b, 'f, 'mn) entry
  | Invis : ('n, ('b, 'n) snoc binding) CubeOf.t -> ('b, N.zero, 'n) entry

module Ordered = struct
  open Ctx.Ordered

  type (_, _) t =
    | Emp : (N.zero, emp) t
    | Snoc : ('a, 'b) t * ('b, 'x, 'n) entry * ('a, 'x, 'ax) N.plus -> ('ax, ('b, 'n) snoc) t
    (* A locked context permits no access to the variables behind it. *)
    | Lock : ('a, 'b) t -> ('a, 'b) t

  let eval_bindings :
      type a b n.
      (a, b) Ctx.Ordered.t -> (n, (b, n) snoc binding) CubeOf.t -> (n, Binding.t) CubeOf.t =
   fun ctx cbs ->
    let i = Ctx.Ordered.length ctx in
    let vbs = CubeOf.build (CubeOf.dim cbs) { build = (fun _ -> Binding.unknown ()) } in
    let tempctx = Ctx.Ordered.Snoc (ctx, Invis vbs, Zero) in
    let argtbl = Hashtbl.create 10 in
    let j = ref 0 in
    let () =
      CubeOf.miter
        {
          it =
            (fun fa [ ({ ty = cty; tm = ctm } : (b, n) snoc binding); vb ] ->
              (* Unlike in dom_vars, we don't need to instantiate the types, since their instantiations should have been preserved by readback and will reappear correctly here. *)
              let ety = eval_term tempctx cty in
              let level = (i, !j) in
              j := !j + 1;
              let v =
                match ctm with
                | None -> ({ tm = var level ety; ty = ety } : normal)
                | Some ctm -> { tm = eval_term tempctx ctm; ty = ety } in
              Hashtbl.add argtbl (SFace_of fa) v;
              Binding.specify vb None v);
        }
        [ cbs; vbs ] in
    vbs

  let eval_entry : type a b f n. (a, b) Ctx.Ordered.t -> (b, f, n) entry -> (f, n) Ctx.entry =
   fun ctx e ->
    match e with
    | Vis { dim; plusdim; vars; bindings; hasfields; fields; fplus } ->
        let bindings = eval_bindings ctx bindings in
        let fields = Bwv.map (fun (f, x, _) -> (f, x)) fields in
        Vis { dim; plusdim; vars; bindings; hasfields; fields; fplus }
    | Invis bindings -> Invis (eval_bindings ctx bindings)

  let rec eval : type a b. (a, b) t -> (a, b) Ctx.Ordered.t = function
    | Emp -> Emp
    | Snoc (ctx, e, af) ->
        let ectx = eval ctx in
        Snoc (ectx, eval_entry ectx e, af)
    | Lock ctx -> Lock (eval ctx)
end

type ('a, 'b) t = Permute : ('a, 'i) N.perm * ('i, 'b) Ordered.t -> ('a, 'b) t

let eval : type a b. (a, b) t -> (a, b) Ctx.t = function
  | Permute (p, ctx) -> Permute (p, Ordered.eval ctx)

(* When printing a hole we also uses a Termctx, since that's what we store anyway, and we would also have to read back a value context anyway in order to unparse it. *)
type printable += PHole : (string option, 'a) Bwv.t * ('a, 'b) t * ('b, kinetic) term -> printable
