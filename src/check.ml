open Raw
open Value
open Term
open Dim
open Act
open Norm
open Equal
open Monad.Ops (Monad.Maybe)

(* A context is a list of variables with types which are values.  The variables themselves, when represented by De Bruijn LEVELS, can appear in the types of later variables.  In particular, the LENGTH of this context, which is its type parameter as a type-level nat, is the current De Bruijn LEVEL for new variables to be added.  We can look up the INDEX of a TERM VARIABLE into this Bwv to get its type, but not of course the LEVEL of a VALUE VARIABLE. *)
type 'a ctx = (value, 'a) Bwv.t

let level_of : 'a ctx -> int = fun ctx -> N.to_int (Bwv.length ctx)

(* The empty context *)
let empty_ctx : N.zero ctx = Emp

(* Every context has an underlying environment that substitutes each (level) variable for itself (index).  This environment ALWAYS HAS DIMENSION ZERO, and therefore in particular the variables don't need to come with their boundaries. *)
let rec env_of_ctx : type a. a ctx -> (D.zero, a) env = function
  | Emp -> Emp D.zero
  | Snoc (ctx, ty) ->
      let tbl = Hashtbl.create 1 in
      let () = Hashtbl.add tbl (SFace_of (id_sface D.zero)) (var (level_of ctx) ty) in
      Ext (env_of_ctx ctx, tbl)

(* Evaluate a term in (the environment of) a context.  Thus, replace its De Bruijn indices with De Bruijn levels, and substitute the values of variables with definitions. *)
let eval_in_ctx : type a. a ctx -> a term -> value = fun ctx tm -> eval (env_of_ctx ctx) tm

(* Extend a context by a finite number of new variables, whose types are specified in a hashtable. *)
let rec ctx_exts :
    type a b ab c. a ctx -> (a, b, ab) N.plus -> (c, b) Bwv.t -> (c, value) Hashtbl.t -> ab ctx =
 fun ctx ab keys vals ->
  match (ab, keys) with
  | Zero, Emp -> ctx
  | Suc ab, Snoc (keys, key) -> Snoc (ctx_exts ctx ab keys vals, Hashtbl.find vals key)

(* Look through a specified number of lambdas to find an inner body. *)
let rec lambdas : type a b ab. (a, b, ab) N.plus -> a check -> ab check option =
 fun ab tm ->
  match (ab, tm) with
  | Zero, _ -> Some tm
  | Suc _, Lam body -> lambdas (N.suc_plus'' ab) body
  | _ -> None

(* Slurp up an entire application spine *)
let spine : type a. a synth -> a synth * a check list =
 fun tm ->
  let rec spine tm args =
    match tm with
    | Raw.App (fn, arg) -> spine fn (arg :: args)
    | _ -> (tm, args) in
  spine tm []

let rec check : type a. a ctx -> a check -> value -> a term option =
 fun ctx tm ty ->
  match tm with
  | Synth stm ->
      let* sval, sty = synth ctx stm in
      let* () = equal_val (level_of ctx) sty ty in
      return sval
  | Lam _ -> (
      (* We don't pick up the body here, only the presence of at least one lambda.  We'll pick up an appropriate number of lambdas in check_lam. *)
      match ty with
      | Inst { tm = ty; dim = _; tube; args } -> check_lam ctx tm ty tube args
      | Uninst ty -> check_lam ctx tm ty tube_zero Emp)
  | Pi (dom, cod) ->
      (* User-level pi-types are always dimension zero, so the domain must be a zero-dimensional type. *)
      let* cdom = check ctx dom (Uninst (UU D.zero)) in
      let edom = eval_in_ctx ctx cdom in
      let* ccod = check (Snoc (ctx, edom)) cod (Uninst (UU D.zero)) in
      return (Term.Pi (cdom, ccod))

and check_lam :
    type a m n f.
    a ctx -> a check -> uninst -> (m, n, f) count_tube -> (value, f) Bwv.t -> a term option =
 fun ctx tm ty tube args ->
  match ty with
  | Pi (dom_faces, doms, cod) -> (
      match (compare (tube_uninst tube) D.zero, compare (tube_inst tube) (dim_faces dom_faces)) with
      | Neq, _ | _, Neq -> None
      | Eq, Eq ->
          (* Slurp up the right number of lambdas for the dimension of the pi-type, and pick up the body inside them. *)
          let (Plus af) = N.plus (faces_out dom_faces) in
          let* body = lambdas af tm in
          (* Extend the context by one variable for each type in doms, instantiated at the appropriate previous ones. *)
          (* TODO: This is largely copy-and-pasted from equal_at_uninst.  Factor it out. *)
          let (Tube t) = tube in
          let m = tube_inst tube in
          let Eq = D.plus_uniq t.plus_dim (D.zero_plus m) in
          let Eq = faces_uniq t.total_faces dom_faces in
          let Eq = faces_uniq t.missing_faces faces_zero in
          let Eq = N.plus_uniq t.plus_faces (Suc Zero) in
          let df = sfaces dom_faces in
          let argtbl = Hashtbl.create 10 in
          let ctx =
            Bwv.fold2_left_map_append af
              {
                f =
                  (fun c (SFace_of fa) dom ->
                    let level = level_of c in
                    let k = dom_sface fa in
                    let (Has_tube (Tube t)) = has_tube D.zero k in
                    let Eq = D.plus_uniq t.plus_dim (D.zero_plus k) in
                    let ty =
                      inst dom (Tube t)
                        (Bwv.map_plus t.plus_faces
                           (fun (SFace_of fc) -> Hashtbl.find argtbl (SFace_of (comp_sface fa fc)))
                           (sfaces t.total_faces)) in
                    let v = Uninst (Neu (Var { level; deg = id_deg D.zero }, ty)) in
                    let () = Hashtbl.add argtbl (SFace_of fa) v in
                    ty);
              }
              ctx df doms in
          (* Apply and instantiate the codomain to those arguments to get a type to check the body at. *)
          (* TODO: This code is copy-and-pasted from apply_neu and equal_at_uninst.  Factor it out. *)
          let out_args =
            Bwv.map2_plus t.plus_faces
              (fun (SFace_of fa) afn ->
                let k = dom_sface fa in
                let (Has_faces k_faces) = count_faces k in
                let afntbl = Hashtbl.create 10 in
                let () =
                  Bwv.iter
                    (fun (SFace_of fc) ->
                      Hashtbl.add afntbl (SFace_of fc)
                        (Hashtbl.find argtbl (SFace_of (comp_sface fa fc))))
                    (sfaces k_faces) in
                apply afn (dom_sface fa) afntbl)
              df args in
          let output = inst (apply_binder cod argtbl) tube out_args in
          let* cbody = check ctx body output in
          return (Term.Lam (dom_faces, af, cbody)))
  | _ -> None

and synth : type a. a ctx -> a synth -> (a term * value) option =
 fun ctx tm ->
  match tm with
  | Var v -> return (Term.Var v, Bwv.nth v ctx)
  | UU -> return (Term.UU, Uninst (UU D.zero))
  | App _ ->
      (* If there's at least one application, we slurp up all the applications, synthesize a type for the function, and then pass off to synth_apps to iterate through all the arguments. *)
      let fn, args = spine tm in
      let* sfn, sty = synth ctx fn in
      synth_apps ctx sfn sty args
  | Id (a, x, y) ->
      (* This is just an abbreviation. *)
      synth ctx (App (App (Refl a, x), y))
  | Refl x ->
      let* sx, ety = synth ctx x in
      let ex = eval_in_ctx ctx sx in
      return (Refl sx, act_ty ex ety refl)
  | Sym x -> (
      let* sx, ety = synth ctx x in
      let ex = eval_in_ctx ctx sx in
      try
        let symty = act_ty ex ety sym in
        return (Sym sx, symty)
      with Invalid_uninst_action -> None)
  | Asc (tm, ty) ->
      let* sty, uu = synth ctx ty in
      let* () = equal_val (level_of ctx) uu (Uninst (UU D.zero)) in
      let ety = eval_in_ctx ctx sty in
      let* ctm = check ctx tm ety in
      return (ctm, ety)

(* Given a synthesized function and its type, and a list of arguments, check the arguments in appropriately-sized groups. *)
and synth_apps : type a. a ctx -> a term -> value -> a check list -> (a term * value) option =
 fun ctx sfn sty args ->
  (* First we check one group of arguments. *)
  let* afn, aty, aargs =
    match sty with
    | Inst { tm = fnty; dim = _; tube; args = tyargs } -> synth_app ctx sfn fnty tube tyargs args
    | Uninst fnty -> synth_app ctx sfn fnty tube_zero Emp args in
  (* If that used up all the arguments, we're done; otherwise we continue with the rest of the arguments. *)
  match aargs with
  | [] -> return (afn, aty)
  | _ :: _ -> synth_apps ctx afn aty aargs

and synth_app :
    type a m n f.
    a ctx ->
    a term ->
    uninst ->
    (m, n, f) count_tube ->
    (value, f) Bwv.t ->
    a check list ->
    (a term * value * a check list) option =
 fun ctx sfn fnty tube tyargs args ->
  match fnty with
  (* The obvious thing we can "apply" is an element of a pi-type. *)
  | Pi (dom_faces, doms, cod) -> (
      (* Ensure that the pi-type is fully instantiated and at the right dimension. *)
      let n = dim_faces dom_faces in
      match (compare (tube_inst tube) n, compare (tube_uninst tube) D.zero) with
      | Neq, _ | _, Neq -> None
      | Eq, Eq ->
          (* Pick up the right number of arguments for the dimension, leaving the others for a later call to synth_app *)
          let* args, rest = Bwv.of_list (faces_out dom_faces) args in
          let argtbl = Hashtbl.create 10 in
          let df = sfaces dom_faces in
          let () = Bwv.iter2 (Hashtbl.add argtbl) df args in
          (* Check each argument in "args" against the corresponding type in "doms", instantiated at the appropriate evaluated previous arguments, producing a Bwv of terms and storing the values in a hashtable. *)
          (* TODO: copy-and-pasted *)
          let eargtbl = Hashtbl.create 10 in
          let* cargs =
            bwv_mapM2
              (fun (SFace_of fa) dom ->
                let tm = Hashtbl.find argtbl (SFace_of fa) in
                let k = dom_sface fa in
                let (Has_tube (Tube t)) = has_tube D.zero k in
                let Eq = D.plus_uniq t.plus_dim (D.zero_plus k) in
                let ty =
                  inst dom (Tube t)
                    (Bwv.map_plus t.plus_faces
                       (fun (SFace_of fc) -> Hashtbl.find eargtbl (SFace_of (comp_sface fa fc)))
                       (sfaces t.total_faces)) in
                let* ctm = check ctx tm ty in
                let etm = eval_in_ctx ctx ctm in
                Hashtbl.add eargtbl (SFace_of fa) etm;
                return ctm)
              df doms in
          (* Evaluate cod at these evaluated arguments, and instantiate it at the appropriate values of tyargs, as with similar code in other places. *)
          (* TODO: copy-pasted from apply_neu etc. *)
          let (Tube t) = tube in
          let Eq = faces_uniq t.missing_faces faces_zero in
          let Eq = D.plus_uniq t.plus_dim (D.zero_plus n) in
          let Eq = faces_uniq t.total_faces dom_faces in
          let (Suc Zero) = t.plus_faces in
          let (Snoc (sdf, _)) = df in
          let out_args =
            Bwv.map2
              (fun (SFace_of fa) afn ->
                let k = dom_sface fa in
                let (Has_faces k_faces) = count_faces k in
                let afntbl = Hashtbl.create 10 in
                let () =
                  Bwv.iter
                    (fun (SFace_of fc) ->
                      Hashtbl.add afntbl (SFace_of fc)
                        (Hashtbl.find eargtbl (SFace_of (comp_sface fa fc))))
                    (sfaces k_faces) in
                apply afn (dom_sface fa) afntbl)
              sdf tyargs in
          let output = inst (apply_binder cod eargtbl) tube out_args in
          return (Term.App (sfn, dom_faces, cargs), output, rest))
  (* We can also "apply" a higher-dimensional *type*, leading to a (further) instantiation of it.  Here the number of arguments must exactly match *some* integral instantiation. *)
  | UU n -> (
      (* Ensure that the universe is fully instantiated and at the right dimension. *)
      match (compare (tube_inst tube) n, compare (tube_uninst tube) D.zero) with
      | Neq, _ | _, Neq -> None
      | Eq, Eq -> (
          let (Tube ({ total_faces; _ } as t)) = tube in
          let Eq = faces_uniq t.missing_faces faces_zero in
          let Eq = D.plus_uniq t.plus_dim (D.zero_plus n) in
          let Eq = N.plus_uniq t.plus_faces (Suc Zero) in
          (* Take as many arguments as possible that will instantiate a type of dimension n. *)
          let (Take (plus_dim, missing_faces, plus_faces, args, rest)) =
            take_tube total_faces args in
          (* If there were any arguments left over, there's nothing that can be done with them.  (TODO: Should the iteration in take_tube be folded into that of synth_apps, so that each time through synth_app we only instantiate once?) *)
          match rest with
          | _ :: _ -> None
          | [] ->
              let (Pos _) = faces_pos missing_faces in
              let (Suc ppf) = plus_faces in
              let (Snoc (tf, _)) = sfaces total_faces in
              (* We check each argument against the corresponding type instantiation argument, itself instantiated at the values of the appropriate previous arguments.  This requires random access to the previous evaluated arguments, so we store those in a hashtable, while also assembling them into a Bwv for later. *)
              let eargtbl = Hashtbl.create 10 in
              let* cargs =
                bwv_mapM3_plus ppf
                  (fun (SFace_of fa) tyarg arg ->
                    let k = dom_sface fa in
                    let (Has_tube (Tube kt as ktube)) = has_tube D.zero k in
                    let Eq = faces_uniq kt.missing_faces faces_zero in
                    let Eq = D.plus_uniq kt.plus_dim (D.zero_plus k) in
                    let Eq = N.plus_uniq kt.plus_faces (Suc Zero) in
                    let (Snoc (kfaces, _)) = sfaces kt.total_faces in
                    let kargs =
                      Bwv.map
                        (fun (SFace_of fb) -> Hashtbl.find eargtbl (SFace_of (comp_sface fa fb)))
                        kfaces in
                    let tyk = inst tyarg ktube kargs in
                    let* carg = check ctx arg tyk in
                    let earg = eval_in_ctx ctx carg in
                    let () = Hashtbl.add eargtbl (SFace_of fa) earg in
                    return carg)
                  tf tyargs args in
              (* Now we assemble the synthesized type, which is an full instantiation of the universe at a telescope consisting of instantiations of the type arguments at the evaluated term arguments. *)
              let m = dim_faces missing_faces in
              let n = D.plus_right plus_dim in
              let (Has_tube (Tube mt as mtube)) = has_tube D.zero m in
              let Eq = faces_uniq mt.missing_faces faces_zero in
              let Eq = D.plus_uniq mt.plus_dim (D.zero_plus m) in
              let Eq = N.plus_uniq mt.plus_faces (Suc Zero) in
              let (Snoc (mfaces, _)) = sfaces mt.total_faces in
              let tyargtbl = Hashtbl.create 10 in
              let () = Bwv.iter2 (Hashtbl.add tyargtbl) tf tyargs in
              let margs =
                Bwv.map
                  (fun (SFace_of fe) ->
                    let j = dom_sface fe in
                    let (Has_tube (Tube tyt as tytube)) = has_tube j n in
                    let fen = sface_plus fe plus_dim tyt.plus_dim in
                    let ty = Hashtbl.find tyargtbl (SFace_of fen) in
                    let tyf = sfaces tyt.total_faces in
                    let tyargs =
                      Bwv.map_plus tyt.plus_faces
                        (fun (SFace_of fa) -> Hashtbl.find eargtbl (SFace_of (comp_sface fen fa)))
                        tyf in
                    inst ty tytube tyargs)
                  mfaces in
              return
                ( Term.Inst (sfn, Tube { plus_dim; total_faces; missing_faces; plus_faces }, cargs),
                  inst (Uninst (UU m)) mtube margs,
                  [] )))
  | _ -> None
