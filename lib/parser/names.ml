open Util
open Tbwd
open Dim
open Core
open Term
module StringMap = Map.Make (String)

let __DEFAULT_NAME__ = "H"
let default () = __DEFAULT_NAME__
let __ANONYMOUS_VARIABLE__ = "_H"

(* Track the used variable names, to generate fresh ones for bound variables if needed. *)

(* We store a parametrized list like a context, and also a map that counts how many like-named variables already exist, so that we can create a new one with an unused number. *)
type 'b ctx =
  | Emp : emp ctx
  | Snoc : 'b ctx * 'n variables * (string, string) Abwd.t -> ('b, 'n) snoc ctx

type 'b t = { ctx : 'b ctx; used : int StringMap.t }

let empty : emp t = { ctx = Emp; used = StringMap.empty }

let cubevar x fa : string list =
  let fa = string_of_sface fa in
  if fa = "" then [ x ] else [ x; fa ]

(* Look up an index variable to find a name for it. *)
let lookup : type n. n t -> n index -> string list =
 fun { ctx; used = _ } x ->
  let rec lookup : type n. n ctx -> n index -> string list =
   fun ctx x ->
    match (ctx, x) with
    | Emp, _ -> .
    | Snoc (ctx, _, _), Index (Later x, fa) -> lookup ctx (Index (x, fa))
    | Snoc (_, Variables (_, mn, xs), _), Index (Now, fa) -> (
        let (SFace_of_plus (_, fb, fc)) = sface_of_plus mn fa in
        match NICubeOf.find xs fc with
        | Some x -> cubevar x fb
        | None -> [ __ANONYMOUS_VARIABLE__ ]) in
  lookup ctx x

(* Look up an index variable together with a field, to find a name for the combination, if there is one. *)
let lookup_field : type n. n t -> n index -> string -> string list option =
 fun { ctx; used = _ } x f ->
  let rec lookup : type n. n ctx -> n index -> string list option =
   fun ctx x ->
    match (ctx, x) with
    | Emp, _ -> .
    | Snoc (ctx, _, _), Index (Later x, fa) -> lookup ctx (Index (x, fa))
    | Snoc (_, Variables (_, mn, _), fields), Index (Now, fa) ->
        let open Monad.Ops (Monad.Maybe) in
        let (SFace_of_plus (_, fb, fc)) = sface_of_plus mn fa in
        let* _ = is_id_sface fc in
        let* y = Abwd.find_opt f fields in
        return (cubevar y fb) in
  lookup ctx x

(* Make a variable name unique, adding the new one to the list of used variables and returning it. *)
let uniquify : string -> int StringMap.t -> string * [ `Original | `Renamed ] * int StringMap.t =
 fun name used ->
  match StringMap.find_opt name used with
  | None -> (name, `Original, used |> StringMap.add name 0)
  | Some n ->
      (* The tentative new name is the original one suffixed by that number.  But the user might already have created a variable with that name, so we have to increment the number until we find an unused name.  *)
      let rec until_unique k =
        let namek = name ^ string_of_int k in
        match StringMap.find_opt namek used with
        | None -> (namek, k)
        | Some _ -> until_unique (k + 1) in
      let namen, n = until_unique n in
      (namen, `Renamed, used |> StringMap.add namen 0 |> StringMap.add name (n + 1))

(* Make a variable name unique, leaving unnamed variables unnamed. *)
let uniquify_opt :
    string option -> int StringMap.t -> string option * [ `Original | `Renamed ] * int StringMap.t =
 fun name used ->
  match name with
  | None -> (None, `Original, used)
  | Some name ->
      let name, orig, used = uniquify name used in
      (Some name, orig, used)

(* Do the same thing to a whole cube of variable names, leaving unnamed variables unnamed. *)
let uniquify_cube : type n left right.
    (left, n, string option, right) NICubeOf.t ->
    int StringMap.t ->
    (left, n, string option, right) NICubeOf.t * int StringMap.t =
 fun names used ->
  (* Apparently we need to define the iteration function with an explicit type so that it ends up sufficiently polymorphic. *)
  let uniquify_nfamof : type m left right.
      (left, m, string option, right) NFamOf.t ->
      int StringMap.t ->
      (left, m, string option, right) NFamOf.t * int StringMap.t =
   fun (NFamOf name) used ->
    let name, _, used = uniquify_opt name used in
    (NFamOf name, used) in
  let open NICubeOf.Applicatic (Applicative.OfMonad (Monad.State (struct
    type t = int StringMap.t
  end))) in
  mapM { map = (fun _ name used -> uniquify_nfamof name used) } names used

(* Add a new cube variable at a specified dimension, generating a fresh version of its name if necessary to avoid conflicts, leaving unnamed variables unnamed. *)
let add_cube : type n b. n D.t -> b t -> string option -> string option * (b, n) snoc t =
 fun n { ctx; used } name ->
  let name, _, used = uniquify_opt name used in
  ( name,
    { ctx = Snoc (ctx, Variables (n, D.plus_zero n, NICubeOf.singleton name), Abwd.empty); used } )

(* Same, but starting from an unnamed variable and giving it a default name. *)
let add_cube_autogen : type n b. n D.t -> b t -> string * (b, n) snoc t =
 fun n ctx ->
  let x, used = add_cube n ctx (Some __DEFAULT_NAME__) in
  (Option.get x, used)

(* Add a cube of variables, generating a fresh version of each of their names, leaving unnamed variables unnamed. *)
let add : 'b t -> 'n variables -> 'n variables * ('b, 'n) snoc t =
 fun { ctx; used } (Variables (m, mn, names)) ->
  let names, used = uniquify_cube names used in
  let vars = Variables (m, mn, names) in
  (vars, { ctx = Snoc (ctx, vars, Abwd.empty); used })

(* Extract all the names in a context, generating a fresh version of each name from left to right, including field access variables, leaving unnamed variables unnamed. *)
let rec of_ordered_ctx : type a b. (a, b) Ctx.Ordered.t -> b t = function
  | Emp -> empty
  | Snoc (ctx, Vis { dim; plusdim; vars; bindings = _; hasfields = _; fields; fplus = _ }, _) ->
      let { ctx; used } = of_ordered_ctx ctx in
      let vars, used = uniquify_cube vars used in
      let module M = Mbwd.Monadic (Monad.State (struct
        type t = int StringMap.t
      end)) in
      let fields, used =
        M.mmapM
          (fun [ (f, x) ] used ->
            let x, _, used = uniquify x used in
            ((Field.to_string f, x), used))
          [ Bwv.to_bwd fields ]
          used in
      { ctx = Snoc (ctx, Variables (dim, plusdim, vars), fields); used }
  | Snoc (ctx, Invis bindings, _) -> snd (add_cube (CubeOf.dim bindings) (of_ordered_ctx ctx) None)
  | Lock ctx -> of_ordered_ctx ctx

let of_ctx : type a b. (a, b) Ctx.t -> b t = function
  | Permute (_, _, ctx) -> of_ordered_ctx ctx

(* Add a cube of variables WITHOUT replacing them by fresh versions.  Should only be used when the variables have already been so replaced, as in the output of uniquify_vars below. *)
let unsafe_add : 'b t -> 'n variables -> (string, string) Abwd.t -> ('b, 'n) snoc t =
 fun { ctx; used } vars fields -> { ctx = Snoc (ctx, vars, fields); used }

(* Given a Bwv of variables, proceed through from the *right* to mark them as visible or shadowed, accumulating a list of the visible names in a map.  Replaces unnamed variables by a default name. *)
let rec used_vars : type n.
    (string option, n) Bwv.t ->
    int StringMap.t ->
    (string * [ `Visible | `Shadowed ], n) Bwv.t * int StringMap.t =
 fun vars used ->
  let do_var x used =
    match x with
    | Some x ->
        if StringMap.mem x used then (x, `Shadowed, used)
        else (x, `Visible, used |> StringMap.add x 0)
    | None -> (__DEFAULT_NAME__, `Shadowed, used) in
  match vars with
  | Emp -> (Emp, used)
  | Snoc (vars, x) ->
      let x, o, used = do_var x used in
      let vars, used = used_vars vars used in
      (Snoc (vars, (x, o)), used)

(* Uniquify the names in a bwv from the *right*, thus leaving unchanged those that are still in lexical scope.  Also assigns an autogenerated name to previously unnamed variables.  Returns a Names object in the empty context that can then be used to build up a new one including those variables.  Since those variables have already been uniquified, they should be added in with unsafe_add.  (TODO: Can we avoid having to expose unsafe_add?) *)
let uniquify_vars : type a.
    (string option, a) Bwv.t -> (string * [ `Original | `Renamed ], a) Bwv.t * emp t =
 fun vars ->
  (* First we collect a map of all the visible names, also marking the given names as visible or shadowed. *)
  let vars, used = used_vars vars StringMap.empty in
  (* Then we proceed again from right to left, leaving the visible variables alone and replacing the shadowed ones with uniquified versions.  We do this in two passes to ensure that the uniquified version of a shadowed variable is never chosen in such a way as would shadow a variable to its left that already had that name. *)
  let rec go : type n.
      (string * [ `Visible | `Shadowed ], n) Bwv.t ->
      int StringMap.t ->
      (string * [ `Original | `Renamed ], n) Bwv.t * int StringMap.t =
   fun vars used ->
    match vars with
    | Emp -> (Emp, used)
    | Snoc (vars, (x, sh)) ->
        let x, orig, used =
          match sh with
          | `Visible -> (x, `Original, used)
          | `Shadowed ->
              let x, _, used = uniquify x used in
              (x, `Renamed, used) in
        let vars, used = go vars used in
        (Snoc (vars, (x, orig)), used) in
  let vars, used = go vars used in
  (vars, { ctx = Emp; used })
