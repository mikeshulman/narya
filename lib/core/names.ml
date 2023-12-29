open Util
open Dim
open Term
open Reporter
module StringMap = Map.Make (String)
open Hctx

(* Track the used variable names, to generate fresh ones for bound variables if needed. *)

(* We store a parametrized list like a context, and also a map that counts how many like-named variables already exist, so that we can create a new one with an unused number. *)
type 'b ctx = Emp : emp ctx | Snoc : 'b ctx * 'n variables -> ('b, 'n) ext ctx
type 'b t = { ctx : 'b ctx; used : int StringMap.t }

let empty : emp t = { ctx = Emp; used = StringMap.empty }

let lookup : type n. n t -> n index -> [ `Normal of string | `Cube of string * string ] =
 fun { ctx; used = _ } x ->
  let rec lookup : type n. n ctx -> n index -> [ `Normal of string | `Cube of string * string ] =
   fun ctx x ->
    match (ctx, x) with
    | Emp, _ -> .
    | Snoc (ctx, _), Pop x -> lookup ctx x
    | Snoc (_, `Cube (Some x)), Top fa -> `Cube (x, string_of_sface fa)
    | Snoc (_, `Cube None), Top _ -> fatal (Anomaly "Reference to anonymous variable")
    | Snoc (_, `Normal xs), Top fa -> (
        match CubeOf.find xs fa with
        | Some x -> `Normal x
        | None -> fatal (Anomaly "Reference to anonymous variable")) in
  lookup ctx x

(* Make a variable name unique, adding the new one to the list of used variables and returning it. *)

let uniquify : string option -> int StringMap.t -> string option * int StringMap.t =
 fun name used ->
  match name with
  | None -> (None, used)
  | Some name -> (
      match StringMap.find_opt name used with
      | None -> (Some name, used |> StringMap.add name 0)
      | Some n ->
          (* The tentative new name is the original one suffixed by that number.  But the user might already have created a variable with that name, so we have to increment the number until we find an unused name.  *)
          let rec until_unique k =
            let namek = name ^ string_of_int k in
            match StringMap.find_opt namek used with
            | None -> (namek, k)
            | Some _ -> until_unique (k + 1) in
          let namen, n = until_unique n in
          (Some namen, used |> StringMap.add namen 0 |> StringMap.add name (n + 1)))

(* Do the same thing to a whole cube of variable names. *)
let uniquifies :
    type n.
    (n, string option) CubeOf.t -> int StringMap.t -> (n, string option) CubeOf.t * int StringMap.t
    =
 fun names used ->
  let module M = Monad.State (struct
    type t = int StringMap.t
  end) in
  let open CubeOf.Monadic (M) in
  mmapM { map = (fun _ [ name ] used -> uniquify name used) } [ names ] used

let add_cube : 'b t -> string option -> string option * ('b, 'n) ext t =
 fun { ctx; used } name ->
  let name, used = uniquify name used in
  (name, { ctx = Snoc (ctx, `Cube name); used })

let add_normals :
    'b t -> ('n, string option) CubeOf.t -> ('n, string option) CubeOf.t * ('b, 'n) ext t =
 fun { ctx; used } names ->
  let names, used = uniquifies names used in
  (names, { ctx = Snoc (ctx, `Normal names); used })

let add : 'b t -> 'n variables -> 'n variables * ('b, 'n) ext t =
 fun vars name ->
  match name with
  | `Cube name ->
      let name, vars = add_cube vars name in
      (`Cube name, vars)
  | `Normal name ->
      let name, vars = add_normals vars name in
      (`Normal name, vars)
