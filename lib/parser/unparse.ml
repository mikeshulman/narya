open Bwd
open Util
open Bwd_extra
open Dim
open Core
open Term
open Notation
open Builtins
open Reporter
module StringMap = Map.Make (String)
open Hctx

(* If the head of an application spine is a constant term, and that constant has an associated notation, and there are enough of the supplied arguments to instantiate the notation, split off that many arguments and return the notation, those arguments, and the rest. *)
let get_notation head args =
  match head with
  | `Term (Const c) -> (
      match State.print_const c with
      | Some (notn, k) -> (
          match bwd_take k args with
          | Some (first, rest) -> Some (notn, first, rest)
          | None -> None)
      | None -> None)
  | _ -> None

(* Put parentheses around a term. *)
let parenthesize tm = outfix ~notn:parens ~inner:(Snoc (Emp, Term tm))

module Variables : sig
  type 'n t

  val empty : emp t
  val lookup : 'n t -> 'n index -> [ `Normal of string | `Cube of string * string ]
  val add_cube : 'b t -> string option -> string option * ('b, 'n) ext t

  val add_normals :
    'b t -> ('n, string option) CubeOf.t -> ('n, string option) CubeOf.t * ('b, 'n) ext t
end = struct
  type 'b ctx =
    | Emp : emp ctx
    | Cube : 'b ctx * string option -> ('b, 'n) ext ctx
    | Normals : 'b ctx * ('n, string option) CubeOf.t -> ('b, 'n) ext ctx

  type 'b t = { ctx : 'b ctx; used : int StringMap.t }

  let empty : emp t = { ctx = Emp; used = StringMap.empty }

  let lookup : type n. n t -> n index -> [ `Normal of string | `Cube of string * string ] =
   fun { ctx; used = _ } x ->
    let rec lookup : type n. n ctx -> n index -> [ `Normal of string | `Cube of string * string ] =
     fun ctx x ->
      match (ctx, x) with
      | Emp, _ -> .
      | Cube (ctx, _), Pop x -> lookup ctx x
      | Normals (ctx, _), Pop x -> lookup ctx x
      | Cube (_, Some x), Top fa -> `Cube (x, string_of_sface fa)
      | Cube (_, None), Top _ -> fatal (Anomaly "Reference to anonymous variable")
      | Normals (_, xs), Top fa -> (
          match CubeOf.find xs fa with
          | Some x -> `Normal x
          | None -> fatal (Anomaly "Reference to anonymous variable")) in
    lookup ctx x

  let uniquify : string option -> int StringMap.t -> string option * int StringMap.t =
   fun name used ->
    match name with
    | None -> (None, used)
    | Some name -> (
        match StringMap.find_opt name used with
        | None -> (Some name, used |> StringMap.add name 0)
        | Some n ->
            let rec until_unique k =
              let namek = name ^ string_of_int k in
              match StringMap.find_opt namek used with
              | None -> (namek, k)
              | Some _ -> until_unique (k + 1) in
            let namen, n = until_unique n in
            (Some namen, used |> StringMap.add namen 0 |> StringMap.add name (n + 1)))

  let uniquifies :
      type n.
      (n, string option) CubeOf.t ->
      int StringMap.t ->
      (n, string option) CubeOf.t * int StringMap.t =
   fun names used ->
    let module M = Monad.State (struct
      type t = int StringMap.t
    end) in
    let open CubeOf.Monadic (M) in
    mmapM { map = (fun _ [ name ] used -> uniquify name used) } [ names ] used

  let add_cube : 'b t -> string option -> string option * ('b, 'n) ext t =
   fun { ctx; used } name ->
    let name, used = uniquify name used in
    (name, { ctx = Cube (ctx, name); used })

  let add_normals :
      'b t -> ('n, string option) CubeOf.t -> ('n, string option) CubeOf.t * ('b, 'n) ext t =
   fun { ctx; used } names ->
    let names, used = uniquifies names used in
    (names, { ctx = Normals (ctx, names); used })
end

type unparser = {
  unparse :
    'lt 'ls 'rt 'rs. ('lt, 'ls) Interval.tt -> ('rt, 'rs) Interval.tt -> ('lt, 'ls, 'rt, 'rs) parse;
}

let unparse_notation :
    type left tight right lt ls rt rs.
    (left, tight, right) notation ->
    unparser Bwd.t ->
    (lt, ls) Interval.tt ->
    (rt, rs) Interval.tt ->
    (lt, ls, rt, rs) parse =
 fun notn args li ri ->
  let t = tightness notn in
  match (left notn, right notn) with
  | Open _, Open _ -> (
      match split_first args with
      | Some (first, Snoc (inner, last)) -> (
          match (Interval.contains li t, Interval.contains ri t) with
          | Some left_ok, Some right_ok ->
              let first = first.unparse li (interval_left notn) in
              let inner =
                Bwd.map (fun tm -> Term (tm.unparse Interval.entire Interval.entire)) inner in
              let last = last.unparse (interval_right notn) ri in
              infix ~notn ~first ~inner ~last ~left_ok ~right_ok
          | _ ->
              let first = first.unparse Interval.entire (interval_left notn) in
              let inner =
                Bwd.map (fun tm -> Term (tm.unparse Interval.entire Interval.entire)) inner in
              let last = last.unparse (interval_right notn) Interval.entire in
              let left_ok = No.minusomega_le t in
              let right_ok = No.minusomega_le t in
              parenthesize (infix ~notn ~first ~inner ~last ~left_ok ~right_ok))
      | _ -> fatal (Anomaly "missing arguments unparsing infix"))
  | Closed, Open _ -> (
      match args with
      | Snoc (inner, last) -> (
          match Interval.contains ri t with
          | Some right_ok ->
              let inner =
                Bwd.map (fun tm -> Term (tm.unparse Interval.entire Interval.entire)) inner in
              let last = last.unparse (interval_right notn) ri in
              prefix ~notn ~inner ~last ~right_ok
          | _ ->
              let inner =
                Bwd.map (fun tm -> Term (tm.unparse Interval.entire Interval.entire)) inner in
              let last = last.unparse (interval_right notn) Interval.entire in
              let right_ok = No.minusomega_le t in
              parenthesize (prefix ~notn ~inner ~last ~right_ok))
      | _ -> fatal (Anomaly "missing argument unparsing prefix"))
  | Open _, Closed -> (
      match split_first args with
      | Some (first, inner) -> (
          match Interval.contains li t with
          | Some left_ok ->
              let first = first.unparse li (interval_left notn) in
              let inner =
                Bwd.map (fun tm -> Term (tm.unparse Interval.entire Interval.entire)) inner in
              postfix ~notn ~first ~inner ~left_ok
          | _ ->
              let first = first.unparse Interval.entire (interval_left notn) in
              let inner =
                Bwd.map (fun tm -> Term (tm.unparse Interval.entire Interval.entire)) inner in
              let left_ok = No.minusomega_le t in
              parenthesize (postfix ~notn ~first ~inner ~left_ok))
      | _ -> fatal (Anomaly "missing argument unparsing postfix"))
  | Closed, Closed ->
      let inner = Bwd.map (fun tm -> Term (tm.unparse Interval.entire Interval.entire)) args in
      outfix ~notn ~inner

let unparse_var : type lt ls rt rs. string option -> (lt, ls, rt, rs) parse = function
  | Some x -> Ident [ x ]
  | None -> Placeholder

let rec unparse_abs :
    type li ls ri rs.
    string option Bwd.t ->
    (li, ls) Interval.tt ->
    (li, ls, No.plus_omega) No.lt ->
    (ri, rs, No.plus_omega) No.lt ->
    (li, ls, ri, rs) parse =
 fun xs li left_ok right_ok ->
  match xs with
  | Emp -> fatal (Anomaly "missing abstractions")
  | Snoc (Emp, Some x) -> Ident [ x ]
  | Snoc (Emp, None) -> Placeholder
  | Snoc (xs, x) ->
      let fn = unparse_abs xs li left_ok (No.le_refl No.plus_omega) in
      let arg = unparse_var x in
      App { fn; arg; left_ok; right_ok }

let unparse_numeral : type n li ls ri rs. n term -> (li, ls, ri, rs) parse option =
 fun tm ->
  let rec getsucs tm k =
    match tm with
    (* As in parsing, it would be better not to hardcode the constructor names 'zero' and 'suc'. *)
    | Term.Constr (c, _, Emp) when c = Constr.intern "zero" -> Some (Numeral (Q.of_int k))
    | Constr (c, _, Snoc (Emp, arg)) when c = Constr.intern "suc" ->
        getsucs (CubeOf.find_top arg) (k + 1)
    | _ -> None in
  getsucs tm 0

let rec get_spine :
    type b n. n term -> [ `App of n term * n term Bwd.t | `Field of n term * Field.t * n term Bwd.t ]
    = function
  | App (fn, arg) -> (
      match get_spine fn with
      | `App (head, args) -> `App (head, CubeOf.append_bwd args arg)
      | `Field (head, fld, args) -> `Field (head, fld, CubeOf.append_bwd args arg))
  | Field (head, fld) -> `Field (head, fld, Emp)
  | Act (tm, s) -> (
      match is_id_deg s with
      | Some () -> get_spine tm
      | None -> `App (tm, Emp))
  | tm -> `App (tm, Emp)

let rec unparse :
    type n lt ls rt rs.
    n Variables.t ->
    n term ->
    (lt, ls) Interval.tt ->
    (rt, rs) Interval.tt ->
    (lt, ls, rt, rs) parse =
 fun vars tm li ri ->
  match tm with
  | Var x -> (
      match Variables.lookup vars x with
      | `Normal x -> Ident [ x ]
      | `Cube (x, fa) -> if fa = "" then Ident [ x ] else Ident [ x; fa ])
  | Const c -> Ident [ Scope.name_of c ]
  (* TODO: Can we associate notations to fields, like to constants? *)
  | Field (tm, fld) -> unparse_spine vars (`Field (tm, fld)) Emp li ri
  | UU n ->
      unparse_act vars
        { unparse = (fun _ _ -> outfix ~notn:universe ~inner:Emp) }
        (deg_zero n) li ri
  | Inst (ty, tyargs) ->
      (* TODO: How can we allow special notations for some instantiations, like x=y for Id A x y? *)
      unparse_spine vars (`Term ty)
        (Bwd.map (make_unparser vars) (TubeOf.append_bwd Emp tyargs))
        li ri
  | Pi _ -> unparse_pis vars Emp tm li ri
  | App _ -> (
      match get_spine tm with
      | `App (fn, args) -> unparse_spine vars (`Term fn) (Bwd.map (make_unparser vars) args) li ri
      | `Field (head, fld, args) ->
          unparse_spine vars (`Field (head, fld)) (Bwd.map (make_unparser vars) args) li ri)
  | Act (tm, s) -> unparse_act vars { unparse = (fun li ri -> unparse vars tm li ri) } s li ri
  | Let (x, tm, body) -> (
      let tm = unparse vars tm Interval.entire Interval.entire in
      match Interval.contains ri No.minus_omega with
      | Some right_ok ->
          let x, vars = Variables.add_cube vars x in
          let body = unparse vars body Interval.entire ri in
          prefix ~notn:letin
            ~inner:(Snoc (Snoc (Emp, Term (unparse_var x)), Term tm))
            ~last:body ~right_ok
      | None ->
          let x, vars = Variables.add_cube vars x in
          let body = unparse vars body Interval.entire Interval.entire in
          let right_ok = No.le_refl No.minus_omega in
          parenthesize
            (prefix ~notn:letin
               ~inner:(Snoc (Snoc (Emp, Term (unparse_var x)), Term tm))
               ~last:body ~right_ok))
  | Lam (_, cube, _) -> unparse_lam cube vars Emp tm li ri
  | Struct fields -> (
      let flds = List.map (fun (key, _) -> Field.to_string key) (Field.Map.bindings fields) in
      match State.print_struct flds with
      | Some (Wrap notn) ->
          let vals =
            List.fold_left
              (fun args (_, v) -> Snoc (args, make_unparser vars v))
              Emp (Field.Map.bindings fields) in
          unparse_notation notn vals li ri
      | None ->
          outfix ~notn:struc
            ~inner:
              (Field.Map.fold
                 (fun fld tm acc ->
                   Snoc
                     ( Snoc (acc, Term (Ident [ Field.to_string fld ])),
                       Term (unparse vars tm Interval.entire Interval.entire) ))
                 fields Emp))
  (* TODO: Can we associate notations to constructors, like to constants? *)
  | Constr (c, _, args) -> (
      (* TODO: This doesn't print the dimension.  This is correct since constructors don't have to (and in fact *can't* be) written with their dimension, but it could also be somewhat confusing, e.g. printing "refl (0:N)" yields just "0", and similarly "refl (nil. : List N)" yields "nil.". *)
      match unparse_numeral tm with
      | Some tm -> tm
      | None ->
          let args = Bwd.map CubeOf.find_top args in
          unparse_spine vars (`Constr c) (Bwd.map (make_unparser vars) args) li ri)

and make_unparser : type n. n Variables.t -> n term -> unparser =
 fun vars tm -> { unparse = (fun li ri -> unparse vars tm li ri) }

and unparse_spine :
    type n lt ls rt rs.
    n Variables.t ->
    [ `Term of n term
    | `Constr of Constr.t
    | `Field of n term * Field.t
    | `Degen of string
    | `Unparser of unparser ] ->
    unparser Bwd.t ->
    (lt, ls) Interval.tt ->
    (rt, rs) Interval.tt ->
    (lt, ls, rt, rs) parse =
 fun vars head args li ri ->
  (* First we check whether the head has an associated notation, and if so whether it is applied to enough arguments to instantiate that notation. *)
  match get_notation head args with
  (* If it's applied to exactly the right number of arguments, we unparse it as that notation. *)
  | Some (Wrap notn, args, Emp) -> unparse_notation notn args li ri
  (* Otherwise, the unparsed notation has to be applied to the rest of the arguments as a spine. *)
  | Some (Wrap notn, args, (Snoc _ as rest)) ->
      unparse_spine vars
        (`Unparser { unparse = (fun li ri -> unparse_notation notn args li ri) })
        rest li ri
  (* If not, we proceed to unparse it as an application spine. *)
  | None -> (
      match args with
      | Emp -> (
          match head with
          | `Term tm -> unparse vars tm li ri
          | `Constr c -> Constr (Constr.to_string c)
          | `Field (tm, fld) ->
              unparse_field
                { unparse = (fun li ri -> unparse vars tm li ri) }
                (Field.to_string fld) li ri
          | `Degen s -> Ident [ s ]
          | `Unparser tm -> tm.unparse li ri)
      | Snoc (args, arg) -> (
          match (Interval.contains li No.plus_omega, Interval.contains ri No.plus_omega) with
          | Some left_ok, Some right_ok ->
              let fn = unparse_spine vars head args li Interval.plus_omega_only in
              let arg = arg.unparse Interval.empty ri in
              App { fn; arg; left_ok; right_ok }
          | _ ->
              let fn =
                unparse_spine vars head args Interval.plus_omega_only Interval.plus_omega_only in
              let arg = arg.unparse Interval.empty Interval.plus_omega_only in
              let left_ok = No.le_refl No.plus_omega in
              let right_ok = No.le_refl No.plus_omega in
              parenthesize (App { fn; arg; left_ok; right_ok })))

and unparse_field :
    type n lt ls rt rs.
    unparser -> string -> (lt, ls) Interval.tt -> (rt, rs) Interval.tt -> (lt, ls, rt, rs) parse =
 fun tm fld li ri ->
  match (Interval.contains li No.plus_omega, Interval.contains ri No.plus_omega) with
  | Some left_ok, Some right_ok ->
      let fn = tm.unparse li Interval.plus_omega_only in
      let arg = Field fld in
      App { fn; arg; left_ok; right_ok }
  | _ ->
      let fn = tm.unparse Interval.plus_omega_only Interval.plus_omega_only in
      let arg = Field fld in
      let left_ok = No.le_refl No.plus_omega in
      let right_ok = No.le_refl No.plus_omega in
      parenthesize (App { fn; arg; left_ok; right_ok })

and unparse_lam :
    type m n lt ls rt rs.
    m variables ->
    n Variables.t ->
    string option Bwd.t ->
    n term ->
    (lt, ls) Interval.tt ->
    (rt, rs) Interval.tt ->
    (lt, ls, rt, rs) parse =
 fun cube vars xs body li ri ->
  match (cube, body) with
  | `Cube _, Lam (_, `Cube x, inner) ->
      let x, vars = Variables.add_cube vars x in
      unparse_lam cube vars (Snoc (xs, x)) inner li ri
  | `Normal _, Lam (_, `Normal x, inner) ->
      let x, vars = Variables.add_normals vars x in
      unparse_lam cube vars (CubeOf.append_bwd xs x) inner li ri
  | _ -> (
      let notn =
        match cube with
        | `Cube _ -> cubeabs
        | `Normal _ -> abs in
      match (Interval.contains li No.minus_omega, Interval.contains ri No.minus_omega) with
      | Some left_ok, Some right_ok ->
          let li_ok = No.lt_trans Any_strict left_ok No.minusomega_lt_plusomega in
          let first = unparse_abs xs li li_ok No.minusomega_lt_plusomega in
          let last = unparse vars body Interval.entire ri in
          infix ~notn ~first ~inner:Emp ~last ~left_ok ~right_ok
      | _ ->
          let first =
            unparse_abs xs Interval.entire (No.le_plusomega No.minus_omega)
              No.minusomega_lt_plusomega in
          let last = unparse vars body Interval.entire Interval.entire in
          let left_ok = No.le_refl No.minus_omega in
          let right_ok = No.le_refl No.minus_omega in
          parenthesize (infix ~notn ~first ~inner:Emp ~last ~left_ok ~right_ok))

and unparse_act :
    type n lt ls rt rs a b.
    n Variables.t ->
    unparser ->
    (a, b) deg ->
    (lt, ls) Interval.tt ->
    (rt, rs) Interval.tt ->
    (lt, ls, rt, rs) parse =
 fun vars tm s li ri ->
  match is_id_deg s with
  | Some () -> tm.unparse li ri
  | None -> (
      match name_of_deg s with
      | Some str -> unparse_spine vars (`Degen str) (Snoc (Emp, tm)) li ri
      | None -> (
          match Interval.contains li No.plus_omega with
          | Some left_ok ->
              let tm = tm.unparse li Interval.empty in
              postfix ~notn:degen ~first:tm
                ~inner:(Snoc (Emp, Term (Ident [ string_of_deg s ])))
                ~left_ok
          | None ->
              let tm = tm.unparse Interval.entire Interval.empty in
              parenthesize
                (postfix ~notn:degen ~first:tm
                   ~inner:(Snoc (Emp, Term (Ident [ string_of_deg s ])))
                   ~left_ok:(No.le_plusomega No.minus_omega))))

and unparse_pis :
    type n lt ls rt rs.
    n Variables.t ->
    unparser Bwd.t ->
    n term ->
    (lt, ls) Interval.tt ->
    (rt, rs) Interval.tt ->
    (lt, ls, rt, rs) parse =
 fun vars accum tm li ri ->
  match tm with
  | Pi (x, doms, cods) -> (
      match (x, compare (CubeOf.dim doms) D.zero) with
      | Some x, Eq ->
          let x, newvars = Variables.add_normals vars (CubeOf.singleton (Some x)) in
          unparse_pis newvars
            (Snoc
               ( accum,
                 {
                   unparse =
                     (fun _ _ ->
                       unparse_pi_dom
                         (Option.get (CubeOf.find_top x))
                         (unparse vars (CubeOf.find_top doms) (interval_right asc) Interval.entire));
                 } ))
            (CodCube.find_top cods) li ri
      | None, Eq ->
          let _, newvars = Variables.add_normals vars (CubeOf.singleton None) in
          unparse_pis_final vars accum
            {
              unparse =
                (fun li ri ->
                  unparse_arrow
                    (make_unparser vars (CubeOf.find_top doms))
                    (make_unparser newvars (CodCube.find_top cods))
                    li ri);
            }
            li ri
      | _, Neq ->
          (* TODO *)
          fatal (Unimplemented "printing higher-dimensional Pi-type")
          (* unparse_pis_final vars accum0 accum (Sorry.e ()) li ri *))
  | _ -> unparse_pis_final vars accum (make_unparser vars tm) li ri

and unparse_arrow :
    type n lt ls rt rs.
    unparser -> unparser -> (lt, ls) Interval.tt -> (rt, rs) Interval.tt -> (lt, ls, rt, rs) parse =
 fun dom cod li ri ->
  match (Interval.contains li No.zero, Interval.contains ri No.zero) with
  | Some left_ok, Some right_ok ->
      let first = dom.unparse li (interval_left arrow) in
      let last = cod.unparse (interval_right arrow) ri in
      infix ~notn:arrow ~first ~inner:Emp ~last ~left_ok ~right_ok
  | _ ->
      let first = dom.unparse Interval.entire (interval_left arrow) in
      let last = cod.unparse (interval_right arrow) Interval.entire in
      let left_ok = No.minusomega_lt_zero in
      let right_ok = No.minusomega_lt_zero in
      parenthesize (infix ~notn:arrow ~first ~inner:Emp ~last ~left_ok ~right_ok)

and unparse_pis_final :
    type n lt ls rt rs.
    n Variables.t ->
    unparser Bwd.t ->
    unparser ->
    (lt, ls) Interval.tt ->
    (rt, rs) Interval.tt ->
    (lt, ls, rt, rs) parse =
 fun vars accum tm li ri ->
  match split_first accum with
  | None -> tm.unparse li ri
  | Some (dom0, accum) ->
      unparse_arrow
        { unparse = (fun li ri -> unparse_spine vars (`Unparser dom0) accum li ri) }
        tm li ri

and unparse_pi_dom :
    type lt ls rt rs.
    string ->
    (No.minus_omega, No.strict, No.minus_omega, No.nonstrict) parse ->
    (lt, ls, rt, rs) parse =
 fun x dom ->
  outfix ~notn:parens
    ~inner:
      (Snoc
         ( Emp,
           Term
             (infix ~notn:asc ~first:(Ident [ x ]) ~inner:Emp ~last:dom
                ~left_ok:(No.le_refl No.minus_omega) ~right_ok:(No.le_refl No.minus_omega)) ))
