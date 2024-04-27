open Bwd
open Util
open Bwd_extra
open Dim
open Core
open Syntax
open Term
open Notation
open Builtins
open Reporter
open Printable
module StringMap = Map.Make (String)

(* If the head of an application spine is a constant or constructor, and it has an associated notation, and there are enough of the supplied arguments to instantiate the notation, split off that many arguments and return the notation, those arguments permuted to match the order of the pattern variables in the notation, and the rest. *)
let get_notation head args =
  let open Monad.Ops (Monad.Maybe) in
  let* { notn; pat_vars; val_vars } =
    match head with
    | `Term (Const c) -> State.Current.unparse (`Constant c)
    | `Constr c -> State.Current.unparse (`Constr c)
    | _ -> None in
  (* There's probably a more efficient way to do this that doesn't involve converting to and from forwards lists, but this way is more natural and easier to understand, and I think this is unlikely to be a performance bottleneck. *)
  let rec take_labeled labels elts acc =
    match (labels, elts) with
    | [], _ -> return (acc, elts)
    | _ :: _, [] -> None
    | k :: labels, x :: elts -> take_labeled labels elts (acc |> StringMap.add k x) in
  let* first, rest = take_labeled val_vars (Bwd.to_list args) StringMap.empty in
  let first = List.fold_left (fun acc k -> Snoc (acc, StringMap.find k first)) Emp pat_vars in
  return (notn, first, Bwd.of_list rest)

let unlocated (value : 'a) : 'a located = { value; loc = None }

(* Put parentheses around a term. *)
let parenthesize tm = unlocated (outfix ~notn:parens ~ws:[] ~inner:(Snoc (Emp, Term tm)))

(* A "delayed" result of unparsing that needs only to know the tightness intervals to produce a result. *)
type unparser = {
  unparse :
    'lt 'ls 'rt 'rs.
    ('lt, 'ls) Interval.tt -> ('rt, 'rs) Interval.tt -> ('lt, 'ls, 'rt, 'rs) parse located;
}

(* Unparse a notation together with all its arguments. *)
let unparse_notation :
    type left tight right lt ls rt rs.
    (left, tight, right) notation ->
    unparser Bwd.t ->
    (lt, ls) Interval.tt ->
    (rt, rs) Interval.tt ->
    (lt, ls, rt, rs) parse located =
 fun notn args li ri ->
  let t = tightness notn in
  (* Based on the fixity of the notation, we have to extract the first and/or last argument to treat differently.  In each case except for outfix, we also have to test whether the notation fits in the given tightness interval, and if not, parenthesize it. *)
  match (left notn, right notn) with
  | Open _, Open _ -> (
      match split_first args with
      | Some (first, Snoc (inner, last)) -> (
          let inner = Bwd.map (fun tm -> Term (tm.unparse Interval.entire Interval.entire)) inner in
          match (Interval.contains li t, Interval.contains ri t) with
          | Some left_ok, Some right_ok ->
              let first = first.unparse li (interval_left notn) in
              let last = last.unparse (interval_right notn) ri in
              unlocated (infix ~notn ~ws:[] ~first ~inner ~last ~left_ok ~right_ok)
          | _ ->
              let first = first.unparse Interval.entire (interval_left notn) in
              let last = last.unparse (interval_right notn) Interval.entire in
              let left_ok = No.minusomega_le t in
              let right_ok = No.minusomega_le t in
              parenthesize (unlocated (infix ~notn ~ws:[] ~first ~inner ~last ~left_ok ~right_ok)))
      | _ -> fatal (Anomaly "missing arguments unparsing infix"))
  | Closed, Open _ -> (
      match args with
      | Snoc (inner, last) -> (
          let inner = Bwd.map (fun tm -> Term (tm.unparse Interval.entire Interval.entire)) inner in
          match Interval.contains ri t with
          | Some right_ok ->
              let last = last.unparse (interval_right notn) ri in
              unlocated (prefix ~notn ~ws:[] ~inner ~last ~right_ok)
          | _ ->
              let last = last.unparse (interval_right notn) Interval.entire in
              let right_ok = No.minusomega_le t in
              parenthesize (unlocated (prefix ~notn ~ws:[] ~inner ~last ~right_ok)))
      | _ -> fatal (Anomaly "missing argument unparsing prefix"))
  | Open _, Closed -> (
      match split_first args with
      | Some (first, inner) -> (
          let inner = Bwd.map (fun tm -> Term (tm.unparse Interval.entire Interval.entire)) inner in
          match Interval.contains li t with
          | Some left_ok ->
              let first = first.unparse li (interval_left notn) in
              unlocated (postfix ~notn ~ws:[] ~first ~inner ~left_ok)
          | _ ->
              let first = first.unparse Interval.entire (interval_left notn) in
              let left_ok = No.minusomega_le t in
              parenthesize (unlocated (postfix ~notn ~ws:[] ~first ~inner ~left_ok)))
      | _ -> fatal (Anomaly "missing argument unparsing postfix"))
  | Closed, Closed ->
      let inner = Bwd.map (fun tm -> Term (tm.unparse Interval.entire Interval.entire)) args in
      unlocated (outfix ~notn ~ws:[] ~inner)

(* Unparse a variable name, possibly anonymous. *)
let unparse_var : type lt ls rt rs. string option -> (lt, ls, rt, rs) parse located = function
  | Some x -> unlocated (Ident ([ x ], []))
  | None -> unlocated (Placeholder [])

(* Unparse a Bwd of variables to occur in an iterated abstraction.  If there is more than one variable, the result is an "application spine".  Can occur in any tightness interval that contains +ω. *)
let rec unparse_abs :
    type li ls ri rs.
    string option Bwd.t ->
    (li, ls) Interval.tt ->
    (li, ls, No.plus_omega) No.lt ->
    (ri, rs, No.plus_omega) No.lt ->
    (li, ls, ri, rs) parse located =
 fun xs li left_ok right_ok ->
  match xs with
  | Emp -> fatal (Anomaly "missing abstractions")
  | Snoc (Emp, Some x) -> unlocated (Ident ([ x ], []))
  | Snoc (Emp, None) -> unlocated (Placeholder [])
  | Snoc (xs, x) ->
      let fn = unparse_abs xs li left_ok (No.le_refl No.plus_omega) in
      let arg = unparse_var x in
      unlocated (App { fn; arg; left_ok; right_ok })

(* If a term is a natural number numeral (a bunch of 'suc' constructors applied to a 'zero' constructor), unparse it as that numeral; otherwise return None. *)
let unparse_numeral : type n li ls ri rs. (n, kinetic) term -> (li, ls, ri, rs) parse option =
 fun tm ->
  let rec getsucs tm k =
    match tm with
    (* As in parsing, it would be better not to hardcode the constructor names 'zero' and 'suc'. *)
    | Term.Constr (c, _, Emp) when c = Constr.intern "zero" ->
        Some (Ident (String.split_on_char '.' (Q.to_string (Q.of_int k)), []))
    | Constr (c, _, Snoc (Emp, arg)) when c = Constr.intern "suc" ->
        getsucs (CubeOf.find_top arg) (k + 1)
    | _ -> None in
  getsucs tm 0

let rec get_list :
    type n li ls ri rs.
    (n, kinetic) term -> (n, kinetic) term Bwd.t -> (n, kinetic) term Bwd.t option =
 fun tm elts ->
  match tm with
  | Term.Constr (c, _, Emp) when c = Constr.intern "nil" -> Some elts
  | Constr (c, _, Snoc (Snoc (Emp, car), cdr)) when c = Constr.intern "cons" ->
      get_list (CubeOf.find_top cdr) (Snoc (elts, CubeOf.find_top car))
  | _ -> None

let rec get_bwd :
    type n li ls ri rs.
    (n, kinetic) term -> (n, kinetic) term list -> (n, kinetic) term Bwd.t option =
 fun tm elts ->
  match tm with
  | Term.Constr (c, _, Emp) when c = Constr.intern "emp" -> Some (Bwd.of_list elts)
  | Constr (c, _, Snoc (Snoc (Emp, rdc), rac)) when c = Constr.intern "snoc" ->
      get_bwd (CubeOf.find_top rdc) (CubeOf.find_top rac :: elts)
  | _ -> None

(* Given a term, extract its head and arguments as an application spine.  If the spine contains a field projection, stop there and return only the arguments after it, noting the field name and what it is applied to (which itself be another spine). *)
let rec get_spine :
    type b n.
    (n, kinetic) term ->
    [ `App of (n, kinetic) term * (n, kinetic) term Bwd.t
    | `Field of (n, kinetic) term * Field.t * (n, kinetic) term Bwd.t ] =
 fun tm ->
  match tm with
  | App (fn, arg) -> (
      match get_spine fn with
      | `App (head, args) -> `App (head, CubeOf.append_bwd args arg)
      | `Field (head, fld, args) -> `Field (head, fld, CubeOf.append_bwd args arg))
  | Field (head, fld) -> `Field (head, fld, Emp)
  (* We have to look through identity degeneracies here. *)
  | Act (body, s) -> (
      match is_id_deg s with
      | Some () -> get_spine body
      | None -> `App (tm, Emp))
  | tm -> `App (tm, Emp)

(* The primary unparsing function.  Given the variable names, unparse a term into given tightness intervals. *)
let rec unparse :
    type n lt ls rt rs.
    n Names.t ->
    (n, kinetic) term ->
    (lt, ls) Interval.tt ->
    (rt, rs) Interval.tt ->
    (lt, ls, rt, rs) parse located =
 fun vars tm li ri ->
  match tm with
  | Var x -> unlocated (Ident (Names.lookup vars x, []))
  | Const c -> unlocated (Ident (Scope.name_of c, []))
  (* TODO: Can we associate notations to fields, like to constants? *)
  | Field (tm, fld) -> unparse_spine vars (`Field (tm, fld)) Emp li ri
  | UU n ->
      unparse_act vars
        { unparse = (fun _ _ -> unlocated (outfix ~notn:universe ~ws:[] ~inner:Emp)) }
        (deg_zero n) li ri
  | Inst (ty, tyargs) ->
      (* We unparse instantiations like application spines, since that is how they are represented in user syntax.
         TODO: How can we allow special notations for some instantiations, like x=y for Id A x y? *)
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
      (* If a let-in doesn't fit in its interval, we have to parenthesize it. *)
      let x, vars = Names.add_cube D.zero vars x in
      match Interval.contains ri No.minus_omega with
      | Some right_ok ->
          let body = unparse vars body Interval.entire ri in
          unlocated
            (prefix ~notn:letin ~ws:[]
               ~inner:(Snoc (Snoc (Emp, Term (unparse_var x)), Term tm))
               ~last:body ~right_ok)
      | None ->
          let body = unparse vars body Interval.entire Interval.entire in
          let right_ok = No.le_refl No.minus_omega in
          parenthesize
            (unlocated
               (prefix ~notn:letin ~ws:[]
                  ~inner:(Snoc (Snoc (Emp, Term (unparse_var x)), Term tm))
                  ~last:body ~right_ok)))
  | Lam (Variables (m, _, _), _) ->
      let cube =
        match compare m D.zero with
        | Eq -> `Normal
        | Neq -> `Cube in
      unparse_lam cube vars Emp tm li ri
  | Struct (Eta, _, fields) ->
      unlocated
        (outfix ~notn:parens ~ws:[]
           ~inner:
             (Abwd.fold
                (fun fld (tm, l) acc ->
                  let tm = unparse vars tm Interval.entire Interval.entire in
                  Snoc
                    ( acc,
                      Term
                        (match l with
                        | `Labeled ->
                            unlocated
                              (infix ~notn:coloneq ~ws:[]
                                 ~first:(unlocated (Ident ([ Field.to_string fld ], [])))
                                 ~inner:Emp ~last:tm ~left_ok:(No.le_refl No.minus_omega)
                                 ~right_ok:(No.le_refl No.minus_omega))
                        (* An unlabeled 1-tuple must be written (_ := M). *)
                        | `Unlabeled when Bwd.length fields = 1 ->
                            unlocated
                              (infix ~notn:coloneq ~ws:[] ~first:(unlocated (Placeholder []))
                                 ~inner:Emp ~last:tm ~left_ok:(No.le_refl No.minus_omega)
                                 ~right_ok:(No.le_refl No.minus_omega))
                        | `Unlabeled -> tm) ))
                fields Emp))
  (* Not yet unparsing comatches *)
  (*
  | Struct (Noeta, fields) ->
      unlocated
        (outfix ~notn:comatch ~ws:[]
           ~inner:
             (Abwd.fold
                (* Comatches can't have unlabeled fields *)
                  (fun fld (tm, _) acc ->
                  Snoc
                    ( Snoc (acc, Term (unlocated (Field (Field.to_string fld, [])))),
                      Term (unparse vars tm Interval.entire Interval.entire) ))
                fields Emp))
*)
  | Constr (c, _, args) -> (
      (* TODO: This doesn't print the dimension.  This is correct since constructors don't have to (and in fact *can't* be) written with their dimension, but it could also be somewhat confusing, e.g. printing "refl (0:N)" yields just "0", and similarly "refl (nil. : List N)" yields "nil.". *)
      match unparse_numeral tm with
      | Some tm -> unlocated tm
      | None -> (
          match get_list tm Emp with
          | Some args ->
              let inner =
                Mbwd.mmap
                  (fun [ tm ] -> Term (unparse vars tm Interval.entire Interval.entire))
                  [ args ] in
              unlocated (outfix ~notn:fwd ~ws:[] ~inner)
          | None -> (
              match get_bwd tm [] with
              | Some args ->
                  let inner =
                    Mbwd.mmap
                      (fun [ tm ] -> Term (unparse vars tm Interval.entire Interval.entire))
                      [ args ] in
                  unlocated (outfix ~notn:bwd ~ws:[] ~inner)
              | None ->
                  let args = Bwd.map CubeOf.find_top args in
                  unparse_spine vars (`Constr c) (Bwd.map (make_unparser vars) args) li ri)))

(* The master unparsing function can easily be delayed. *)
and make_unparser : type n. n Names.t -> (n, kinetic) term -> unparser =
 fun vars tm -> { unparse = (fun li ri -> unparse vars tm li ri) }

(* Unparse a spine with its arguments whose head could be many things: an as-yet-not-unparsed term, a constructor, a field projection, a degeneracy, or a general delayed unparsing. *)
and unparse_spine :
    type n lt ls rt rs.
    n Names.t ->
    [ `Term of (n, kinetic) term
    | `Constr of Constr.t
    | `Field of (n, kinetic) term * Field.t
    | `Degen of string
    | `Unparser of unparser ] ->
    unparser Bwd.t ->
    (lt, ls) Interval.tt ->
    (rt, rs) Interval.tt ->
    (lt, ls, rt, rs) parse located =
 fun vars head args li ri ->
  (* First we check whether the head is a term with an associated notation, and if so whether it is applied to enough arguments to instantiate that notation. *)
  match get_notation head args with
  (* If it's applied to exactly the right number of arguments, we unparse it as that notation. *)
  | Some (Wrap notn, args, Emp) -> unparse_notation notn args li ri
  (* Otherwise, the unparsed notation has to be applied to the rest of the arguments as a spine. *)
  | Some (Wrap notn, args, (Snoc _ as rest)) ->
      unparse_spine vars
        (`Unparser { unparse = (fun li ri -> unparse_notation notn args li ri) })
        rest li ri
  (* If not, we proceed to unparse it as an application spine, recursively. *)
  | None -> (
      match args with
      | Emp -> (
          match head with
          | `Term tm -> unparse vars tm li ri
          | `Constr c -> unlocated (Constr (Constr.to_string c, []))
          | `Field (tm, fld) -> unparse_field (make_unparser vars tm) (Field.to_string fld) li ri
          | `Degen s -> unlocated (Ident ([ s ], []))
          | `Unparser tm -> tm.unparse li ri)
      | Snoc (args, arg) -> (
          (* As before, if the application doesn't fit in its tightness interval, we have to parenthesize it. *)
          match (Interval.contains li No.plus_omega, Interval.contains ri No.plus_omega) with
          | Some left_ok, Some right_ok ->
              let fn = unparse_spine vars head args li Interval.plus_omega_only in
              let arg = arg.unparse Interval.empty ri in
              unlocated (App { fn; arg; left_ok; right_ok })
          | _ ->
              let fn =
                unparse_spine vars head args Interval.plus_omega_only Interval.plus_omega_only in
              let arg = arg.unparse Interval.empty Interval.plus_omega_only in
              let left_ok = No.le_refl No.plus_omega in
              let right_ok = No.le_refl No.plus_omega in
              parenthesize (unlocated (App { fn; arg; left_ok; right_ok }))))

and unparse_field :
    type n lt ls rt rs.
    unparser ->
    string ->
    (lt, ls) Interval.tt ->
    (rt, rs) Interval.tt ->
    (lt, ls, rt, rs) parse located =
 fun tm fld li ri ->
  match (Interval.contains li No.plus_omega, Interval.contains ri No.plus_omega) with
  | Some left_ok, Some right_ok ->
      let fn = tm.unparse li Interval.plus_omega_only in
      let arg = unlocated (Field (fld, [])) in
      unlocated (App { fn; arg; left_ok; right_ok })
  | _ ->
      let fn = tm.unparse Interval.plus_omega_only Interval.plus_omega_only in
      let arg = unlocated (Field (fld, [])) in
      let left_ok = No.le_refl No.plus_omega in
      let right_ok = No.le_refl No.plus_omega in
      parenthesize (unlocated (App { fn; arg; left_ok; right_ok }))

(* For unparsing an iterated abstraction, we group together the fully-normal variables and at-least-partially-cube variables, since they have different notations.  There is no notation for partially-cube variables, so we make them fully cube.  We recursively descend through the structure of the term, storing in 'cube' which kind of variable we are picking up and continuing until we find either a non-abstraction or an abstraction of the wrong type.  *)
and unparse_lam :
    type n lt ls rt rs.
    [ `Cube | `Normal ] ->
    n Names.t ->
    string option Bwd.t ->
    (n, kinetic) term ->
    (lt, ls) Interval.tt ->
    (rt, rs) Interval.tt ->
    (lt, ls, rt, rs) parse located =
 fun cube vars xs body li ri ->
  match body with
  | Lam (Variables (m, m_n, boundvars), inner) -> (
      match (cube, compare m D.zero) with
      | `Normal, Eq ->
          let Eq = D.plus_uniq m_n (D.zero_plus (D.plus_right m_n)) in
          let x, vars = Names.add_normals vars boundvars in
          unparse_lam cube vars (CubeOf.append_bwd xs x) inner li ri
      | `Cube, Neq ->
          let x, vars = Names.add_cube (D.plus_out m m_n) vars (CubeOf.find_top boundvars) in
          unparse_lam cube vars (Snoc (xs, x)) inner li ri
      | _ -> unparse_lam_done cube vars xs body li ri)
  | _ -> unparse_lam_done cube vars xs body li ri

(* Once we hit either a non-abstraction or a different kind of abstraction, we pick the appropriate notation to use for the abstraction, depending on the kind of variables.  Note that both are (un)parsed as binary operators whose left-hand argument is an "application spine" of variables, produced here by unparse_abs. *)
and unparse_lam_done :
    type n lt ls rt rs.
    [ `Cube | `Normal ] ->
    n Names.t ->
    string option Bwd.t ->
    (n, kinetic) term ->
    (lt, ls) Interval.tt ->
    (rt, rs) Interval.tt ->
    (lt, ls, rt, rs) parse located =
 fun cube vars xs body li ri ->
  let notn =
    match cube with
    | `Cube -> cubeabs
    | `Normal -> abs in
  (* Of course, if we don't fit in the tightness interval, we have to parenthesize. *)
  match (Interval.contains li No.minus_omega, Interval.contains ri No.minus_omega) with
  | Some left_ok, Some right_ok ->
      let li_ok = No.lt_trans Any_strict left_ok No.minusomega_lt_plusomega in
      let first = unparse_abs xs li li_ok No.minusomega_lt_plusomega in
      let last = unparse vars body Interval.entire ri in
      unlocated (infix ~notn ~ws:[] ~first ~inner:Emp ~last ~left_ok ~right_ok)
  | _ ->
      let first =
        unparse_abs xs Interval.entire (No.le_plusomega No.minus_omega) No.minusomega_lt_plusomega
      in
      let last = unparse vars body Interval.entire Interval.entire in
      let left_ok = No.le_refl No.minus_omega in
      let right_ok = No.le_refl No.minus_omega in
      parenthesize (unlocated (infix ~notn ~ws:[] ~first ~inner:Emp ~last ~left_ok ~right_ok))

and unparse_act :
    type n lt ls rt rs a b.
    n Names.t ->
    unparser ->
    (a, b) deg ->
    (lt, ls) Interval.tt ->
    (rt, rs) Interval.tt ->
    (lt, ls, rt, rs) parse located =
 fun vars tm s li ri ->
  match is_id_deg s with
  | Some () -> tm.unparse li ri
  | None -> (
      match name_of_deg s with
      | Some str -> unparse_spine vars (`Degen str) (Snoc (Emp, tm)) li ri
      | None -> unlocated (Superscript (Some (tm.unparse li Interval.empty), string_of_deg s, [])))

(* We group together all the 0-dimensional dependent pi-types in a notation, so we recursively descend through the term picking those up until we find a non-pi-type, a higher-dimensional pi-type, or a non-dependent pi-type, in which case we pass it off to unparse_pis_final. *)
and unparse_pis :
    type n lt ls rt rs.
    n Names.t ->
    unparser Bwd.t ->
    (n, kinetic) term ->
    (lt, ls) Interval.tt ->
    (rt, rs) Interval.tt ->
    (lt, ls, rt, rs) parse located =
 fun vars accum tm li ri ->
  match tm with
  | Pi (x, doms, cods) -> (
      match (x, compare (CubeOf.dim doms) D.zero) with
      | Some x, Eq ->
          let x, newvars = Names.add_normals vars (CubeOf.singleton (Some x)) in
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
          let _, newvars = Names.add_normals vars (CubeOf.singleton None) in
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

(* The arrow in both kinds of pi-type is (un)parsed as a binary operator.  In the dependent case, its left-hand argument looks like an "application spine" of ascribed variables.  Of course, it may have to be parenthesized. *)
and unparse_arrow :
    type n lt ls rt rs.
    unparser ->
    unparser ->
    (lt, ls) Interval.tt ->
    (rt, rs) Interval.tt ->
    (lt, ls, rt, rs) parse located =
 fun dom cod li ri ->
  match (Interval.contains li No.zero, Interval.contains ri No.zero) with
  | Some left_ok, Some right_ok ->
      let first = dom.unparse li (interval_left arrow) in
      let last = cod.unparse (interval_right arrow) ri in
      unlocated (infix ~notn:arrow ~ws:[] ~first ~inner:Emp ~last ~left_ok ~right_ok)
  | _ ->
      let first = dom.unparse Interval.entire (interval_left arrow) in
      let last = cod.unparse (interval_right arrow) Interval.entire in
      let left_ok = No.minusomega_lt_zero in
      let right_ok = No.minusomega_lt_zero in
      parenthesize (unlocated (infix ~notn:arrow ~ws:[] ~first ~inner:Emp ~last ~left_ok ~right_ok))

and unparse_pis_final :
    type n lt ls rt rs.
    n Names.t ->
    unparser Bwd.t ->
    unparser ->
    (lt, ls) Interval.tt ->
    (rt, rs) Interval.tt ->
    (lt, ls, rt, rs) parse located =
 fun vars accum tm li ri ->
  match split_first accum with
  | None -> tm.unparse li ri
  | Some (dom0, accum) ->
      unparse_arrow
        { unparse = (fun li ri -> unparse_spine vars (`Unparser dom0) accum li ri) }
        tm li ri

(* Unparse a single domain of a dependent pi-type. *)
and unparse_pi_dom :
    type lt ls rt rs.
    string ->
    (No.minus_omega, No.strict, No.minus_omega, No.nonstrict) parse located ->
    (lt, ls, rt, rs) parse located =
 fun x dom ->
  unlocated
    (outfix ~notn:parens ~ws:[]
       ~inner:
         (Snoc
            ( Emp,
              Term
                (unlocated
                   (infix ~notn:asc ~ws:[]
                      ~first:(unlocated (Ident ([ x ], [])))
                      ~inner:Emp ~last:dom ~left_ok:(No.le_refl No.minus_omega)
                      ~right_ok:(No.le_refl No.minus_omega))) )))

(* See the explanation of this function in Core.Reporter. *)
let () =
  Reporter.printer :=
    fun pr ->
      Reporter.try_with ~fatal:(fun d ->
          Reporter.emit (Error_printing_error d.message);
          Printed ((fun ppf () -> Format.pp_print_string ppf "PRINTING_ERROR"), ()))
      @@ fun () ->
      match pr with
      | PUnit -> Printed ((fun _ () -> ()), ())
      | PString str -> Printed (Uuseg_string.pp_utf_8, str)
      | PLevel i -> Printed ((fun ppf i -> Format.fprintf ppf "(%d,%d)" (fst i) (snd i)), i)
      | PTerm (ctx, tm) ->
          Printed
            (Print.pp_term `None, Term (unparse (Ctx.names ctx) tm Interval.entire Interval.entire))
      | PVal (ctx, tm) ->
          Printed
            ( Print.pp_term `None,
              Term
                (unparse (Ctx.names ctx) (Readback.readback_val ctx tm) Interval.entire
                   Interval.entire) )
      | PNormal (ctx, tm) ->
          Printed
            ( Print.pp_term `None,
              Term
                (unparse (Ctx.names ctx) (Readback.readback_nf ctx tm) Interval.entire
                   Interval.entire) )
      | PUninst (ctx, tm) ->
          Printed
            ( Print.pp_term `None,
              Term
                (unparse (Ctx.names ctx) (Readback.readback_uninst ctx tm) Interval.entire
                   Interval.entire) )
      | PConstant name ->
          Printed
            ((fun ppf x -> Uuseg_string.pp_utf_8 ppf (String.concat "." x)), Scope.name_of name)
      | Dump.Val tm -> Printed (Dump.value, tm)
      | Dump.Uninst tm -> Printed (Dump.uninst, tm)
      | Dump.Head h -> Printed (Dump.head, h)
      | Dump.Binder b -> Printed (Dump.binder, b)
      | Dump.Term tm -> Printed (Dump.term, tm)
      | Dump.Env e -> Printed (Dump.env, e)
      | _ -> raise (Failure "unknown printable")

(* Hack to ensure the above code is executed. *)
let install () = ()
