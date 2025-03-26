open Bwd
open Bwd.Infix
open Util
open Tbwd
open Bwd_extra
open Dim
open Core
open Term
open Notation
open Builtins
open Reporter
open Printable
open Range
open Readback
module StringMap = Map.Make (String)

(* If the head of an application spine is a constant or constructor, and it has an associated notation, and there are enough of the supplied arguments to instantiate the notation, split off that many arguments and return the notation, those arguments permuted to match the order of the pattern variables in the notation, the symbols to intersperse with them, and the remaining arguments. *)
let get_notation head args =
  let open Monad.Ops (Monad.Maybe) in
  let* { key = _; notn; pat_vars; val_vars; inner_symbols } =
    match head with
    | `Term (Const c) -> Situation.Current.unparse (`Constant c)
    | `Constr c -> Situation.Current.unparse (`Constr (c, Bwd.length args))
    (* TODO: Can we associate notations to Fields too? *)
    | _ -> None in
  (* There's probably a more efficient way to do this that doesn't involve converting to and from forwards lists, but this way is more natural and easier to understand, and I think this is unlikely to be a performance bottleneck. *)
  let rec take_labeled labels elts acc =
    match (labels, elts) with
    | [], _ -> return (acc, elts)
    | _ :: _, [] -> None
    | k :: labels, x :: elts -> take_labeled labels elts (acc |> StringMap.add k x) in
  let* first, rest = take_labeled val_vars (Bwd.to_list args) StringMap.empty in
  let first =
    List.map (fun k -> StringMap.find_opt k first <|> Anomaly "not found in get_notation") pat_vars
  in
  (* Constructors don't belong to a function-type, so their notation can't be applied to "more arguments" as a function.  Thus, if there are more arguments leftover, it means that the constructor is being used at a different datatype that takes a different number of arguments, and so the notation shouldn't be applied at all (just as if there were too few arguments). *)
  match (head, rest) with
  | `Constr _, _ :: _ -> None
  | _ -> return (notn, first, inner_symbols, Bwd.of_list rest)

(* Put parentheses around a term. *)
let parenthesize tm =
  unlocated
    (outfix ~notn:parens ~inner:(Multiple ((LParen, []), Snoc (Emp, Term tm), (RParen, []))))

(* Put them only if they aren't there already *)
let parenthesize_maybe (tm : ('lt, 'ls, 'rt, 'rs) parse located) =
  match tm.value with
  | Notn ((Parens, _), _) -> tm
  | _ -> parenthesize tm

(* A "delayed" result of unparsing that needs only to know the tightness intervals to produce a result. *)
type unparser = {
  unparse :
    'lt 'ls 'rt 'rs.
    ('lt, 'ls) No.iinterval -> ('rt, 'rs) No.iinterval -> ('lt, 'ls, 'rt, 'rs) parse located;
}

let observations_of_symbols :
    unparser list ->
    [ `Single of Token.t | `Multiple of Token.t * Token.t option list * Token.t ] ->
    observations =
 fun args inner_symbols ->
  match inner_symbols with
  | `Single tok -> Single (tok, [])
  | `Multiple (first, inner, last) ->
      Multiple
        ( (first, []),
          fst
            (List.fold_left
               (fun (acc, args) symbol ->
                 match (symbol, args) with
                 | Some tok, _ -> (Snoc (acc, Token (tok, [])), args)
                 | None, tm :: args ->
                     (Snoc (acc, Term (tm.unparse No.Interval.entire No.Interval.entire)), args)
                 | None, [] -> fatal (Anomaly "missing argument in observations_of_symbols"))
               (Emp, args) inner),
          (last, []) )

(* Unparse a notation together with all its arguments. *)
let unparse_notation : type left tight right lt ls rt rs.
    (left, tight, right) notation ->
    unparser list ->
    [ `Single of Token.t | `Multiple of Token.t * Token.t option list * Token.t ] ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun notn args inner_symbols li ri ->
  let t = tightness notn in
  (* Based on the fixity of the notation, we have to extract the first and/or last argument to treat differently.  In each case except for outfix, we also have to test whether the notation fits in the given tightness interval, and if not, parenthesize it. *)
  match (left notn, right notn) with
  | Open _, Open _ -> (
      match List_extra.split_last args with
      | Some (first :: inner, last) -> (
          let inner = observations_of_symbols inner inner_symbols in
          match (No.Interval.contains li t, No.Interval.contains ri t) with
          | Some left_ok, Some right_ok ->
              let first = first.unparse li (interval_left notn) in
              let last = last.unparse (interval_right notn) ri in
              unlocated (infix ~notn ~first ~inner ~last ~left_ok ~right_ok)
          | _ ->
              let first = first.unparse No.Interval.entire (interval_left notn) in
              let last = last.unparse (interval_right notn) No.Interval.entire in
              let left_ok = No.minusomega_le t in
              let right_ok = No.minusomega_le t in
              parenthesize (unlocated (infix ~notn ~first ~inner ~last ~left_ok ~right_ok)))
      | _ -> fatal (Anomaly "missing arguments unparsing infix"))
  | Closed, Open _ -> (
      match List_extra.split_last args with
      | Some (inner, last) -> (
          let inner = observations_of_symbols inner inner_symbols in
          match No.Interval.contains ri t with
          | Some right_ok ->
              let last = last.unparse (interval_right notn) ri in
              unlocated (prefix ~notn ~inner ~last ~right_ok)
          | _ ->
              let last = last.unparse (interval_right notn) No.Interval.entire in
              let right_ok = No.minusomega_le t in
              parenthesize (unlocated (prefix ~notn ~inner ~last ~right_ok)))
      | _ -> fatal (Anomaly "missing argument unparsing prefix"))
  | Open _, Closed -> (
      match args with
      | first :: inner -> (
          let inner = observations_of_symbols inner inner_symbols in
          match No.Interval.contains li t with
          | Some left_ok ->
              let first = first.unparse li (interval_left notn) in
              unlocated (postfix ~notn ~first ~inner ~left_ok)
          | _ ->
              let first = first.unparse No.Interval.entire (interval_left notn) in
              let left_ok = No.minusomega_le t in
              parenthesize (unlocated (postfix ~notn ~first ~inner ~left_ok)))
      | _ -> fatal (Anomaly "missing argument unparsing postfix"))
  | Closed, Closed ->
      let inner = observations_of_symbols args inner_symbols in
      unlocated (outfix ~notn ~inner)

(* Unparse a variable name, possibly anonymous. *)
let unparse_var : type lt ls rt rs. string option -> (lt, ls, rt, rs) parse located = function
  | Some x -> unlocated (Ident ([ x ], []))
  | None -> unlocated (Placeholder [])

(* Unparse a Bwd of variables to occur in an iterated abstraction.  If there is more than one variable, the result is an "application spine".  Can occur in any tightness interval that contains +ω. *)
let rec unparse_abs : type li ls ri rs.
    string option Bwd.t ->
    (li, ls) No.iinterval ->
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
    | Term.Constr (c, _, []) when c = Constr.intern "zero" ->
        Some (Ident (String.split_on_char '.' (Q.to_string (Q.of_int k)), []))
    | Constr (c, _, [ arg ]) when c = Constr.intern "suc" -> getsucs (CubeOf.find_top arg) (k + 1)
    | _ -> None in
  getsucs tm 0

let rec get_list : type n.
    (n, kinetic) term -> (n, kinetic) term Bwd.t -> (n, kinetic) term Bwd.t option =
 fun tm elts ->
  match tm with
  | Term.Constr (c, _, []) when c = Constr.intern "nil" -> Some elts
  | Constr (c, _, [ car; cdr ]) when c = Constr.intern "cons" ->
      get_list (CubeOf.find_top cdr) (Snoc (elts, CubeOf.find_top car))
  | _ -> None

let rec get_bwd : type n.
    (n, kinetic) term -> (n, kinetic) term list -> (n, kinetic) term Bwd.t option =
 fun tm elts ->
  match tm with
  | Term.Constr (c, _, []) when c = Constr.intern "emp" -> Some (Bwd.of_list elts)
  | Constr (c, _, [ rdc; rac ]) when c = Constr.intern "snoc" ->
      get_bwd (CubeOf.find_top rdc) (CubeOf.find_top rac :: elts)
  | _ -> None

let synths : type n. (n, kinetic) term -> bool = function
  | Var _ | Const _
  | Meta (_, _)
  | MetaEnv (_, _)
  | Field (_, _, _)
  | UU _
  | Inst (_, _)
  | Pi (_, _, _)
  | App (_, _)
  | Act (_, _)
  | Let (_, _, _) -> true
  | Constr (_, _, _) | Lam (_, _) | Struct (_, _, _, _) -> false

(* Given a term, extract its head and arguments as an application spine.  If the spine contains a field projection, stop there and return only the arguments after it, noting the field name and what it is applied to (which itself be another spine). *)
let rec get_spine : type n.
    (n, kinetic) term ->
    [ `App of (n, kinetic) term * ((n, kinetic) term * [ `Implicit | `Explicit ]) Bwd.t
    | `Field of
      (n, kinetic) term * string * int list * ((n, kinetic) term * [ `Implicit | `Explicit ]) Bwd.t
    ] =
 fun tm ->
  match tm with
  | App (fn, arg) -> (
      let module M = CubeOf.Monadic (Monad.State (struct
        type t = ((n, kinetic) term * [ `Implicit | `Explicit ]) Bwd.t
      end)) in
      (* To append the entries in a cube to a Bwd, we iterate through it with a Bwd state. *)
      let append_bwd args =
        let all_args = not (synths (CubeOf.find_top arg)) in
        snd
          (M.miterM
             {
               it =
                 (fun fa [ x ] s ->
                   match
                     ( Implicitboundaries.functions (),
                       Display.function_boundaries (),
                       is_id_sface fa,
                       all_args )
                   with
                   | `Implicit, `Hide, None, false -> ((), s)
                   | `Implicit, _, None, _ -> ((), Snoc (s, (x, `Implicit)))
                   | _ -> ((), Snoc (s, (x, `Explicit))));
             }
             [ arg ] args) in
      match get_spine fn with
      | `App (head, args) -> `App (head, append_bwd args)
      | `Field (head, fld, ins, args) -> `Field (head, fld, ins, append_bwd args))
  | Field (head, fld, ins) -> `Field (head, Field.to_string fld, ints_of_ins ins, Emp)
  (* We have to look through identity degeneracies here. *)
  | Act (body, s) -> (
      match is_id_deg s with
      | Some _ -> get_spine body
      | None -> `App (tm, Emp))
  | tm -> `App (tm, Emp)

(* The primary unparsing function.  Given the variable names, unparse a term into given tightness intervals. *)
let rec unparse : type n lt ls rt rs s.
    n Names.t ->
    (n, s) term ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun vars tm li ri ->
  match tm with
  | Var x -> unlocated (Ident (Names.lookup vars x, []))
  | Const c -> (
      match Situation.Current.unparse (`Constant c) with
      | Some { key = _; notn = Wrap notn; pat_vars = []; val_vars = []; inner_symbols } ->
          unparse_notation notn [] inner_symbols li ri
      | _ -> unlocated (Ident (Scope.name_of c, [])))
  | Meta (v, _) ->
      unlocated (Ident ([ (if Display.metas () == `Numbered then Meta.name v else "?") ], []))
  (* NB: We don't currently print the arguments of a metavariable. *)
  | MetaEnv (v, _) ->
      unlocated
        (Ident ([ (if Display.metas () == `Numbered then Meta.name v ^ "{…}" else "?") ], []))
  | Field (tm, fld, ins) ->
      unparse_spine vars (`Field (tm, Field.to_string fld, ints_of_ins ins)) Emp li ri
  | UU n ->
      unparse_act vars
        {
          unparse =
            (fun _ _ -> unlocated (outfix ~notn:universe ~inner:(Single (Ident [ "Type" ], []))));
        }
        (deg_zero n) li ri
  | Inst (ty, tyargs) ->
      (* We unparse instantiations like application spines, since that is how they are represented in user syntax.
         TODO: How can we allow special notations for some instantiations, like x=y for Id A x y? *)
      let module M = TubeOf.Monadic (Monad.State (struct
        type t = unparser Bwd.t
      end)) in
      (* To append the entries in a cube to a Bwd, we iterate through it with a Bwd state. *)
      let (), args =
        M.miterM
          {
            it =
              (fun fa [ x ] s ->
                let (Tface_of fa1) = codim1_envelope fa in
                let all_args = not (synths (TubeOf.find tyargs fa1)) in
                match
                  (Implicitboundaries.types (), Display.type_boundaries (), is_codim1 fa, all_args)
                with
                | `Implicit, `Hide, None, false -> ((), s)
                | `Implicit, _, None, _ -> ((), Snoc (s, make_unparser_implicit vars (x, `Implicit)))
                | _ -> ((), Snoc (s, make_unparser_implicit vars (x, `Explicit))));
          }
          [ tyargs ] Emp in
      unparse_spine vars (`Term ty) args li ri
  | Pi _ -> unparse_pis vars Emp tm li ri
  | App _ -> (
      match get_spine tm with
      | `App (fn, args) ->
          unparse_spine vars (`Term fn) (Bwd.map (make_unparser_implicit vars) args) li ri
      | `Field (head, fld, ins, args) ->
          unparse_spine vars
            (`Field (head, fld, ins))
            (Bwd.map (make_unparser_implicit vars) args)
            li ri)
  | Act (tm, s) -> unparse_act vars { unparse = (fun li ri -> unparse vars tm li ri) } s li ri
  | Let (x, tm, body) -> (
      let tm = unparse vars tm No.Interval.entire No.Interval.entire in
      (* If a let-in doesn't fit in its interval, we have to parenthesize it. *)
      let x, vars = Names.add_cube D.zero vars x in
      match No.Interval.contains ri No.minus_omega with
      | Some right_ok ->
          let body = unparse vars body No.Interval.entire ri in
          unlocated
            (prefix ~notn:letin
               ~inner:
                 (Multiple
                    ( (Let, []),
                      Emp <: Term (unparse_var x) <: Token (Coloneq, []) <: Term tm,
                      (In, []) ))
               ~last:body ~right_ok)
      | None ->
          let body = unparse vars body No.Interval.entire No.Interval.entire in
          let right_ok = No.le_refl No.minus_omega in
          parenthesize
            (unlocated
               (prefix ~notn:letin
                  ~inner:
                    (Multiple
                       ( (Let, []),
                         Emp <: Term (unparse_var x) <: Token (Coloneq, []) <: Term tm,
                         (In, []) ))
                  ~last:body ~right_ok)))
  | Lam (Variables (m, _, _), _) ->
      let cube =
        match D.compare m D.zero with
        | Eq -> `Normal
        | Neq -> `Cube in
      unparse_lam cube vars Emp tm li ri
  | Struct
      (type m et)
      ((Eta, _, fields, _) : (s, et) eta * m D.t * (m * n * s * et) StructfieldAbwd.t * s energy) ->
      unlocated
        (outfix ~notn:parens
           ~inner:
             (Multiple
                ( (LParen, []),
                  Bwd_extra.intersperse
                    (Token (Op ",", []))
                    (Bwd.fold_left
                       (fun acc
                            (Term.StructfieldAbwd.Entry
                               (type i)
                               ((fld, structfield) : i Field.t * (i, m * n * s * et) Structfield.t))
                          ->
                         match structfield with
                         | Lower (fldtm, lbl) ->
                             let fldtm = unparse vars fldtm No.Interval.entire No.Interval.entire in
                             Snoc
                               ( acc,
                                 Term
                                   (match lbl with
                                   | `Labeled ->
                                       unlocated
                                         (infix ~notn:coloneq
                                            ~first:(unlocated (Ident ([ Field.to_string fld ], [])))
                                            ~inner:(Single (Coloneq, []))
                                            ~last:fldtm ~left_ok:(No.le_refl No.minus_omega)
                                            ~right_ok:(No.le_refl No.minus_omega))
                                   (* An unlabeled 1-tuple is currently unparsed as (_ := M). *)
                                   | `Unlabeled when Bwd.length fields = 1 ->
                                       unlocated
                                         (infix ~notn:coloneq ~first:(unlocated (Placeholder []))
                                            ~inner:(Single (Coloneq, []))
                                            ~last:fldtm ~left_ok:(No.le_refl No.minus_omega)
                                            ~right_ok:(No.le_refl No.minus_omega))
                                   | `Unlabeled -> fldtm) ))
                       Emp fields),
                  (RParen, []) )))
  | Constr (c, _, args) -> (
      (* TODO: This doesn't print the dimension.  This is correct since constructors don't have to (and in fact *can't* be) written with their dimension, but it could also be somewhat confusing, e.g. printing "refl (0:N)" yields just "0", and similarly "refl (nil. : List N)" yields "nil.". *)
      match unparse_numeral tm with
      | Some tm -> unlocated tm
      | None ->
          let args = of_list_map (fun x -> make_unparser vars (CubeOf.find_top x)) args in
          unparse_spine vars (`Constr c) args li ri)
  | Realize tm -> unparse vars tm li ri
  | Canonical _ -> fatal (Unimplemented "unparsing canonical types")
  | Struct (Noeta, _, _, _) -> fatal (Unimplemented "unparsing comatches")
  | Match _ -> fatal (Unimplemented "unparsing matches")

(* The master unparsing function can easily be delayed. *)
and make_unparser : type n. n Names.t -> (n, kinetic) term -> unparser =
 fun vars tm -> { unparse = (fun li ri -> unparse vars tm li ri) }

(* A version that wraps implicit arguments in braces. *)
and make_unparser_implicit : type n.
    n Names.t -> (n, kinetic) term * [ `Implicit | `Explicit ] -> unparser =
 fun vars (tm, i) ->
  match i with
  | `Explicit -> { unparse = (fun li ri -> unparse vars tm li ri) }
  | `Implicit ->
      {
        unparse =
          (fun _ _ ->
            let tm = unparse vars tm No.Interval.entire No.Interval.entire in
            unlocated
              (outfix ~notn:Postprocess.braces
                 ~inner:(Multiple ((LBrace, []), Snoc (Emp, Term tm), (RBrace, [])))));
      }

(* Unparse a spine with its arguments whose head could be many things: an as-yet-not-unparsed term, a constructor, a field projection, a degeneracy, or a general delayed unparsing. *)
and unparse_spine : type n lt ls rt rs.
    n Names.t ->
    [ `Term of (n, kinetic) term
    | `Constr of Constr.t
    | `Field of (n, kinetic) term * string * int list
    | `Degen of string
    | `Unparser of unparser ] ->
    unparser Bwd.t ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun vars head args li ri ->
  (* First we check whether the head is a term with an associated notation, and if so whether it is applied to enough arguments to instantiate that notation. *)
  match get_notation head args with
  (* If it's applied to exactly the right number of arguments, we unparse it as that notation. *)
  | Some (Wrap notn, args, inner_symbols, Emp) -> unparse_notation notn args inner_symbols li ri
  (* Otherwise, the unparsed notation has to be applied to the rest of the arguments as a spine. *)
  | Some (Wrap notn, args, inner_symbols, (Snoc _ as rest)) ->
      unparse_spine vars
        (`Unparser { unparse = (fun li ri -> unparse_notation notn args inner_symbols li ri) })
        rest li ri
  (* If not, we proceed to unparse it as an application spine, recursively. *)
  | None -> (
      match args with
      | Emp -> (
          match head with
          | `Term tm -> unparse vars tm li ri
          | `Constr c -> unlocated (Constr (Constr.to_string c, []))
          | `Field (tm, fld, ins) -> unparse_field vars tm fld ins li ri
          | `Degen s -> unlocated (Ident ([ s ], []))
          | `Unparser tm -> tm.unparse li ri)
      | Snoc (args, arg) -> (
          (* As before, if the application doesn't fit in its tightness interval, we have to parenthesize it. *)
          match (No.Interval.contains li No.plus_omega, No.Interval.contains ri No.plus_omega) with
          | Some left_ok, Some right_ok ->
              let fn = unparse_spine vars head args li No.Interval.plus_omega_only in
              let arg = arg.unparse No.Interval.empty ri in
              (* We parenthesize the argument if the style dictates and it doesn't already have parentheses. *)
              let arg =
                match Display.argstyle () with
                | `Spaces -> arg
                | `Parens -> parenthesize_maybe arg in
              unlocated (App { fn; arg; left_ok; right_ok })
          | _ ->
              let fn =
                unparse_spine vars head args No.Interval.plus_omega_only No.Interval.plus_omega_only
              in
              let arg = arg.unparse No.Interval.empty No.Interval.plus_omega_only in
              let arg =
                match Display.argstyle () with
                | `Spaces -> arg
                | `Parens -> parenthesize_maybe arg in
              let left_ok = No.le_refl No.plus_omega in
              let right_ok = No.le_refl No.plus_omega in
              parenthesize (unlocated (App { fn; arg; left_ok; right_ok }))))

and unparse_field : type n lt ls rt rs.
    n Names.t ->
    (n, kinetic) term ->
    string ->
    int list ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun vars tm fld ins li ri ->
  match unparse_field_var vars tm fld with
  | Some res -> res
  | None -> (
      match (No.Interval.contains li No.plus_omega, No.Interval.contains ri No.plus_omega) with
      | Some left_ok, Some right_ok ->
          let fn = unparse vars tm li No.Interval.plus_omega_only in
          let arg = unlocated (Field (fld, List.map string_of_int ins, [])) in
          unlocated (App { fn; arg; left_ok; right_ok })
      | _ ->
          let fn = unparse vars tm No.Interval.plus_omega_only No.Interval.plus_omega_only in
          let arg = unlocated (Field (fld, List.map string_of_int ins, [])) in
          let left_ok = No.le_refl No.plus_omega in
          let right_ok = No.le_refl No.plus_omega in
          parenthesize (unlocated (App { fn; arg; left_ok; right_ok })))

and unparse_field_var : type n lt ls rt rs.
    n Names.t -> (n, kinetic) term -> string -> (lt, ls, rt, rs) parse located option =
 fun vars tm fld ->
  match tm with
  | Var x -> (
      match Names.lookup_field vars x fld with
      (* If the field got used up by the lookup, we just return the variable. *)
      | Some name -> Some (unlocated (Ident (name, [])))
      (* If the field is still leftover after the lookup, we unparse it as a field. *)
      | None -> None)
  | Act (tm, deg) -> (
      match is_id_deg deg with
      | Some _ -> unparse_field_var vars tm fld
      | None -> None)
  | _ -> None

(* For unparsing an iterated abstraction, we group together the fully-normal variables and at-least-partially-cube variables, since they have different notations.  There is no notation for partially-cube variables, so we make them fully cube.  We recursively descend through the structure of the term, storing in 'cube' which kind of variable we are picking up and continuing until we find either a non-abstraction or an abstraction of the wrong type.  *)
and unparse_lam : type n lt ls rt rs s.
    [ `Cube | `Normal ] ->
    n Names.t ->
    string option Bwd.t ->
    (n, s) term ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun cube vars xs body li ri ->
  match body with
  | Lam ((Variables (m, _, _) as boundvars), inner) -> (
      match (cube, D.compare m D.zero) with
      | `Normal, Eq | `Cube, Neq ->
          let Variables (_, _, x), vars = Names.add vars boundvars in
          let module Fold = NICubeOf.Traverse (struct
            type 'acc t = string option Bwd.t
          end) in
          (* Apparently we need to define the folding function explicitly with a type to make it come out sufficiently polymorphic. *)
          let folder : type m left right.
              string option Bwd.t ->
              (left, m, string option, right) NFamOf.t ->
              (left, m, unit, right) NFamOf.t * string option Bwd.t =
           fun acc (NFamOf x) -> (NFamOf (), Snoc (acc, x)) in
          unparse_lam cube vars
            (snd (Fold.fold_map_left { foldmap = (fun _ acc x -> folder acc x) } xs x))
            inner li ri
      | _ -> unparse_lam_done cube vars xs body li ri)
  | _ -> unparse_lam_done cube vars xs body li ri

(* Once we hit either a non-abstraction or a different kind of abstraction, we pick the appropriate notation to use for the abstraction, depending on the kind of variables.  Note that both are (un)parsed as binary operators whose left-hand argument is an "application spine" of variables, produced here by unparse_abs. *)
and unparse_lam_done : type n lt ls rt rs s.
    [ `Cube | `Normal ] ->
    n Names.t ->
    string option Bwd.t ->
    (n, s) term ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun cube vars xs body li ri ->
  let notn, mapsto =
    match cube with
    | `Cube -> (cubeabs, Token.DblMapsto)
    | `Normal -> (abs, Mapsto) in
  (* Of course, if we don't fit in the tightness interval, we have to parenthesize. *)
  match (No.Interval.contains li No.minus_omega, No.Interval.contains ri No.minus_omega) with
  | Some left_ok, Some right_ok ->
      let li_ok = No.lt_trans Any_strict left_ok No.minusomega_lt_plusomega in
      let first = unparse_abs xs li li_ok No.minusomega_lt_plusomega in
      let last = unparse vars body No.Interval.entire ri in
      unlocated (infix ~notn ~first ~inner:(Single (mapsto, [])) ~last ~left_ok ~right_ok)
  | _ ->
      let first =
        unparse_abs xs No.Interval.entire (No.le_plusomega No.minus_omega)
          No.minusomega_lt_plusomega in
      let last = unparse vars body No.Interval.entire No.Interval.entire in
      let left_ok = No.le_refl No.minus_omega in
      let right_ok = No.le_refl No.minus_omega in
      parenthesize
        (unlocated (infix ~notn ~first ~inner:(Single (mapsto, [])) ~last ~left_ok ~right_ok))

and unparse_act : type n lt ls rt rs a b.
    n Names.t ->
    unparser ->
    (a, b) deg ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun vars tm s li ri ->
  match is_id_deg s with
  | Some _ -> tm.unparse li ri
  | None -> (
      match name_of_deg s with
      | Some str -> unparse_spine vars (`Degen str) (Snoc (Emp, tm)) li ri
      | None ->
          unlocated (Superscript (Some (tm.unparse li No.Interval.empty), string_of_deg s, [])))

(* We group together all the 0-dimensional dependent pi-types in a notation, so we recursively descend through the term picking those up until we find a non-pi-type, a higher-dimensional pi-type, or a non-dependent pi-type, in which case we pass it off to unparse_pis_final. *)
and unparse_pis : type n lt ls rt rs.
    n Names.t ->
    unparser Bwd.t ->
    (n, kinetic) term ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun vars accum tm li ri ->
  match tm with
  | Pi (x, doms, cods) -> (
      match (x, D.compare (CubeOf.dim doms) D.zero) with
      | Some x, Eq ->
          let Variables (_, _, x), newvars = Names.add vars (singleton_variables D.zero (Some x)) in
          unparse_pis newvars
            (Snoc
               ( accum,
                 {
                   unparse =
                     (fun _ _ ->
                       unparse_pi_dom
                         (NICubeOf.find_top x <|> Anomaly "missing top in unparse_pis")
                         (unparse vars (CubeOf.find_top doms) (interval_right asc)
                            No.Interval.entire));
                 } ))
            (CodCube.find_top cods) li ri
      | None, Eq ->
          let _, newvars = Names.add vars (singleton_variables D.zero None) in
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
          let module S = Monad.State (struct
            type t = unparser Bwd.t
          end) in
          let module MOf = CubeOf.Monadic (S) in
          let all_args = not (synths (CubeOf.find_top doms)) in
          let (), args =
            MOf.miterM
              {
                it =
                  (fun fa [ dom ] args ->
                    let newdoms =
                      match
                        ( Implicitboundaries.functions (),
                          Display.function_boundaries (),
                          is_id_sface fa,
                          all_args )
                      with
                      | `Implicit, `Hide, None, false -> []
                      | `Implicit, _, None, _ -> [ (dom, `Implicit) ]
                      | _ -> [ (dom, `Explicit) ] in
                    ((), Bwd.append args (List.map (make_unparser_implicit vars) newdoms)));
              }
              [ doms ] Emp in
          let module MCod = CodCube.Monadic (S) in
          let (), args =
            MCod.miterM
              {
                it =
                  (fun fa [ cod ] args ->
                    let impl =
                      match (Implicitboundaries.functions (), is_id_sface fa) with
                      | `Implicit, None -> `Implicit
                      | _ -> `Explicit in
                    ( (),
                      Snoc
                        ( args,
                          make_unparser_implicit vars
                            (Lam (singleton_variables (dom_sface fa) x, cod), impl) ) ));
              }
              [ cods ] args in
          unparse_pis_final vars accum
            {
              unparse =
                (fun li ri ->
                  unparse_spine vars
                    (`Term (Act (Const Pi.const, deg_zero (CubeOf.dim doms))))
                    args li ri);
            }
            li ri)
  | _ -> unparse_pis_final vars accum (make_unparser vars tm) li ri

(* The arrow in both kinds of pi-type is (un)parsed as a binary operator.  In the dependent case, its left-hand argument looks like an "application spine" of ascribed variables.  Of course, it may have to be parenthesized. *)
and unparse_arrow : type lt ls rt rs.
    unparser ->
    unparser ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun dom cod li ri ->
  match (No.Interval.contains li No.zero, No.Interval.contains ri No.zero) with
  | Some left_ok, Some right_ok ->
      let first = dom.unparse li (interval_left arrow) in
      let last = cod.unparse (interval_right arrow) ri in
      unlocated (infix ~notn:arrow ~first ~inner:(Single (Arrow, [])) ~last ~left_ok ~right_ok)
  | _ ->
      let first = dom.unparse No.Interval.entire (interval_left arrow) in
      let last = cod.unparse (interval_right arrow) No.Interval.entire in
      let left_ok = No.minusomega_lt_zero in
      let right_ok = No.minusomega_lt_zero in
      parenthesize
        (unlocated (infix ~notn:arrow ~first ~inner:(Single (Arrow, [])) ~last ~left_ok ~right_ok))

and unparse_pis_final : type n lt ls rt rs.
    n Names.t ->
    unparser Bwd.t ->
    unparser ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun vars accum tm li ri ->
  match split_first accum with
  | None -> tm.unparse li ri
  | Some (dom0, accum) ->
      unparse_arrow
        { unparse = (fun li ri -> unparse_spine vars (`Unparser dom0) accum li ri) }
        tm li ri

(* Unparse a single domain of a dependent pi-type. *)
and unparse_pi_dom : type lt ls rt rs.
    string ->
    (No.minus_omega, No.strict, No.minus_omega, No.nonstrict) parse located ->
    (lt, ls, rt, rs) parse located =
 fun x dom ->
  unlocated
    (outfix ~notn:parens
       ~inner:
         (Multiple
            ( (LParen, []),
              Snoc
                ( Emp,
                  Term
                    (unlocated
                       (infix ~notn:asc
                          ~first:(unlocated (Ident ([ x ], [])))
                          ~inner:(Single (Colon, []))
                          ~last:dom ~left_ok:(No.le_refl No.minus_omega)
                          ~right_ok:(No.le_refl No.minus_omega))) ),
              (RParen, []) )))

(* Unparse a term context, given a vector of variable names obtained by pre-uniquifying a variable list, and a list of names for by the empty context that nevertheless remembers the variables in that vector, as produced by Names.uniquify_vars.  Yields not only the list of unparsed terms/types, but a corresponding list of names that can be used to unparse further objects in that context. *)
let rec unparse_ctx : type a b.
    emp Names.t ->
    [ `Locked | `Unlocked ] ->
    (string * [ `Original | `Renamed ], a) Bwv.t ->
    (a, b) ordered_termctx ->
    b Names.t
    * (string * [ `Original | `Renamed | `Locked ] * wrapped_parse option * wrapped_parse) Bwd.t =
 fun names lock vars ctx ->
  let merge_orig =
    match lock with
    | `Locked -> fun _ -> `Locked
    | `Unlocked -> fun o -> (o :> [ `Original | `Renamed | `Locked ]) in
  let module S = struct
    type t =
      (string * [ `Original | `Renamed | `Locked ] * wrapped_parse option * wrapped_parse) Bwd.t
  end in
  let module M = CubeOf.Monadic (Monad.State (S)) in
  match ctx with
  | Emp -> (names, Emp)
  | Lock ctx -> unparse_ctx names `Locked vars ctx
  | Ext (ctx, entry, af) -> (
      let vars, xs = Bwv.unappend af vars in
      let names, result = unparse_ctx names lock vars ctx in
      match entry with
      | Invis bindings ->
          (* We treat an invisible binding as consisting of all nameless variables, and autogenerate names for them all. *)
          let x, names = Names.add_cube_autogen (CubeOf.dim bindings) names in
          let do_binding (b : b binding) (res : S.t) : unit * S.t =
            let ty = Wrap (unparse names b.ty No.Interval.entire No.Interval.entire) in
            let tm =
              Option.map
                (fun t -> Wrap (unparse names t No.Interval.entire No.Interval.entire))
                b.tm in
            ((), Snoc (res, (x, `Renamed, tm, ty))) in
          let _, result =
            M.miterM { it = (fun _ [ b ] res -> do_binding b res) } [ bindings ] result in
          (names, result)
      | Vis { dim; plusdim; vars; bindings; hasfields; fields; fplus } ->
          (* First we split off the field variables, if any. *)
          let xs, fs = Bwv.unappend fplus xs in
          (* Now we assemble the variable names we got from the uniquified variable list into a cube, iterating backwards so that the indices match those of the Bwv.  We ignore the variable names given in the context, but we use their cube to ensure statically that we got the right number of uniquified names.  *)
          let module T = struct
            type 'n t = (string * [ `Original | `Renamed ], 'n) Bwv.t
          end in
          let module Fold = NICubeOf.Traverse (T) in
          let do_var : type left right m n.
              (m, n) sface ->
              (left, m, string option, right) NFamOf.t ->
              right T.t ->
              left T.t * (left, m, string * [ `Original | `Renamed ], right) NFamOf.t =
           fun _ (NFamOf _) (Snoc (xs, x)) -> (xs, NFamOf x) in
          let _, vardata = Fold.fold_map_right { foldmap = do_var } vars xs in
          (* Then we project out the variable names alone.  TODO: Can we do this as part of the same iteration?  It would require a two-output version of the traversal.  *)
          let projector : type left right m n.
              (m, n) sface ->
              (left, m, string * [ `Original | `Renamed ], right) NFamOf.t ->
              (left, m, string option, right) NFamOf.t =
           fun _ (NFamOf (x, _)) -> NFamOf (Some x) in
          let xs = NICubeOf.map { map = projector } vardata in
          (* With the variables projected out, we add them to the Names.t.  We use Names.unsafe_add because at this point the variables have already been uniquified by Names.uniquify_vars. *)
          let fnames =
            Bwv.mmap (fun [ (x, _); (f, _, _) ] -> (Field.to_string f, x)) [ fs; fields ] in
          let names = Names.unsafe_add names (Variables (dim, plusdim, xs)) (Bwv.to_bwd fnames) in
          (* Then we iterate forwards through the bindings, unparsing them with these names and adding them to the result. *)
          let do_binding fab (b : b binding) (res : S.t) : unit * S.t =
            match (hasfields, is_id_sface fab) with
            | Has_fields, Some _ -> ((), res)
            | _ ->
                let ty = Wrap (unparse names b.ty No.Interval.entire No.Interval.entire) in
                let tm =
                  Option.map
                    (fun t -> Wrap (unparse names t No.Interval.entire No.Interval.entire))
                    b.tm in
                let (SFace_of_plus (_, fa, fb)) = sface_of_plus plusdim fab in
                let fastr = "." ^ string_of_sface fa in
                let add_fa =
                  match D.compare (cod_sface fa) D.zero with
                  | Eq -> fun y -> y
                  | Neq -> fun y -> y ^ fastr in
                let x, orig = NICubeOf.find vardata fb in
                let x = add_fa x in
                let res = Snoc (res, (x, merge_orig orig, tm, ty)) in
                ((), res) in
          let _, result =
            M.miterM { it = (fun fab [ b ] res -> do_binding fab b res) } [ bindings ] result in
          (* Finally, we iterate forwards through the fields as well, unparsing their types and adding them to the result also. *)
          let module M = Bwv.Monadic (Monad.State (S)) in
          let _, result =
            M.miterM
              (fun [ (x, orig); (_, _, ty) ] res ->
                let ty = Wrap (unparse names ty No.Interval.entire No.Interval.entire) in
                let res = Snoc (res, (x, merge_orig orig, None, ty)) in
                ((), res))
              [ fs; fields ] result in
          (names, result))

(* See the explanation of this function in Core.Reporter. *)
let () =
  let open PPrint in
  let open Print in
  Reporter.printer :=
    fun pr ->
      Reporter.try_with ~fatal:(fun d ->
          Reporter.Code.PrintingError.read () d.message;
          string "_UNPRINTABLE")
      @@ fun () ->
      Readback.Displaying.run ~env:true @@ fun () ->
      match pr with
      | PUnit -> empty
      | PInt i -> string (string_of_int i)
      | PString str -> utf8string str
      | PField f -> utf8string (Field.to_string f)
      | PConstr c -> utf8string (Constr.to_string c)
      | PLevel i -> string (Printf.sprintf "(%d,%d)" (fst i) (snd i))
      | PTerm (ctx, tm) ->
          pp_complete_term
            (Wrap (unparse (Names.of_ctx ctx) tm No.Interval.entire No.Interval.entire))
            `None
      | PVal (ctx, tm) ->
          pp_complete_term
            (Wrap
               (unparse (Names.of_ctx ctx) (readback_val ctx tm) No.Interval.entire
                  No.Interval.entire))
            `None
      | PNormal (ctx, tm) ->
          pp_complete_term
            (Wrap
               (unparse (Names.of_ctx ctx) (readback_nf ctx tm) No.Interval.entire
                  No.Interval.entire))
            `None
      | PUninst (ctx, tm) ->
          pp_complete_term
            (Wrap
               (unparse (Names.of_ctx ctx) (readback_uninst ctx tm) No.Interval.entire
                  No.Interval.entire))
            `None
      | PConstant name -> utf8string (String.concat "." (Scope.name_of name))
      | PMeta v -> utf8string (Meta.name v)
      | PHole (vars, Permute (p, ctx), ty) ->
          let vars, names = Names.uniquify_vars vars in
          let names, ctx = unparse_ctx names `Unlocked (Bwv.permute vars p) ctx in
          let ty = unparse names ty No.Interval.entire No.Interval.entire in
          pp_hole ctx (Wrap ty)
      | Dump.Val tm -> Dump.value tm
      | Dump.DeepVal (tm, n) -> Dump.dvalue n tm
      | Dump.Uninst tm -> Dump.uninst tm
      | Dump.Head h -> Dump.head h
      | Dump.Binder b -> Dump.binder b
      | Dump.Term tm -> Dump.term tm
      | Dump.Env e -> Dump.env e
      | Dump.Check e -> Dump.check e
      | _ -> fatal (Anomaly "unknown printable")

(* Hack to ensure the above code is executed. *)
let install () = ()
