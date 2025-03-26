open Bwd
open Util
open Dim
open Postprocess
open Print
open PPrint
open Core
open Raw
open Reporter
open Notation
open Monad.Ops (Monad.Maybe)
open Range
module StringSet = Set.Make (String)

module StringsSet = Set.Make (struct
  type t = string * string list

  let compare = compare
end)

let invalid str = fatal (Anomaly ("invalid notation arguments for " ^ str))

(* ********************
   Parentheses
 ******************** *)

(* Parentheses are parsed, processed, and printed along with tuples, since their notation overlaps.  But we define them here, since they are used as sub-notations in many other notations.  *)

type (_, _, _) identity += Parens : (closed, No.plus_omega, closed) identity

let parens : (closed, No.plus_omega, closed) notation = (Parens, Outfix)

(* ********************
   Braces
 ******************** *)

(* Braces were defined in Postprocess; here we say how to parse and print them, and how *not* to process them on their own. *)

let () =
  make Postprocess.braces
    {
      name = "braces";
      tree = Closed_entry (eop LBrace (term RBrace (Done_closed Postprocess.braces)));
      processor = (fun _ _ _ -> fatal Parse_error);
      print_term =
        Some
          (fun obs ->
            match obs with
            | [ Token (LBrace, wslbrace); Term body; Token (RBrace, wsrbrace) ] ->
                let ptm, wtm = pp_term body in
                ( Token.pp LBrace
                  ^^ pp_ws `None wslbrace
                  ^^ ptm
                  ^^ pp_ws `None wtm
                  ^^ Token.pp RBrace,
                  wsrbrace )
            | _ -> invalid "braces");
      print_case = None;
      is_case = (fun _ -> false);
    }

(* ********************
   The universe
 ******************** *)

type (_, _, _) identity += UU : (closed, No.plus_omega, closed) identity

let universe : (closed, No.plus_omega, closed) notation = (UU, Outfix)

let () =
  make universe
    {
      name = "universe";
      tree = Closed_entry (eop (Ident [ "Type" ]) (Done_closed universe));
      processor =
        (fun _ obs loc ->
          match obs with
          | [ Token (Ident [ "Type" ], _) ] -> { value = Synth UU; loc }
          | _ -> invalid "universe");
      (* Universes are never part of case trees. *)
      print_term =
        Some
          (function
          | [ Token (Ident [ "Type" ], wstype) ] -> (string "Type", wstype)
          | _ -> invalid "universe");
      print_case = None;
      is_case = (fun _ -> false);
    }

(* ********************
   Ascription
 ******************** *)

type (_, _, _) identity += Asc : (No.strict opn, No.minus_omega, No.strict opn) identity

let asc : (No.strict opn, No.minus_omega, No.strict opn) notation = (Asc, Infix No.minus_omega)

let () =
  make asc
    {
      name = "ascription";
      tree = Open_entry (eop Colon (done_open asc));
      processor =
        (fun ctx obs loc ->
          match obs with
          | [ Term tm; Token (Colon, _); Term ty ] ->
              let tm = process ctx tm in
              let ty = process ctx ty in
              { value = Synth (Asc (tm, ty)); loc }
          | _ -> invalid "ascription");
      (* Ascriptions are never part of case trees. *)
      print_term =
        Some
          (fun obs ->
            match obs with
            | [ Term tm; Token (Colon, wscolon); Term ty ] ->
                let ptm, wtm = pp_term tm in
                let pty, wty = pp_term ty in
                ( align
                    (group
                       (ptm ^^ pp_ws `Break wtm ^^ Token.pp Colon ^^ pp_ws `Nobreak wscolon ^^ pty)),
                  wty )
            | _ -> invalid "ascription");
      print_case = None;
      is_case = (fun _ -> false);
    }

(* ********************
   Abstraction
 ******************** *)

(* Abstractions (and cube abstractions) are encoded as a right-associative infix operator that inspects its left-hand argument deeply before processing it, expecting it to look like an application spine of variables, and then instead binds those variables in its right-hand argument. *)

type (_, _, _) identity +=
  | Abs : (No.strict opn, No.minus_omega, No.nonstrict opn) identity
  | Cubeabs : (No.strict opn, No.minus_omega, No.nonstrict opn) identity

let abs : (No.strict opn, No.minus_omega, No.nonstrict opn) notation = (Abs, Infixr No.minus_omega)

let cubeabs : (No.strict opn, No.minus_omega, No.nonstrict opn) notation =
  (Cubeabs, Infixr No.minus_omega)

type _ extended_ctx =
  | Extctx :
      ('n, 'm, 'nm) N.plus * (Asai.Range.t option, 'm) Bwv.t * (string option, 'nm) Bwv.t
      -> 'n extended_ctx

let rec get_vars : type n lt1 ls1 rt1 rs1.
    (string option, n) Bwv.t -> (lt1, ls1, rt1, rs1) parse located -> n extended_ctx =
 fun ctx vars ->
  match vars.value with
  | Ident ([ x ], _) -> Extctx (Suc Zero, Snoc (Emp, vars.loc), Bwv.snoc ctx (Some x))
  | Ident (xs, _) -> fatal ?loc:vars.loc (Invalid_variable xs)
  | Placeholder _ -> Extctx (Suc Zero, Snoc (Emp, vars.loc), Bwv.snoc ctx None)
  | App { fn; arg = { value = Ident ([ x ], _); _ }; _ } ->
      let (Extctx (ab, locs, ctx)) = get_vars ctx fn in
      Extctx (Suc ab, Snoc (locs, vars.loc), Bwv.snoc ctx (Some x))
  | App { arg = { value = Ident (xs, _); loc }; _ } -> fatal ?loc (Invalid_variable xs)
  | App { fn; arg = { value = Placeholder _; _ }; _ } ->
      let (Extctx (ab, locs, ctx)) = get_vars ctx fn in
      Extctx (Suc ab, Snoc (locs, vars.loc), Bwv.snoc ctx None)
  | _ -> fatal ?loc:vars.loc Parse_error

let rec raw_lam : type a b ab.
    (string option, ab) Bwv.t ->
    [ `Cube | `Normal ] ->
    (a, b, ab) N.plus ->
    (Asai.Range.t option, b) Bwv.t ->
    ab check located ->
    a check located =
 fun names cube ab locs tm ->
  match (ab, locs) with
  | Zero, Emp -> tm
  | Suc ab, Snoc (locs, loc) ->
      let (Snoc (names, x)) = names in
      raw_lam names cube ab locs
        { value = Lam ({ value = x; loc }, cube, tm); loc = Range.merge_opt loc tm.loc }

let process_abs cube ctx obs _loc =
  (* The loc argument isn't used here since we can deduce the locations of each lambda by merging its variables with its body. *)
  match obs with
  (* Don't bother checking that the mapsto token is valid; it could be different in the two cases. *)
  | [ Term vars; Token _; Term body ] ->
      let (Extctx (ab, locs, ctx)) = get_vars ctx vars in
      raw_lam ctx cube ab locs (process ctx body)
  | _ -> invalid "abstraction"

(* Abstractions are printed bundled with let-bindings. *)

(* ********************
   Let-binding
 ******************** *)

(* Let-in doesn't need to be right-associative in order to chain, because it is left-closed, but we make it right-associative anyway for consistency.  *)

type (_, _, _) identity +=
  | Let : (closed, No.minus_omega, No.nonstrict opn) identity
  | Letrec : (closed, No.minus_omega, No.nonstrict opn) identity

let letin : (closed, No.minus_omega, No.nonstrict opn) notation = (Let, Prefixr No.minus_omega)

let process_let : type n.
    (string option, n) Bwv.t -> observation list -> Asai.Range.t option -> n check located =
 fun ctx obs loc ->
  match obs with
  | [
   Token (Let, _);
   Term x;
   Token (Colon, _);
   Term ty;
   Token (Coloneq, _);
   Term tm;
   Token (In, _);
   Term body;
  ] ->
      let x = get_var x in
      let ty = process ctx ty in
      let tm = process ctx tm in
      let body = process (Bwv.snoc ctx x) body in
      let v : n synth located = { value = Asc (tm, ty); loc = Range.merge_opt ty.loc tm.loc } in
      { value = Synth (Let (x, v, body)); loc }
  | [ Token (Let, _); Term x; Token (Coloneq, _); Term tm; Token (In, _); Term body ] ->
      let x = get_var x in
      let term = process_synth ctx tm "value of let" in
      let body = process (Bwv.snoc ctx x) body in
      { value = Synth (Let (x, term, body)); loc }
  | _ -> invalid "let"

let letin_tree =
  Closed_entry
    (eop Let
       (terms
          [
            (Coloneq, term In (Done_closed letin));
            (Colon, term Coloneq (term In (Done_closed letin)));
          ]))

(* ********************
   Let rec
 ******************** *)

let letrec : (closed, No.minus_omega, No.nonstrict opn) notation = (Letrec, Prefixr No.minus_omega)

type (_, _) letrec_terms =
  | Letrec_terms :
      ('a, 'b, 'ab) tel
      * ('c, 'b, 'cb) Fwn.fplus
      * ('ab check located, 'cb) Vec.t
      * 'ab check located
      -> ('c, 'a) letrec_terms

(* We pre-process the observation list by replacing the initial "let rec" by another "and", so that this recursive function can treat all cases equally. *)
let rec process_letrec_terms : type c a.
    (string option, a) Bwv.t ->
    observation list ->
    (wrapped_parse, c) Bwv.t ->
    c N.t ->
    (c, a) letrec_terms =
 fun ctx obs terms c ->
  match obs with
  | Token (And, _) :: Term x :: Token (Colon, _) :: Term ty :: Token (Coloneq, _) :: Term tm :: rest
    ->
      let x = get_var x in
      let ty = process ctx ty in
      let (Letrec_terms (tel, Suc cb, terms, body)) =
        process_letrec_terms (Snoc (ctx, x)) rest (Snoc (terms, Wrap tm)) (N.suc c) in
      Letrec_terms (Ext (x, ty, tel), cb, terms, body)
  | [ Token (In, _); Term body ] ->
      let (Fplus cb) = Fwn.fplus c in
      let body = process ctx body in
      let terms = Bwv.mmap (fun [ Wrap t ] -> process ctx t) [ terms ] in
      Letrec_terms (Emp, cb, Bwv.prepend cb terms [], body)
  | _ -> invalid "let-rec"

let process_letrec ctx obs loc =
  match obs with
  | Token (Let, _) :: Token (Rec, _) :: obs ->
      let (Letrec_terms (tys, Zero, tms, body)) =
        process_letrec_terms ctx (Token (And, []) :: obs) Emp N.zero in
      locate (Synth (Letrec (tys, tms, body))) loc
  | _ -> invalid "let-rec"

let rec letrec_terms () =
  term Colon
    (term Coloneq (terms [ (And, Lazy (lazy (letrec_terms ()))); (In, Done_closed letrec) ]))

let letrec_tree = Closed_entry (eop Let (op Rec (letrec_terms ())))

(* ****************************************
   Printing abstractions and let-bindings
   **************************************** *)

(* We collate multiple iterated abstractions and lets to treat together.  This function inspects the argument list of a notation, assuming it to be either an abstraction or a let-binding (including letrec), descending into its bodies to find more abstractions and let-bindings.  (It doesn't need to be told what kind of notation it is separately, since that information is contained in the tokens of the argument list.)  It accumulates the notations that it finds (including the implicit outer one, and breaking up letrec-and blocks into one entry per binding) into a heterogeneous bwd, each entry in which contains the necessary information to print that piece.  With exceptions, each such entry will appear on a line by itself in a case tree.  It also returns the innermost body.  *)
let rec get_abslets heads obs =
  match obs with
  (* Abstraction *)
  | [ Term vars; Token (Mapsto, wsmapsto); Term body ] ->
      get_abslets_of_parse (Snoc (heads, `Abs (Wrap vars, Token.Mapsto, wsmapsto))) (Wrap body)
  | [ Term vars; Token (DblMapsto, wsmapsto); Term body ] ->
      get_abslets_of_parse (Snoc (heads, `Abs (Wrap vars, DblMapsto, wsmapsto))) (Wrap body)
  (* Let-binding *)
  | Token _ :: _ -> (
      (* First we pull off the "let", "let rec", or "and" tokens and the variable name. *)
      let toks, x, obs =
        match obs with
        | Token (Let, wslet) :: Token (Rec, wsrec) :: Term x :: rest ->
            ([ (Token.Let, wslet); (Rec, wsrec) ], Wrap x, rest)
        | Token (Let, wslet) :: Term x :: rest -> ([ (Token.Let, wslet) ], Wrap x, rest)
        | Token (And, wsand) :: Term x :: rest -> ([ (Token.And, wsand) ], Wrap x, rest)
        | _ -> invalid "let" in
      (* Then we pull off the ascribed type, if any. *)
      let ty, obs =
        match obs with
        | Token (Colon, wscolon) :: Term ty :: rest -> (Some (wscolon, Wrap ty), rest)
        | _ -> (None, obs) in
      (* Finally we pull the bound value. *)
      match obs with
      (* If we're at an "in", this is the end of this "let". *)
      | [ Token (Coloneq, wscoloneq); Term tm; Token (In, wsin); Term body ] ->
          get_abslets_of_parse
            (Snoc (heads, `Let (toks, x, ty, wscoloneq, Wrap tm, Some wsin)))
            (Wrap body)
      (* Otherwise, we must be at an "and", so we continue inspecting this observation list. *)
      | Token (Coloneq, wscoloneq) :: Term tm :: rest ->
          get_abslets (Snoc (heads, `Let (toks, x, ty, wscoloneq, Wrap tm, None))) rest
      | _ -> invalid "let")
  | _ -> invalid "abstraction"

(* This subroutine takes a given parsed notation and extracts its argument list, if it is either an abstraction or a let-binding, to pass back to the previous function.  *)
and get_abslets_of_parse heads (Wrap body) =
  match body.value with
  | Notn ((Abs, _), d) -> get_abslets heads (args d)
  | Notn ((Cubeabs, _), d) -> get_abslets heads (args d)
  | Notn ((Let, _), d) -> get_abslets heads (args d)
  | Notn ((Letrec, _), d) -> get_abslets heads (args d)
  | _ -> (heads, Wrap body)

(* Given the argument list of an abstraction or let-binding, convert all the prefixes to PPrint documents and arrange them for printing.  Specifically, we convert the heterogeneous list of data returned by get_abslets into a list of PPrint documents.  In addition, we split off the first few abstractions and also the last few, so that the first few can be the intro, and all the trailing abstractions and the body can be flowed together on one line if they fit, and retain the preceding whitespace of each trailing abstraction so we can decide later whether it should be breaking.  We also return the trailing whitespace and the body (as yet unprinted). *)
let pp_abslets obs :
    (Whitespace.t list option * document) list
    * document list
    * (Whitespace.t list option * document) list
    * Whitespace.t list option
    * wrapped_parse =
  let heads, body = get_abslets Emp obs in
  let introabs, abslets, trailabs, ws =
    Bwd.fold_left
      (fun (introabs, heads, trailabs, prews) abslet ->
        match abslet with
        | `Abs (Wrap vars, mapsto, wsmapsto) -> (
            let pvars, wsvars = pp_term vars in
            (* Printing a variable list as an application spine, with its hanging indent if it wraps, is just fine. *)
            let head = pvars ^^ pp_ws `Nobreak wsvars ^^ Token.pp mapsto in
            match heads with
            | Bwd.Emp -> (Snoc (introabs, (prews, head)), heads, trailabs, Some wsmapsto)
            | Snoc _ -> (introabs, heads, Snoc (trailabs, (prews, head)), Some wsmapsto))
        | `Let (toks, Wrap x, ty, wscoloneq, Wrap tm, wsin) ->
            let kws = concat_map (fun (tok, ws) -> Token.pp tok ^^ pp_ws `Nobreak ws) toks in
            let px, wx = pp_term x in
            (* The type of an explicitly typed let-binding is always displayed in term mode, with a wrapping break allowed before the colon. *)
            (* This code should be as parallel as possible with the printing of "def" commands. *)
            let gty, wty =
              match ty with
              | Some (wscolon, Wrap ty) ->
                  let pty, wty = pp_term ty in
                  (group (pp_ws `Break wx ^^ Token.pp Colon ^^ pp_ws `Nobreak wscolon ^^ pty), wty)
              | None -> (empty, wx) in
            let var_and_ty = group (hang 2 (kws ^^ px ^^ gty)) in
            let coloneq = pp_ws `Break wty ^^ Token.pp Coloneq ^^ pp_ws `Nobreak wscoloneq in
            let get_in wtm =
              match wsin with
              | Some wsin -> (group (pp_ws `Break wtm ^^ Token.pp In), wsin)
              | None -> (empty, wtm) in
            let head, wsin =
              if is_case tm then
                (* If the term is a case tree, we display it in case mode.  In this case, the principal breaking points are those in the term's case tree, and we group its "intro" with the let and type. *)
                let itm, ptm, wtm = pp_case `Nontrivial tm in
                let gin, wsin = get_in wtm in
                ( optional (pp_ws `Break) prews
                  ^^ group
                       (var_and_ty ^^ group (nest 2 (coloneq ^^ group (hang 2 itm))) ^^ ptm ^^ gin),
                  wsin )
              else
                (* If the term is not a case tree, then we display it in term mode, and the principal breaking points are before the colon (if any), before the coloneq, and before the "in" (though that will be rare, since "in" is so short). *)
                let ptm, wtm = pp_term tm in
                let gin, wsin = get_in wtm in
                ( optional (pp_ws `Break) prews
                  ^^ group (var_and_ty ^^ nest 2 (coloneq ^^ group (hang 2 ptm) ^^ gin)),
                  wsin ) in
            ( introabs,
              Snoc
                ( Bwd_extra.append heads
                    (Bwd.map (fun (ws, x) -> optional (pp_ws `Break) ws ^^ x) trailabs),
                  head ),
              Emp,
              Some wsin ))
      (Emp, Emp, Emp, None) heads in
  (Bwd.to_list introabs, Bwd.to_list abslets, Bwd.to_list trailabs, ws, body)

(* Print an abstraction or let-binding outside a case tree.  In this case, if it has to be linebroken, we line up all the abstractions and let-bindings, and the body below them. *)
let pp_abslet_term obs =
  let introabs, abslets, trailabs, ws, Wrap body = pp_abslets obs in
  let pbody, wsbody = pp_term body in
  ( align
      (group
         (group
            (match introabs with
            | [] -> empty
            | (absws, abs) :: introabs ->
                optional (pp_ws `Break) absws
                ^^ group (abs ^^ concat_map (fun (w, x) -> optional (pp_ws `Break) w ^^ x) introabs))
         ^^ concat abslets
         ^^
         match trailabs with
         | [] -> optional (pp_ws `Break) ws ^^ pbody
         | (absws, abs) :: trailabs ->
             optional (pp_ws `Break) absws
             (* This "group" allows all the trailing abstractions to go on one line if they fit.  Excluding the preceding whitespace from the "group" ensures that this "one line" is a *new* line relative to any preceding let-bindings.  But if there are no preceding let-bindings, then absws is None and there is no preceding break.  That is, some abstractions alone can appear without a linebreak, but when there are let-bindings too we require a linebreak before they start. *)
             ^^ group
                  (abs
                  ^^ concat_map (fun (w, x) -> optional (pp_ws `Break) w ^^ x) trailabs
                  ^^ optional (pp_ws `Break) ws
                  ^^ pbody))),
    wsbody )

(* Inside a case tree, abstractions and let-bindings go on the starting line if they all fit and then breaks afterwards.  If they don't all fit, they all break immediately to the first line of the subtree, indented as stipulated by the caller.  If there are multiple abstractions, either they all go on the first line or they all go on the first line of the subtree.  Similarly, if a sequence of lets gets linebreaked, we display them one above the other with the body also aligned:
     let x ≔ a in
     let y ≔ b in
     c
   Thus, we concatenate them with breaking whitespaces between.  In each individual let-binding, we allow flow-type breaking at the colon and coloneq and in, which then get an extra indent:
     let x
       : type
       ≔ term in
*)
let pp_abslet_case triv obs =
  let introabs, abslets, trailabs, ws, Wrap body = pp_abslets obs in
  match trailabs with
  | [] -> (
      match abslets with
      | [] ->
          let ibody, pbody, wsbody = pp_case `Nontrivial body in
          ( group
              (concat_map (fun (w, x) -> optional (pp_ws `Break) w ^^ x) introabs
              ^^ optional (pp_ws `Break) ws
              ^^ ibody),
            pbody,
            wsbody )
      | _ :: _ -> (
          let ibody, pbody, wsbody = pp_case `Trivial body in
          let newbody = nest 2 (concat abslets ^^ optional (pp_ws `Break) ws ^^ ibody ^^ pbody) in
          match (introabs, triv) with
          | [], `Trivial -> (empty, newbody, wsbody)
          | [], `Nontrivial ->
              let doc = ifflat empty (hardline ^^ blank 2) ^^ newbody in
              (empty, (if List.is_empty abslets then group doc else doc), wsbody)
          | _ :: _, _ ->
              ( group (concat_map (fun (w, x) -> optional (pp_ws `Break) w ^^ x) introabs),
                newbody,
                wsbody )))
  | (absws, abs) :: trailabs -> (
      let ibody, pbody, wsbody = pp_case `Nontrivial body in
      let newbody =
        nest 2
          (concat abslets
          ^^ optional (pp_ws `Break) absws
          ^^ group
               (abs
               ^^ concat_map (fun (w, x) -> optional (pp_ws `Break) w ^^ x) trailabs
               ^^ optional (pp_ws `Break) ws
               ^^ ibody)
          ^^ pbody) in
      match (introabs, triv) with
      | [], `Trivial -> (empty, newbody, wsbody)
      | [], `Nontrivial ->
          let doc = ifflat empty (hardline ^^ blank 2) ^^ newbody in
          (empty, (if List.is_empty abslets then group doc else doc), wsbody)
      | (absws, abs) :: introabs, _ -> (
          match abslets with
          | [] ->
              ( group
                  (abs
                  ^^ concat_map (fun (w, x) -> optional (pp_ws `Break) w ^^ x) introabs
                  ^^ optional (pp_ws `Break) ws
                  ^^ ibody),
                optional (pp_ws `Break) absws ^^ pbody,
                wsbody )
          | _ :: _ ->
              ( group (abs ^^ concat_map (fun (w, x) -> optional (pp_ws `Break) w ^^ x) introabs),
                optional (pp_ws `Break) absws ^^ newbody,
                wsbody )))

(* An abstraction should be printed as a case tree if its body is. *)
let abs_is_case = function
  | [ _; _; Term body ] -> is_case body
  | _ -> invalid "abstraction"

let () =
  make abs
    {
      name = "abstraction";
      tree = Open_entry (eop Mapsto (done_open abs));
      processor = (fun ctx obs loc -> process_abs `Normal ctx obs loc);
      print_term = Some pp_abslet_term;
      print_case = Some pp_abslet_case;
      is_case = abs_is_case;
    };
  make cubeabs
    {
      name = "cube_abstraction";
      tree = Open_entry (eop DblMapsto (done_open cubeabs));
      processor = (fun ctx obs loc -> process_abs `Cube ctx obs loc);
      print_term = Some pp_abslet_term;
      print_case = Some pp_abslet_case;
      is_case = abs_is_case;
    };
  make letin
    {
      name = "let";
      tree = letin_tree;
      processor = (fun ctx obs loc -> process_let ctx obs loc);
      print_term = Some pp_abslet_term;
      print_case = Some pp_abslet_case;
      (* However, a let-binding is always printed as a case tree. *)
      is_case = (fun _ -> true);
    };
  make letrec
    {
      name = "letrec";
      tree = letrec_tree;
      processor = process_letrec;
      print_term = Some pp_abslet_term;
      print_case = Some pp_abslet_case;
      is_case = (fun _ -> true);
    }

(* ********************
   Telescopes
   ******************** *)

(* These functions inspect and process multiple-variable type declarations like "x y z : A", such as appear (in paretheses) in the domain of a Π-type. *)

(* Inspect 'xs', expecting it to be a spine of valid bindable local variables or underscores, and produce a list of those variables, consing it onto the accumulator argument 'vars'. *)
let rec process_var_list : type lt ls rt rs.
    (lt, ls, rt, rs) parse located ->
    (string option * Whitespace.t list) list ->
    (string option * Whitespace.t list) list option =
 fun { value; loc } vars ->
  match value with
  | Ident ([ x ], w) -> Some ((Some x, w) :: vars)
  | Placeholder w -> Some ((None, w) :: vars)
  | App { fn; arg = { value = Ident ([ x ], w); _ }; _ } -> process_var_list fn ((Some x, w) :: vars)
  | App { fn; arg = { value = Placeholder w; _ }; _ } -> process_var_list fn ((None, w) :: vars)
  (* There's a choice here: an invalid variable name could still be a valid term, so we could allow for instance (x.y : A) → B to be parsed as a non-dependent function type.  But that seems a recipe for confusion. *)
  | Ident (name, _) -> fatal ?loc (Invalid_variable name)
  | App { arg = { value = Ident (xs, _); loc }; _ } -> fatal ?loc (Invalid_variable xs)
  | _ -> None

(* Inspect 'arg', expecting it to be of the form 'x y z : A', and return the list of variables, the type, and the whitespace of the colon.  Return None if it is not of that form, causing callers to fall back to alternative interpretations.*)
let process_typed_vars : type lt ls rt rs.
    (lt, ls, rt, rs) parse ->
    ((string option * Whitespace.t list) list * Whitespace.t list * wrapped_parse) option =
 fun arg ->
  let open Monad.Ops (Monad.Maybe) in
  match arg with
  | Notn ((Asc, _), n) -> (
      match args n with
      | [ Term xs; Token (Colon, wscolon); Term ty ] ->
          let* vars = process_var_list xs [] in
          return (vars, wscolon, Wrap ty)
      | _ -> None)
  | _ -> None

(* ****************************************
   Function types (dependent and non)
 **************************************** *)

type (_, _, _) identity += Arrow : (No.strict opn, No.zero, No.nonstrict opn) identity

let arrow : (No.strict opn, No.zero, No.nonstrict opn) notation = (Arrow, Infixr No.zero)

type arrow_opt = [ `Arrow of Whitespace.t list | `Noarrow | `First ]

type pi_dom =
  | Dep of {
      wsarrow : arrow_opt;
      vars : (string option * Whitespace.t list) list;
      ty : wrapped_parse;
      wslparen : Whitespace.t list;
      wscolon : Whitespace.t list;
      wsrparen : Whitespace.t list;
    }
  | Nondep of { wsarrow : arrow_opt; ty : wrapped_parse }

(* Inspect 'doms', expecting it to be of the form (x:A)(y:B) etc, and produce a list of variables with types, prepending that list onto the front of the given accumulation list, with the first one having an arrow attached (before it front) if 'wsarrow' is given.  If it isn't of that form, interpret it as the single domain type of a non-dependent function-type and cons it onto the list. *)
let get_pi_args : type lt ls rt rs.
    arrow_opt -> (lt, ls, rt, rs) parse located -> pi_dom list -> pi_dom list =
 fun wsarrow doms accum ->
  let open Monad.Ops (Monad.Maybe) in
  let rec go : type lt ls rt rs. (lt, ls, rt, rs) parse located -> pi_dom list -> pi_dom list option
      =
   fun doms accum ->
    match doms.value with
    | Notn ((Parens, _), n) -> (
        match args n with
        | [ Token (LParen, wslparen); Term body; Token (RParen, wsrparen) ] ->
            let* vars, wscolon, ty = process_typed_vars body.value in
            return (Dep { wsarrow; vars; ty; wslparen; wscolon; wsrparen } :: accum)
        | _ -> None)
    | App { fn; arg = { value = Notn ((Parens, _), n); _ }; _ } -> (
        match args n with
        | [ Token (LParen, wslparen); Term body; Token (RParen, wsrparen) ] ->
            let* vars, wscolon, ty = process_typed_vars body.value in
            go fn (Dep { wsarrow = `Noarrow; vars; ty; wslparen; wscolon; wsrparen } :: accum)
        | _ -> None)
    | _ -> None in
  match go doms accum with
  | Some result -> result
  | None -> Nondep { wsarrow; ty = Wrap doms } :: accum

(* Get all the domains and eventual codomain from a right-associated iterated function-type. *)
let rec get_pi : arrow_opt -> observation list -> pi_dom list * Whitespace.t list * wrapped_parse =
 fun prev_arr obs ->
  match obs with
  | [ Term doms; Token (Arrow, wsarrow); Term cod ] ->
      let vars, ws, cod =
        match cod.value with
        | Notn ((Arrow, _), n) -> get_pi (`Arrow wsarrow) (args n)
        | _ -> ([], wsarrow, Wrap cod) in
      (get_pi_args prev_arr doms vars, ws, cod)
  | _ -> invalid "arrow"

(* Given the variables with domains and the codomain of a pi-type, process it into a raw term. *)
let rec process_pi : type n lt ls rt rs.
    (string option, n) Bwv.t -> pi_dom list -> (lt, ls, rt, rs) parse located -> n check located =
 fun ctx doms cod ->
  match doms with
  | [] -> process ctx cod
  | Nondep { ty = Wrap dom; _ } :: doms ->
      let cdom = process ctx dom in
      let ctx = Bwv.snoc ctx None in
      let cod = process_pi ctx doms cod in
      let loc = Range.merge_opt cdom.loc cod.loc in
      { value = Synth (Pi (None, cdom, cod)); loc }
  | Dep ({ vars = (x, _) :: xs; ty = Wrap dom; _ } as data) :: doms ->
      let cdom = process ctx dom in
      let ctx = Bwv.snoc ctx x in
      let cod = process_pi ctx (Dep { data with vars = xs } :: doms) cod in
      let loc = Range.merge_opt cdom.loc cod.loc in
      { value = Synth (Pi (x, cdom, cod)); loc }
  | Dep { vars = []; _ } :: doms -> process_pi ctx doms cod

(* Pretty-print the domains of a right-associated iterated function-type that may mix dependent and non-dependent arguments.  Each argument is preceded by an arrow if its wsarrow is given; pi_doms ensures these go in the right place.  If linebreaked, the eventual codomain with its arrow goes on a line by itself with hanging indent, and then the domains are flowed with their own hanging indent.  Arrows never come at the beginnings of lines.  *)

(* This function prints only the domains. *)
let pp_doms : pi_dom list -> document * Whitespace.t list =
 fun doms ->
  let doc, ws =
    List.fold_left
      (fun (acc, prews) dom ->
        let wsarrow, (pty, wty) =
          match dom with
          | Dep { wsarrow; vars; ty = Wrap ty; wslparen; wscolon; wsrparen } ->
              let pvars, wvars =
                List.fold_left
                  (fun (acc, prews) (x, wx) ->
                    ( acc
                      ^^ group
                           (optional (pp_ws `Break) prews
                           ^^ Option.fold ~some:utf8string ~none:(Token.pp Underscore) x),
                      Some wx ))
                  (empty, None) vars in
              let pty, wty = pp_term ty in
              ( wsarrow,
                ( group
                    (Token.pp LParen
                    ^^ pp_ws `None wslparen
                    ^^ hang 2 pvars
                    ^^ optional (pp_ws `Break) wvars
                    ^^ Token.pp Colon
                    ^^ pp_ws `Nobreak wscolon
                    ^^ pty
                    ^^ pp_ws `None wty
                    ^^ Token.pp RParen),
                  wsrparen ) )
          | Nondep { wsarrow; ty = Wrap ty } -> (wsarrow, pp_term ty) in
        let doc, ws =
          match wsarrow with
          | `Arrow wsarrow ->
              ( optional (pp_ws `Nobreak) prews ^^ Token.pp Arrow ^^ pp_ws `Break wsarrow ^^ pty,
                Some wty )
          | `Noarrow | `First -> (optional (pp_ws `Break) prews ^^ pty, Some wty) in
        (acc ^^ group doc, ws))
      (empty, None) doms in
  (doc, ws <|> Anomaly "missing ws in pp_doms")

let () =
  make arrow
    {
      name = "arrow";
      tree = Open_entry (eop Arrow (done_open arrow));
      processor =
        (fun ctx obs _loc ->
          (* We don't need the loc parameter here, since we can reconstruct the location of each pi-type from its arguments. *)
          let doms, _, Wrap cod = get_pi `First obs in
          process_pi ctx doms cod);
      print_term =
        Some
          (fun obs ->
            let doms, wsarrow, Wrap cod = get_pi `First obs in
            let pdom, wdom = pp_doms doms in
            let pcod, wcod = pp_term cod in
            ( group
                (align
                   (pdom
                   ^^ pp_ws `Break wdom
                   ^^ Token.pp Arrow
                   ^^ hang 2 (pp_ws `Nobreak wsarrow ^^ pcod))),
              wcod ));
      (* Function-types are never part of case trees. *)
      print_case = None;
      is_case = (fun _ -> false);
    }

(* ********************
   Coloneq
 ******************** *)

(* Coloneq is an auxiliary notation only used as a sub-notation of others. *)

type (_, _, _) identity += Coloneq : (No.strict opn, No.minus_omega, No.nonstrict opn) identity

let coloneq : (No.strict opn, No.minus_omega, No.nonstrict opn) notation =
  (Coloneq, Infixr No.minus_omega)

let () =
  make coloneq
    {
      name = "coloneq";
      tree = Open_entry (eop Coloneq (done_open coloneq));
      processor = (fun _ _ -> fatal Parse_error);
      print_term =
        Some
          (fun obs ->
            match obs with
            | [ Term x; Token (Coloneq, wscoloneq); Term body ] ->
                let px, wx = pp_term x in
                let pbody, wbody = pp_term body in
                ( group
                    (px ^^ pp_ws `Break wx ^^ Token.pp Coloneq ^^ pp_ws `Nobreak wscoloneq ^^ pbody),
                  wbody )
            | _ -> invalid "tuple");
      (* This is used when printing labeled fields of a tuple in case mode. *)
      print_case =
        Some
          (* Always nontrivial *)
          (fun _triv obs ->
            match obs with
            | [ Term x; Token (Coloneq, wscoloneq); Term body ] ->
                let px, wx = pp_term x in
                let ibody, pbody, wbody = pp_case `Nontrivial body in
                ( group
                    (px ^^ pp_ws `Break wx ^^ Token.pp Coloneq ^^ pp_ws `Nobreak wscoloneq ^^ ibody),
                  pbody,
                  wbody )
            | _ -> invalid "tuple");
      is_case = (fun _ -> false);
    }

(* ********************
   Tuples
 ******************** *)

(* The notation for tuples is "( x ≔ M, y ≔ N, z ≔ P )".  The parentheses don't conflict with ordinary parentheses, since ≔ and , are not term-forming operators all by themselves.  The 0-ary tuple "()" is included, and also doesn't conflict since ordinary parentheses must contain a term.  We also allow some of the components of the tuple to be unlabeled, as in "(M, N, P)"; these are assigned to the fields that don't have a corresponding labeled component in the order they appear in the record type.  The only thing that's not allowed is an unlabeled 1-tuple "(M)" without trailing comma, since that would conflict with ordinary parentheses, but "(M,)" works, as does "(_ ≔ M)". *)

let rec tuple_fields () =
  Inner
    {
      empty_branch with
      ops = TokMap.singleton RParen (Done_closed parens);
      term =
        Some
          (TokMap.of_list [ (Op ",", Lazy (lazy (tuple_fields ()))); (RParen, Done_closed parens) ]);
    }

(* Split in cases based on whether an instance of 'parens' is a tuple or just parentheses.  In the former case, we return the interior term; in the latter we strip off the starting parentheses. *)
let parens_case :
    observation list ->
    [ `Parens of Whitespace.t list * wrapped_parse * Whitespace.t list
    | `Tuple of Whitespace.t list * observation list ] = function
  (* Tuple starting with a labeled term *)
  | Token (LParen, wslparen) :: (Term { value = Notn ((Coloneq, _), _); _ } :: _ as obs) ->
      `Tuple (wslparen, obs)
  (* Ordinary parentheses (around an unlabeled term!) *)
  | [ Token (LParen, wslparen); Term body; Token (RParen, wsrparen) ] ->
      `Parens (wslparen, Wrap body, wsrparen)
  (* Other tuple *)
  | Token (LParen, wslparen) :: obs -> `Tuple (wslparen, obs)
  | _ -> invalid "tuple"

let rec process_tuple : type n.
    ((string * string list) option, n check located) Abwd.t ->
    StringSet.t ->
    (string option, n) Bwv.t ->
    observation list ->
    Asai.Range.t option ->
    n check located =
 fun flds found ctx obs loc ->
  match obs with
  (* Got all the fields *)
  | [ Token (RParen, _) ] -> { value = Raw.Struct (Eta, flds); loc }
  (* Comma ending the previous field *)
  | Token (Op ",", _) :: obs -> process_tuple flds found ctx obs loc
  (* Labeled field *)
  | Term { value = Notn ((Coloneq, _), n); loc } :: obs -> (
      match args n with
      | [ Term { value = Ident ([ fld ], _); loc = xloc }; Token (Coloneq, _); Term tm ] ->
          let tm = process ctx tm in
          if StringSet.mem fld found then fatal ?loc:xloc (Duplicate_field_in_tuple fld)
          else
            process_tuple
              (* Tuples have no higher fields, so the bwd of strings labeling a dimension is always empty. *)
              (Abwd.add (Some (fld, [])) tm flds)
              (StringSet.add fld found) ctx obs loc
      | [ Term { value = Placeholder _; _ }; Token (Coloneq, _); Term tm ] ->
          let tm = process ctx tm in
          process_tuple (Abwd.add None tm flds) found ctx obs loc
      | [ Term x; Token (Coloneq, _); _ ] -> fatal ?loc:x.loc Invalid_field_in_tuple
      | _ -> invalid "tuple")
  (* Unlabeled field *)
  | Term tm :: obs ->
      let tm = process ctx tm in
      process_tuple (Abwd.add None tm flds) found ctx obs loc
  | _ -> invalid "tuple"

let rec pp_tuple_fields first prews accum obs : document * Whitespace.t list =
  let prews =
    match Display.spacing () with
    | `Wide -> optional (pp_ws `Break) prews
    | `Narrow -> optional (pp_ws `Cut) prews in
  match obs with
  (* No more terms.  This includes empty tuples.  (Empty tuples can't contain a comma.) *)
  | [ Token (RParen, wsrparen) ] -> (accum ^^ prews ^^ Token.pp RParen, wsrparen)
  (* Last term, without a trailing comma.  Don't add one. *)
  | [ Term tm; Token (RParen, wsrparen) ] ->
      let itm, ptm, wtm = pp_case `Trivial tm in
      let doc = itm ^^ ptm ^^ pp_ws `None wtm ^^ Token.pp RParen in
      (accum ^^ prews ^^ doc, wsrparen)
  (* Last term, with an unnecessary trailing comma (that is, not a 1-tuple or the entry is labeled).  Remove it, but keep its whitespace. *)
  | [ Term tm; Token (Op ",", wscomma); Token (RParen, wsrparen) ] when not first ->
      let itm, ptm, wtm = pp_case `Trivial tm in
      let doc = itm ^^ ptm ^^ pp_ws `None wtm ^^ pp_ws `None wscomma ^^ Token.pp RParen in
      (accum ^^ prews ^^ doc, wsrparen)
  | [
   Term ({ value = Notn ((Coloneq, _), _); _ } as tm);
   Token (Op ",", wscomma);
   Token (RParen, wsrparen);
  ] ->
      let itm, ptm, wtm = pp_case `Trivial tm in
      let doc = itm ^^ ptm ^^ pp_ws `None wtm ^^ pp_ws `None wscomma ^^ Token.pp RParen in
      (accum ^^ prews ^^ doc, wsrparen)
  (* Last term, with a necessary trailing comma.  Keep it. *)
  | [ Term tm; Token (Op ",", wscomma); Token (RParen, wsrparen) ] ->
      let itm, ptm, wtm = pp_case `Trivial tm in
      let doc =
        itm ^^ ptm ^^ pp_ws `None wtm ^^ Token.pp (Op ",") ^^ pp_ws `None wscomma ^^ Token.pp RParen
      in
      (accum ^^ prews ^^ doc, wsrparen)
  (* Non-last term, with a comma after it.  Keep the comma, of course. *)
  | Term tm :: Token (Op ",", wscomma) :: obs ->
      let itm, ptm, wtm = pp_case `Trivial tm in
      let doc = itm ^^ ptm ^^ pp_ws `None wtm ^^ Token.pp (Op ",") in
      pp_tuple_fields false (Some wscomma) (accum ^^ prews ^^ doc) obs
  | _ -> invalid "tuple"

let pp_tuple_term obs =
  match parens_case obs with
  | `Tuple (wslparen, obs) ->
      let doc, ws = pp_tuple_fields true None (pp_ws `None wslparen) obs in
      (Token.pp LParen ^^ group (align doc), ws)
  | `Parens (wslparen, Wrap body, wsrparen) ->
      let pbody, wbody = pp_term body in
      ( group
          (Token.pp LParen
          ^^ align (pp_ws `None wslparen ^^ pbody ^^ pp_ws `None wbody ^^ Token.pp RParen)),
        wsrparen )

let pp_tuple_case triv obs =
  match parens_case obs with
  | `Tuple (wslparen, obs) -> (
      match obs with
      (* For an empty tuple, we put everything in the intro. *)
      | [ Token (RParen, wsrparen) ] ->
          (Token.pp LParen ^^ pp_ws `None wslparen ^^ Token.pp RParen, empty, wsrparen)
      | _ -> (
          let doc, ws = pp_tuple_fields true None empty obs in
          match triv with
          | `Trivial -> (Token.pp LParen, group (align (pp_ws `None wslparen ^^ doc)), ws)
          | `Nontrivial -> (Token.pp LParen, group (nest 2 (pp_ws `Cut wslparen ^^ doc)), ws)))
  | `Parens (wslparen, Wrap body, wsrparen) ->
      let ibody, pbody, wbody = pp_case `Nontrivial body in
      ( Token.pp LParen ^^ pp_ws `None wslparen ^^ ibody,
        pbody ^^ pp_ws `None wbody ^^ Token.pp RParen,
        wsrparen )

let () =
  make parens
    {
      name = "parens/tuple";
      tree = Closed_entry (eop LParen (tuple_fields ()));
      processor =
        (fun ctx obs loc ->
          match parens_case obs with
          | `Tuple (_, obs) -> process_tuple Abwd.empty StringSet.empty ctx obs loc
          | `Parens (_, Wrap body, _) -> process ctx body);
      print_term = Some pp_tuple_term;
      print_case = Some pp_tuple_case;
      (* A tuple is always printed like a case tree, even if it isn't one, because that looks best when it goes over multiple lines.  But parentheses are only printed as a case tree if the term inside is a case tree. *)
      is_case =
        (fun obs ->
          match parens_case obs with
          | `Tuple _ -> true
          | `Parens (_, Wrap body, _) -> is_case body);
    }

(* ********************
   Dot
 ******************** *)

(* A dot is an auxiliary notation used for refutation branches. *)

type (_, _, _) identity += Dot : (closed, No.plus_omega, closed) identity

let dot : (closed, No.plus_omega, closed) notation = (Dot, Outfix)

let () =
  make dot
    {
      name = "dot";
      tree = Closed_entry (eop Dot (Done_closed dot));
      processor = (fun _ _ _ -> fatal Parse_error);
      print_term =
        Some
          (function
          | [ Token (Dot, wsdot) ] -> (Token.pp Dot, wsdot)
          | _ -> invalid "dot");
      print_case = None;
      is_case = (fun _ -> false);
    }

(* ********************
   Matches
 ******************** *)

(* Parsing for implicit matches, explicit (including nondependent) matches, and pattern-matching lambdas shares some code. *)

type (_, _, _) identity +=
  | Implicit_match : (closed, No.plus_omega, closed) identity
  | Explicit_match : (closed, No.plus_omega, closed) identity
  | Matchlam : (closed, No.plus_omega, closed) identity

let implicit_mtch : (closed, No.plus_omega, closed) notation = (Implicit_match, Outfix)
let explicit_mtch : (closed, No.plus_omega, closed) notation = (Explicit_match, Outfix)
let mtchlam : (closed, No.plus_omega, closed) notation = (Matchlam, Outfix)

(* Here are the basic match notation trees. *)

let rec mtch_branches notn bar_ok end_ok comma_ok =
  Inner
    {
      empty_branch with
      ops =
        TokMap.of_list
          ((if end_ok then [ (Token.RBracket, Done_closed notn) ] else [])
          @ if bar_ok then [ (Op "|", mtch_branches notn false false comma_ok) ] else []);
      term =
        Some
          (TokMap.of_list
             ((if comma_ok then [ (Token.Op ",", patterns notn) ] else [])
             @ [ (Mapsto, body notn comma_ok) ]));
    }

and body notn comma_ok =
  terms
    [
      (Op "|", Lazy (lazy (mtch_branches notn false false comma_ok))); (RBracket, Done_closed notn);
    ]

and patterns notn = terms [ (Token.Op ",", Lazy (lazy (patterns notn))); (Mapsto, body notn true) ]

let rec discriminees () =
  terms
    [
      (LBracket, mtch_branches implicit_mtch true true true); (Op ",", Lazy (lazy (discriminees ())));
    ]

(* A pattern is either a variable name or a constructor with some number of pattern arguments. *)
module Pattern = struct
  type t =
    | Var : string option located -> t
    | Constr : Constr.t located * (t, 'n) Vec.t located -> t
end

type pattern = Pattern.t

let get_pattern : type lt1 ls1 rt1 rs1. (lt1, ls1, rt1, rs1) parse located -> pattern =
 fun pat ->
  let rec go : type n lt1 ls1 rt1 rs1.
      (lt1, ls1, rt1, rs1) parse located -> (pattern, n) Vec.t located -> pattern =
   fun pat pats ->
    match pat.value with
    | Ident ([ x ], _) -> (
        match pats.value with
        | [] -> Var (locate (Some x) pat.loc)
        | _ -> fatal ?loc:pat.loc Parse_error)
    | Ident (xs, _) -> fatal ?loc:pat.loc (Invalid_variable xs)
    | Placeholder _ -> (
        match pats.value with
        | [] -> Var (locate None pat.loc)
        | _ -> fatal ?loc:pat.loc Parse_error)
    | Constr (c, _) -> Constr (locate (Constr.intern c) pat.loc, pats)
    | App { fn; arg; _ } ->
        go fn
          (locate
             (go arg (locate Vec.[] arg.loc) :: pats.value : (pattern, n Fwn.suc) Vec.t)
             pats.loc)
    | Notn ((Parens, _), n) -> (
        match args n with
        | [ Token (LParen, _); Term arg; Token (RParen, _) ] -> go arg pats
        | _ -> fatal ?loc:pat.loc Parse_error)
    | _ -> fatal ?loc:pat.loc Parse_error in
  go pat (locate Vec.[] pat.loc)

(* For parsing matches, we use a special kind of scope that labels all the variables with integers (De Bruijn levels) in addition to possible strings. *)
module Matchscope : sig
  type 'a t

  val lookup_num : int -> 'a t -> 'a N.index option
  val ext : 'a t -> string option -> 'a N.suc t
  val last_num : 'a t -> int
  val exts : ('a, 'm, 'am) Raw.Indexed.bplus -> 'a t -> 'am t * (int, 'm) Vec.t
  val make : (string option, 'a) Bwv.t -> 'a t
  val names : 'a t -> (string option, 'a) Bwv.t
  val give_name : int -> string option -> 'a t -> 'a t
end = struct
  type _ t =
    | Matchscope :
        (string option, 'a) Bwv.t * ('a, 'b, 'ab) N.plus * (string option * int, 'b) Bwv.t * int
        -> 'ab t

  let rec lookup_num : type a. int -> a t -> a N.index option =
   fun i -> function
    | Matchscope (_, Zero, Emp, _) -> None
    | Matchscope (base, Suc ab, Snoc (scope, (_, j)), n) -> (
        if i = j then Some Top
        else
          match lookup_num i (Matchscope (base, ab, scope, n - 1)) with
          | Some k -> Some (Pop k)
          | None -> None)

  let check_duplicates : type b. (string option * int, b) Bwv.t -> string option -> unit =
   fun scope name ->
    match name with
    | Some name -> (
        match Bwv.find_opt (fun (y, _) -> y = Some name) scope with
        | Some _ -> fatal (Duplicate_pattern_variable name)
        | None -> ())
    | None -> ()

  let ext : type a. a t -> string option -> a N.suc t =
   fun (Matchscope (base, ab, scope, i)) name ->
    check_duplicates scope name;
    Matchscope (base, Suc ab, Snoc (scope, (name, i)), i + 1)

  let last_num : type a. a t -> int = fun (Matchscope (_, _, _, i)) -> i - 1

  let rec exts : type a m am. (a, m, am) Raw.Indexed.bplus -> a t -> am t * (int, m) Vec.t =
   fun am scope ->
    match (am, scope) with
    | Zero, _ -> (scope, [])
    | Suc am, Matchscope (base, ab, scope, i) ->
        let newscope, levels = exts am (Matchscope (base, Suc ab, Snoc (scope, (None, i)), i + 1)) in
        (newscope, i :: levels)

  let make : type a. (string option, a) Bwv.t -> a t = fun base -> Matchscope (base, Zero, Emp, 0)

  let names : type a. a t -> (string option, a) Bwv.t =
   fun (Matchscope (base, ab, scope, _)) -> Bwv.bappend ab base (Bwv.map fst scope)

  let give_name : type a. int -> string option -> a t -> a t =
   fun i x (Matchscope (base, ab, scope, n)) ->
    check_duplicates scope x;
    Matchscope
      ( base,
        ab,
        Bwv.map
          (fun (y, j) ->
            if i = j then
              match y with
              | None -> (x, j)
              | Some _ -> fatal (Anomaly "renaming already-named pattern variable")
            else (y, j))
          scope,
        n )
end

(* An ('a, 'n) branch is a scope of 'a variables, a vector of 'n patterns, and a body to be parsed in the scope extended by the variables in those patterns.  At the beginning, all the branches start out with the same scope of variables, but as we proceed they can get different ones.  All the branches in a single invocation of process_match have the same *number* of variables in scope, but different branches could have different *names* for those variables. *)
type ('a, 'n) branch = 'a Matchscope.t * (pattern, 'n) Vec.t * wrapped_parse

(* An ('a, 'm, 'n) cbranch is a branch, with scope of 'a variables, that starts with a constructor (unspecified) having 'm arguments and proceeds with 'n other patterns.  *)
type ('a, 'm, 'n) cbranch =
  'a Matchscope.t * (pattern, 'm) Vec.t located * (pattern, 'n) Vec.t * wrapped_parse

(* An ('a, 'n) cbranches is a Bwd of branches that start with the same constructor, which always has the same number of arguments, along with a scope of 'a variables common to those branches. *)
type (_, _) cbranches =
  | CBranches : Constr.t located * ('a, 'm, 'n) cbranch Bwd.t -> ('a, 'n) cbranches

let process_ix : type a. a Matchscope.t -> int -> a synth located =
 fun ctx i ->
  match Matchscope.lookup_num i ctx with
  | Some k -> unlocated (Raw.Var (k, None))
  | None -> fatal (Anomaly "invalid parse-level in processing match")

let process_obs_or_ix : type a. a Matchscope.t -> (wrapped_parse, int) Either.t -> a synth located =
 fun ctx -> function
  | Left (Wrap x) -> process_synth (Matchscope.names ctx) x "discriminee of match"
  | Right i -> (
      match Matchscope.lookup_num i ctx with
      | Some k -> unlocated (Raw.Var (k, None))
      | None -> fatal (Anomaly "invalid parse-level in processing match"))

(* Given a scope of 'a variables, a vector of 'n not-yet-processed discriminees or previous match variables, and a list of branches with 'n patterns each, compile them into a nested match.  The scope given as an argument to this function is used only for the discriminees; it is the original scope extended by unnamed variables (since the discriminees can't actually depend on the pattern variables).  The scopes used for the branches, which also include pattern variables, are stored in the branch data structures. *)
let rec process_branches : type a n.
    a Matchscope.t ->
    ((wrapped_parse, int) Either.t, n) Vec.t ->
    int Bwd.t ->
    (a, n) branch list ->
    Asai.Range.t option ->
    [ `Implicit | `Explicit of wrapped_parse | `Nondep of int located ] ->
    a check located =
 fun xctx xs seen branches loc sort ->
  match branches with
  (* An empty match, having no branches, compiles to a refutation that will check by looking for any discriminee with an empty type.  This can only happen as the top-level call, so 'seen' should be empty and we really can just take all the discriminees. *)
  | [] -> (
      let tms = Vec.to_list_map (process_obs_or_ix xctx) xs in
      match (sort, xs) with
      | `Implicit, _ -> locate (Refute (tms, `Implicit)) loc
      | `Explicit (Wrap motive), [ Left (Wrap tm) ] -> (
          let ctx = Matchscope.names xctx in
          let sort = `Explicit (process ctx motive) in
          match process ctx tm with
          | { value = Synth tm; loc } ->
              locate
                (Synth (Match { tm = locate tm loc; sort; branches = Emp; refutables = None }))
                loc
          | _ -> fatal (Nonsynthesizing "motive of explicit match"))
      | `Nondep i, [ Left (Wrap tm) ] -> (
          let ctx = Matchscope.names xctx in
          let sort = `Nondep i in
          match process ctx tm with
          | { value = Synth tm; loc } ->
              locate
                (Synth (Match { tm = locate tm loc; sort; branches = Emp; refutables = None }))
                loc
          | _ -> fatal (Nonsynthesizing "motive of explicit match"))
      | _ -> fatal (Anomaly "multiple match with return-type"))
  (* If there are no patterns left, and hence no discriminees either, we require that there must be exactly one branch. *)
  | (_, [], _) :: _ :: _ -> fatal No_remaining_patterns
  (* If that one remaining branch is a refutation, we refute all the "seen" terms or variables. *)
  | [ (_, [], Wrap { value = Notn ((Dot, _), _); loc }) ] ->
      let [] = xs in
      let tms = Bwd_extra.to_list_map (process_ix xctx) seen in
      locate (Refute (tms, `Explicit)) loc
  (* Otherwise, the result is just the body of that branch. *)
  | [ (bodyctx, [], Wrap body) ] ->
      let [] = xs in
      process (Matchscope.names bodyctx) body
  (* If the first pattern of the first branch is a variable, then the same must be true of all the other branches, but they could all have different variable names. *)
  | (xctx, Var name :: _, _) :: _ as branches -> (
      (* The variable is assigned to the value of the first discriminee. *)
      let (x :: xs) = xs in
      match x with
      | Right i ->
          (* If that discriminee is a pattern variable that was introduced earlier, then we just alias the current variable name to it. *)
          let branches =
            List.map
              (function
                | bodyctx, (Var y :: patterns : (pattern, n) Vec.t), body ->
                    (Matchscope.give_name i y.value bodyctx, patterns, body)
                | _, Constr (_, { loc = cloc; _ }) :: _, _ -> fatal ?loc:cloc Overlapping_patterns)
              branches in
          let seen = Snoc (seen, i) in
          process_branches xctx xs seen branches loc sort
      | Left (Wrap tm) ->
          (* Otherwise, we have to let-bind it to the discriminee term, adding it as a new variable to the scope. *)
          let branches =
            List.map
              (function
                | bodyctx, (Var y :: patterns : (pattern, n) Vec.t), body ->
                    (Matchscope.ext bodyctx y.value, patterns, body)
                | _, Constr (_, { loc = cloc; _ }) :: _, _ -> fatal ?loc:cloc Overlapping_patterns)
              branches in
          let stm = process_synth (Matchscope.names xctx) tm "discriminee of match" in
          Reporter.try_with
            (fun () ->
              let xctx = Matchscope.ext xctx None in
              let seen = Snoc (seen, Matchscope.last_num xctx) in
              let mtch = process_branches xctx xs seen branches loc sort in
              locate (Synth (Let (name.value, stm, mtch))) loc)
            ~fatal:(fun d ->
              match d.message with
              | No_remaining_patterns -> fatal ?loc:name.loc Overlapping_patterns
              | _ -> fatal_diagnostic d))
  (* If the first pattern of the first branch is a constructor, the same must be true of all the other branches, and we can sort them by constructor.  We require that each constructor always appear with the same number of arguments. *)
  | (xctx, Constr _ :: _, _) :: _ as branches ->
      let cbranches =
        List.fold_left
          (fun acc branch ->
            match branch with
            | bodyctx, (Constr (c, pats) :: patterns : (pattern, n) Vec.t), body ->
                acc
                |> Abwd.update c.value (function
                     | None | Some (CBranches (_, Emp)) ->
                         Some (CBranches (c, Snoc (Emp, (bodyctx, pats, patterns, body))))
                     | Some (CBranches (c', (Snoc (_, (_, pats', _, _)) as cbrs))) -> (
                         match Fwn.compare (Vec.length pats.value) (Vec.length pats'.value) with
                         | Neq -> fatal ?loc:pats.loc Inconsistent_patterns
                         | Eq -> Some (CBranches (c', Snoc (cbrs, (bodyctx, pats, patterns, body))))
                         ))
            | _, Var x :: _, _ -> fatal ?loc:x.loc Overlapping_patterns)
          Abwd.empty branches in
      let (x :: xs) = xs in
      let branches =
        (* Now we recursively process each of those families of branches. *)
        Abwd.map
          (fun (CBranches (type m) ((c, brs) : _ * (_, m, _) cbranch Bwd.t)) ->
            match Bwd.to_list brs with
            | [] -> fatal (Anomaly "empty list of branches for constructor")
            | (_, pats, _, _) :: _ as brs ->
                let m = Vec.length pats.value in
                let (Bplus am) = Raw.Indexed.bplus m in
                let names =
                  Indexed.Namevec.of_vec am
                    (Vec.mmap
                       (function
                         (* Anywhere that the first pattern for this constructor has a name, we take it. *)
                         | [ Pattern.Var name ] -> name.value
                         | [ _ ] -> None)
                       [ pats.value ]) in
                let (Plus mn) = Fwn.plus m in
                let newxctx, newnums = Matchscope.exts am xctx in
                let newxs = Vec.append mn (Vec.mmap (fun [ n ] -> Either.Right n) [ newnums ]) xs in
                let newbrs =
                  List.map
                    (fun (bodyctx, (cpats : (pattern, m) Vec.t located), pats, body) ->
                      (fst (Matchscope.exts am bodyctx), Vec.append mn cpats.value pats, body))
                    brs in
                Reporter.try_with ~fatal:(fun d ->
                    match d.message with
                    | No_remaining_patterns ->
                        fatal ?loc:c.loc (Duplicate_constructor_in_match c.value)
                    | _ -> fatal_diagnostic d)
                @@ fun () ->
                (* After the first outer match, we always switch to implicit matches. *)
                Raw.Branch
                  (locate names loc, process_branches newxctx newxs seen newbrs loc `Implicit))
          cbranches in
      let tm = process_obs_or_ix xctx x in
      let refutables =
        Some
          {
            refutables =
              (fun plus_args ->
                let xctx, _ = Matchscope.exts plus_args xctx in
                Bwd_extra.prepend_map (process_ix xctx) seen
                  (Vec.to_list_map (process_obs_or_ix xctx) xs));
          } in
      let sort =
        match sort with
        | `Implicit -> `Implicit
        | `Nondep i -> `Nondep i
        | `Explicit (Wrap motive) -> `Explicit (process (Matchscope.names xctx) motive) in
      locate (Synth (Match { tm; sort; branches; refutables })) loc

let rec get_discriminees :
    observation list -> (wrapped_parse, int) Either.t Vec.wrapped * observation list =
 fun obs ->
  match obs with
  | Term tm :: Token (Op ",", _) :: obs ->
      let Wrap xs, obs = get_discriminees obs in
      (Wrap (Left (Wrap tm) :: xs), obs)
  | Term tm :: obs -> (Wrap [ Left (Wrap tm) ], obs)
  | _ -> invalid "match"

let rec get_patterns : type n. n Fwn.t -> observation list -> (pattern, n) Vec.t * observation list
    =
 fun n obs ->
  match (n, obs) with
  | _, [] | Zero, _ -> invalid "match"
  | Suc Zero, Term tm :: Token (Mapsto, _) :: obs -> ([ get_pattern tm ], obs)
  | Suc Zero, Term _ :: Term tm :: _ -> fatal ?loc:tm.loc Parse_error
  | Suc Zero, Term tm :: _ -> fatal ?loc:tm.loc Parse_error
  | Suc (Suc _ as n), Term tm :: Token (Op ",", _) :: obs ->
      let pats, obs = get_patterns n obs in
      (get_pattern tm :: pats, obs)
  | Suc (Suc _), Term tm :: _ -> fatal ?loc:tm.loc Wrong_number_of_patterns
  | _ -> invalid "match"

let rec get_branches : type a n. a Matchscope.t -> n Fwn.t -> observation list -> (a, n) branch list
    =
 fun ctx n obs ->
  match obs with
  | [ Token (RBracket, _) ] -> []
  | Token (Op "|", _) :: obs -> (
      let pats, obs = get_patterns n obs in
      match obs with
      | Term body :: obs ->
          let branches = get_branches ctx n obs in
          (ctx, pats, Wrap body) :: branches
      | _ -> invalid "match")
  | _ -> invalid "match"

(* A version of get_patterns that doesn't require a specific number of patterns in advance. *)
let rec get_any_patterns : observation list -> pattern Vec.wrapped * observation list =
 fun obs ->
  match obs with
  | Term tm :: Token (Mapsto, _) :: obs -> (Wrap [ get_pattern tm ], obs)
  | Term tm :: Token (Op ",", _) :: obs ->
      let Wrap pats, obs = get_any_patterns obs in
      (Wrap (get_pattern tm :: pats), obs)
  | _ -> invalid "match"

let rec pp_patterns accum obs =
  match obs with
  (* Not-last pattern *)
  | Term pat :: Token (Op ",", wscomma) :: obs ->
      let ppat, wpat = pp_term pat in
      pp_patterns
        (accum ^^ ppat ^^ pp_ws `None wpat ^^ Token.pp (Op ",") ^^ pp_ws `Break wscomma)
        obs
  (* Last pattern *)
  | Term pat :: obs ->
      let ppat, wpat = pp_term pat in
      (accum ^^ ppat, wpat, obs)
  | _ -> invalid "(co)match 1"

let rec pp_branches first triv accum prews obs : document * Whitespace.t list =
  match obs with
  | [ Token (RBracket, wsrbrack) ] ->
      ( accum
        ^^ ifflat (optional (pp_ws `Nobreak) prews) (optional (pp_ws `None) prews)
        ^^ Token.pp RBracket,
        wsrbrack )
  | Token (Op "|", wsbar) :: obs -> (
      let ppats, wpats, obs = pp_patterns empty obs in
      match obs with
      | Token (Mapsto, wsmapsto) :: Term body :: obs ->
          let ibody, pbody, wbody = pp_case `Nontrivial body in
          pp_branches false triv
            (accum
            ^^ optional (pp_ws `Break) prews
               (* Don't print the starting bar if we're in flat mode. *)
            ^^ ifflat
                 (group
                    (nest 2
                       ((if first then pp_ws `None wsbar
                         else Token.pp (Op "|") ^^ pp_ws `Nobreak wsbar)
                       ^^ group (align ppats)
                       ^^ pp_ws `Nobreak wpats
                       ^^ Token.pp Mapsto
                       ^^ pp_ws `Break wsmapsto
                       ^^ ibody)))
                 (group
                    (nest 2
                       ((if first && triv = `Trivial then pp_ws `None wsbar
                         else Token.pp (Op "|") ^^ pp_ws `Nobreak wsbar)
                       ^^ group (align ppats)
                       ^^ pp_ws `Nobreak wpats
                       ^^ Token.pp Mapsto
                       ^^ pp_ws `Break wsmapsto
                       ^^ ibody)))
            ^^ nest 2 pbody)
            (Some wbody) obs
      | _ -> invalid "(co)match 2")
  | _ -> invalid "(co)match 3"

let rec pp_discriminees accum prews obs : document * Whitespace.t list * observation list =
  match obs with
  (* Not-last discriminee *)
  | Term x :: Token (Op ",", wscomma) :: obs ->
      let px, wx = pp_term x in
      pp_discriminees
        (accum ^^ pp_ws `Break prews ^^ px ^^ pp_ws `None wx ^^ Token.pp (Op ","))
        wscomma obs
  (* Last discriminee *)
  | Term x :: (Token (Return, _) :: _ as obs) ->
      let px, wx = pp_term x in
      (accum ^^ pp_ws `Break prews ^^ px, wx, obs)
  | Term x :: (Token (LBracket, _) :: _ as obs) ->
      let px, wx = pp_term x in
      (accum ^^ pp_ws `Break prews ^^ px, wx, obs)
  | _ -> invalid "(co)match 4"

(* Print an implicit match, explicit match, matching lambda, or comatch, with possible multiple discriminees and possible 'return'.  We can combine comatches with matches because a "field" is just a term that can be printed like a pattern.  Always nontrivial. *)
let pp_match triv = function
  | Token (Match, wsmatch) :: obs -> (
      let pdisc, wdisc, obs = pp_discriminees (Token.pp Match) wsmatch obs in
      let pret, wret, obs =
        match obs with
        (* The motive is parsed as an abstraction sub-notation *)
        | Token (Return, wsreturn) :: Term motive :: Token (LBracket, wslbrack) :: obs ->
            let pmotive, wmotive = pp_term motive in
            ( pp_ws `Break wdisc
              ^^ Token.pp Return
              ^^ pp_ws `Nobreak wsreturn
              ^^ pmotive
              ^^ pp_ws `Nobreak wmotive
              ^^ Token.pp LBracket,
              wslbrack,
              obs )
        | Token (LBracket, wslbrack) :: obs ->
            (pp_ws `Nobreak wdisc ^^ Token.pp LBracket, wslbrack, obs)
        | _ -> invalid "(co)match 5" in
      match obs with
      | [ Token (RBracket, wsrbrack) ] ->
          (* The empty match fits all on one line *)
          ( align (group (hang 2 pdisc) ^^ pret ^^ pp_ws `Nobreak wret ^^ Token.pp RBracket),
            empty,
            wsrbrack )
      | _ ->
          let pbranches, wbranches =
            pp_branches true `Nontrivial empty None (must_start_with (Op "|") obs) in
          (align (group (hang 2 pdisc) ^^ pret), group (pp_ws `Break wret ^^ pbranches), wbranches))
  | Token (LBracket, wslbrack) :: obs ->
      let pbranches, wbranches = pp_branches true triv empty None (must_start_with (Op "|") obs) in
      ( Token.pp LBracket,
        group (pp_ws (if triv = `Trivial then `Nobreak else `Break) wslbrack ^^ pbranches),
        wbranches )
  | _ -> invalid "(co)match 6"

let () =
  (* Implicit matches can be multiple and deep matches, with multiple discriminees and multiple patterns. *)
  make implicit_mtch
    {
      name = "implicit match";
      tree = Closed_entry (eop Match (discriminees ()));
      processor =
        (fun ctx obs loc ->
          let ctx = Matchscope.make ctx in
          match obs with
          | Token (Match, _) :: obs ->
              let Wrap xs, obs = get_discriminees obs in
              let branches =
                match obs with
                | [ Token (LBracket, _); Token (RBracket, _) ] -> []
                | Token (LBracket, _) :: obs ->
                    get_branches ctx (Vec.length xs) (must_start_with (Op "|") obs)
                | _ -> invalid "implicit_match" in
              process_branches ctx xs Emp branches loc `Implicit
          | _ -> invalid "implicit_match");
      print_term = None;
      print_case = Some pp_match;
      is_case = (fun _ -> true);
    };
  (* Explicitly typed matches can be deep, but not (yet) multiple. *)
  make explicit_mtch
    {
      name = "explicit match";
      tree =
        Closed_entry
          (eop Match
             (Inner
                {
                  empty_branch with
                  term =
                    Some
                      (TokMap.singleton Return
                         (* The motive is parsed as an abstraction sub-notation *)
                         (term LBracket (mtch_branches explicit_mtch true true false)));
                }));
      processor =
        (fun ctx obs loc ->
          let ctx = Matchscope.make ctx in
          match obs with
          | Token (Match, _)
            :: Term tm
            :: Token (Return, _) (* The motive is parsed as an abstraction sub-notation *)
            :: Term ({ value = Notn ((Abs, _), n); _ } as motive)
            :: Token (LBracket, _)
            :: obs ->
              let branches =
                match obs with
                | [ Token (RBracket, _) ] -> []
                | _ -> get_branches ctx Fwn.one (must_start_with (Op "|") obs) in
              let sort =
                match args n with
                | [ Term vars; Token (Mapsto, _); Term { value = Placeholder _; _ } ] ->
                    let (Extctx (mn, _, _)) = get_vars (Matchscope.names ctx) vars in
                    `Nondep ({ value = N.to_int (N.plus_right mn); loc = vars.loc } : int located)
                | _ -> `Explicit (Wrap motive) in
              process_branches ctx [ Left (Wrap tm) ] Emp branches loc sort
          | Token (Match, _) :: _ :: Token (Return, _) :: Term nonabs :: Token (LBracket, _) :: _ ->
              fatal ?loc:nonabs.loc Parse_error
          | _ -> invalid "match");
      print_term = None;
      print_case = Some pp_match;
      is_case = (fun _ -> true);
    };
  (* Empty matches [ ] are not allowed for mtchlam, because they are parsed separately as empty_co_match. *)
  make mtchlam
    {
      name = "matchlam";
      tree = Closed_entry (eop LBracket (mtch_branches mtchlam true false true));
      processor =
        (fun ctx obs loc ->
          (* Empty matching lambdas are a different notation, empty_co_match, so here there must be at least one branch. *)
          match obs with
          | Token (LBracket, _) :: Token (Op "|", _) :: obs | Token (LBracket, _) :: obs -> (
              (* We get the *number* of patterns from the first branch. *)
              let Wrap pats, obs = get_any_patterns obs in
              match obs with
              | Term body :: obs ->
                  let n = Vec.length pats in
                  let (Bplus an) = Raw.Indexed.bplus n in
                  let ctx, xs = Matchscope.exts an (Matchscope.make ctx) in
                  let branches = get_branches ctx n obs in
                  let mtch =
                    process_branches ctx
                      (Vec.mmap (fun [ i ] -> Either.Right i) [ xs ])
                      Emp
                      ((ctx, pats, Wrap body) :: branches)
                      loc `Implicit in
                  Raw.lams an (Vec.init (fun () -> (unlocated None, ())) n ()) mtch loc
              | _ -> invalid "match")
          | _ -> invalid "match");
      print_term = None;
      print_case = Some pp_match;
      is_case = (fun _ -> true);
    }

(* ********************
   Comatches
   ******************** *)

type (_, _, _) identity += Comatch : (closed, No.plus_omega, closed) identity

let comatch : (closed, No.plus_omega, closed) notation = (Comatch, Outfix)

let rec comatch_fields () =
  field
    (op Mapsto
       (terms [ (Op "|", Lazy (lazy (comatch_fields ()))); (RBracket, Done_closed comatch) ]))

let rec process_comatch : type n.
    ((string * string list) option, n check located) Abwd.t * StringsSet.t ->
    (string option, n) Bwv.t ->
    observation list ->
    Asai.Range.t option ->
    n check located =
 fun (flds, found) ctx obs loc ->
  match obs with
  | [ Token (RBracket, _) ] -> { value = Raw.Struct (Noeta, flds); loc }
  | Token (Op "|", _)
    :: Term { value = Field (fld, pbij, _); loc = fldloc }
    :: Token (Mapsto, _)
    :: Term tm
    :: obs ->
      let tm = process ctx tm in
      if StringsSet.mem (fld, pbij) found then
        (* Comatches can't have unlabeled fields *)
        fatal ?loc:fldloc (Duplicate_method_in_comatch (fld, pbij))
      else
        process_comatch
          (Abwd.add (Some (fld, pbij)) tm flds, StringsSet.add (fld, pbij) found)
          ctx obs loc
  | _ -> invalid "comatch"

let () =
  make comatch
    {
      name = "comatch";
      tree =
        Closed_entry
          (eop LBracket
             (Inner
                {
                  empty_branch with
                  ops = TokMap.singleton (Op "|") (comatch_fields ());
                  field =
                    Some
                      (op Mapsto
                         (terms
                            [
                              (Op "|", Lazy (lazy (comatch_fields ())));
                              (RBracket, Done_closed comatch);
                            ]));
                }));
      processor =
        (fun ctx obs loc ->
          match obs with
          (* We strip off the starting bracket and make sure there is an initial bar, so that process_comatch can treat each clause uniformly. *)
          | Token (LBracket, _) :: obs ->
              let obs = must_start_with (Op "|") obs in
              process_comatch (Abwd.empty, StringsSet.empty) ctx obs loc
          | _ -> invalid "comatch");
      print_term = None;
      print_case = Some pp_match;
      is_case = (fun _ -> true);
    }

(* ********************
   Empty (co)match
 ******************** *)

type (_, _, _) identity += Empty_co_match : (closed, No.plus_omega, closed) identity

let empty_co_match : (closed, No.plus_omega, closed) notation = (Empty_co_match, Outfix)

let () =
  make empty_co_match
    {
      name = "empty_co_match";
      tree = Closed_entry (eop LBracket (op RBracket (Done_closed empty_co_match)));
      processor = (fun _ _ loc -> { value = Empty_co_match; loc });
      print_term = None;
      print_case =
        Some
          (fun _triv -> function
            | [ Token (LBracket, wslbracket); Token (RBracket, wsrbracket) ] ->
                ( Token.pp LBracket ^^ pp_ws `Nobreak wslbracket ^^ Token.pp RBracket,
                  empty,
                  wsrbracket )
            | _ -> invalid "empty_co_match");
      is_case = (fun _ -> true);
    }

(* ********************
   Codatatypes
   ******************** *)

type (_, _, _) identity += Codata : (closed, No.plus_omega, closed) identity

let codata : (closed, No.plus_omega, closed) notation = (Codata, Outfix)

let rec codata_fields bar_ok =
  Inner
    {
      empty_branch with
      ops =
        (if bar_ok then
           TokMap.of_list
             [ (Op "|", Lazy (lazy (codata_fields false))); (RBracket, Done_closed codata) ]
         else TokMap.empty);
      term =
        Some
          (TokMap.singleton Colon
             (terms [ (Op "|", Lazy (lazy (codata_fields false))); (RBracket, Done_closed codata) ]));
    }

let rec process_codata : type n.
    (Field.wrapped, n Raw.codatafield) Abwd.t ->
    (string option, n) Bwv.t ->
    observation list ->
    Asai.Range.t option ->
    n check located =
 fun flds ctx obs loc ->
  match obs with
  | [ Token (RBracket, _) ] -> { value = Raw.Codata flds; loc }
  | Token (Op "|", _)
    :: Term
         {
           value =
             App
               {
                 fn = { value = x; loc = xloc };
                 arg = { value = Field (fstr, fdstr, _); loc = fldloc };
                 _;
               };
           loc;
         }
    :: Token (Colon, _)
    :: Term ty
    :: obs -> (
      with_loc loc @@ fun () ->
      let x =
        match x with
        | Ident ([ x ], _) -> Some x
        | Placeholder _ -> None
        | Ident (x, _) -> fatal ?loc:xloc (Invalid_variable x)
        | _ -> fatal ?loc:xloc Parse_error in
      match dim_of_string (String.concat "" fdstr) with
      | Some (Any fdim) -> (
          let fld = Field.intern fstr fdim in
          match Abwd.find_opt (Field.Wrap fld) flds with
          | Some _ -> fatal ?loc:fldloc (Duplicate_method_in_codata fld)
          | None ->
              let ty = process (Bwv.snoc ctx x) ty in
              process_codata (Abwd.add (Field.Wrap fld) (Raw.Codatafield (x, ty)) flds) ctx obs loc)
      | None -> fatal (Invalid_field (String.concat "." ("" :: fstr :: fdstr))))
  | _ -> invalid "codata"

let rec pp_codata_fields first prews accum obs : document * Whitespace.t list =
  match obs with
  | [ Token (RBracket, wsrbrack) ] ->
      (accum ^^ optional (pp_ws `Nobreak) prews ^^ Token.pp RBracket, wsrbrack)
  | Token (Op "|", wsbar) :: Term varfld :: Token (Colon, wscolon) :: Term body :: obs ->
      let pvarfld, wsvarfld = pp_term varfld in
      let pbody, wbody = pp_term body in
      pp_codata_fields false (Some wbody)
        (accum
        ^^ optional (pp_ws `Break) prews
        ^^ ifflat
             (group
                (nest 2
                   (* Don't start the first field with a | in flat mode. *)
                   ((if first then pp_ws `None wsbar else Token.pp (Op "|") ^^ pp_ws `Nobreak wsbar)
                   ^^ pvarfld
                   ^^ pp_ws `Break wsvarfld
                   ^^ Token.pp Colon
                   ^^ pp_ws `Nobreak wscolon
                   ^^ pbody)))
             (group
                (nest 2
                   ((Token.pp (Op "|") ^^ pp_ws `Nobreak wsbar)
                   ^^ pvarfld
                   ^^ pp_ws `Break wsvarfld
                   ^^ Token.pp Colon
                   ^^ pp_ws `Nobreak wscolon
                   ^^ pbody))))
        obs
  | _ -> invalid "codata"

let pp_codata _triv = function
  (* The empty codatatype fits all on one line *)
  | [ Token (Codata, wscodata); Token (LBracket, wslbrack); Token (RBracket, wsrbrack) ] ->
      ( Token.pp Codata
        ^^ pp_ws `Nobreak wscodata
        ^^ Token.pp LBracket
        ^^ pp_ws `Nobreak wslbrack
        ^^ Token.pp RBracket,
        empty,
        wsrbrack )
  | Token (Codata, wscodata) :: Token (LBracket, wslbrack) :: obs ->
      let fields, ws = pp_codata_fields true None empty (must_start_with (Op "|") obs) in
      ( Token.pp Codata ^^ pp_ws `Nobreak wscodata ^^ Token.pp LBracket,
        pp_ws `Break wslbrack ^^ fields,
        ws )
  | _ -> invalid "codata"

let () =
  make codata
    {
      name = "codata";
      tree = Closed_entry (eop Codata (op LBracket (codata_fields true)));
      processor =
        (fun ctx obs loc ->
          match obs with
          | Token (Codata, _) :: Token (LBracket, _) :: obs ->
              process_codata Emp ctx (must_start_with (Op "|") obs) loc
          | _ -> invalid "codata");
      print_term = None;
      print_case = Some pp_codata;
      is_case = (fun _ -> true);
    }

(* ********************
   Record types
   ******************** *)

type (_, _, _) identity += Record : (closed, No.plus_omega, closed) identity

let record : (closed, No.plus_omega, closed) notation = (Record, Outfix)

let rec record_fields () =
  Inner
    {
      empty_branch with
      ops = TokMap.singleton RParen (Done_closed record);
      term =
        Some
          (TokMap.singleton Colon
             (terms [ (Op ",", Lazy (lazy (record_fields ()))); (RParen, Done_closed record) ]));
    }

type _ any_tel = Any_tel : ('a, 'c, 'ac) Raw.tel -> 'a any_tel

let rec process_tel : type a.
    (string option, a) Bwv.t -> StringSet.t -> observation list -> a any_tel =
 fun ctx seen obs ->
  match obs with
  | [ Token (RParen, _) ] -> Any_tel Emp
  | Token (Op ",", _) :: obs -> process_tel ctx seen obs
  | Term { value = Ident ([ name ], _); loc } :: Token (Colon, _) :: Term ty :: obs ->
      if StringSet.mem name seen then
        fatal ?loc (Duplicate_field_in_record (Field.intern name D.zero));
      let ty = process ctx ty in
      let ctx = Bwv.snoc ctx (Some name) in
      let (Any_tel tel) = process_tel ctx (StringSet.add name seen) obs in
      Any_tel (Ext (Some name, ty, tel))
  | _ -> invalid "record"

let process_record ctx obs loc =
  let opacity, obs =
    match obs with
    | Token (Sig, _)
      :: Token (Op "#", _)
      :: Token (LParen, _)
      :: Term attr
      :: Token (RParen, _)
      :: obs ->
        let opacity =
          match attr.value with
          | Ident ([ "opaque" ], _) -> `Opaque
          | Ident ([ "transparent" ], _) -> `Transparent `Labeled
          | Ident ([ "translucent" ], _) -> `Translucent `Labeled
          | App
              {
                fn = { value = Ident ([ "transparent" ], _); _ };
                arg = { value = Ident ([ "labeled" ], _); _ };
                _;
              } -> `Transparent `Labeled
          | App
              {
                fn = { value = Ident ([ "transparent" ], _); _ };
                arg = { value = Ident ([ "positional" ], _); _ };
                _;
              } -> `Transparent `Unlabeled
          | App
              {
                fn = { value = Ident ([ "translucent" ], _); _ };
                arg = { value = Ident ([ "labeled" ], _); _ };
                _;
              } -> `Translucent `Labeled
          | App
              {
                fn = { value = Ident ([ "translucent" ], _); _ };
                arg = { value = Ident ([ "positional" ], _); _ };
                _;
              } -> `Translucent `Unlabeled
          | _ -> fatal ?loc:attr.loc Unrecognized_attribute in
        (opacity, obs)
    | Token (Sig, _) :: obs -> (`Opaque, obs)
    | _ -> invalid "record" in
  match obs with
  | Term x :: Token (Mapsto, _) :: Token (LParen, _) :: obs ->
      with_loc x.loc @@ fun () ->
      let vars = process_var_list x [ (None, []) ] <|> Parse_error in
      let (Wrap vars) = Vec.of_list (List.map fst vars) in
      let (Bplus ac) = Fwn.bplus (Vec.length vars) in
      let ctx = Bwv.append ac ctx vars in
      let (Any_tel tel) = process_tel ctx StringSet.empty obs in
      Range.locate (Raw.Record (locate_opt x.loc (namevec_of_vec ac vars), tel, opacity)) loc
  | Token (LParen, _) :: obs ->
      let ctx = Bwv.snoc ctx None in
      let (Any_tel tel) = process_tel ctx StringSet.empty obs in
      { value = Record ({ value = [ None ]; loc }, tel, opacity); loc }
  | _ -> invalid "record"

let rec pp_record_fields prews accum obs =
  match obs with
  (* If the user ended with a trailing comma, don't print it, but do print its whitespace. *)
  | [ Token (Op ",", wscomma); Token (RParen, wsrparen) ] ->
      (accum ^^ optional (pp_ws `None) prews ^^ pp_ws `Nobreak wscomma ^^ Token.pp RParen, wsrparen)
  (* If the user ended without a trailing comma, don't add one. *)
  | [ Token (RParen, wsrparen) ] ->
      (accum ^^ optional (pp_ws `Nobreak) prews ^^ Token.pp RParen, wsrparen)
  (* If the previous field ended with a comma, print it. *)
  | Token (Op ",", wscomma) :: obs ->
      pp_record_fields (Some wscomma)
        (accum ^^ optional (pp_ws `None) prews ^^ Token.pp (Op ","))
        obs
  (* Now we're on a field. *)
  | Term var :: Token (Colon, wscolon) :: Term body :: obs ->
      let pvar, wvar = pp_term var in
      let pbody, wbody = pp_term body in
      pp_record_fields (Some wbody)
        (accum
        ^^ optional (pp_ws `Break) prews
        ^^ ifflat
             (group
                (nest 2
                   (pvar ^^ pp_ws `Nobreak wvar ^^ Token.pp Colon ^^ pp_ws `Nobreak wscolon ^^ pbody)))
             (group
                (nest 4
                   (blank 2
                   ^^ pvar
                   ^^ pp_ws `Nobreak wvar
                   ^^ Token.pp Colon
                   ^^ pp_ws `Nobreak wscolon
                   ^^ pbody))))
        obs
  | _ -> invalid "record"

let pp_record _triv obs =
  let withattr, wsattr, obs =
    match obs with
    | Token (Sig, wssig)
      :: Token (Op "#", wshash)
      :: Token (LParen, wslattr)
      :: Term attr
      :: Token (RParen, wsrattr)
      :: obs ->
        let pattr, wattr = pp_term attr in
        ( Token.pp Sig
          ^^ group
               (pp_ws `Break wssig
               ^^ Token.pp (Op "#")
               ^^ pp_ws `Nobreak wshash
               ^^ Token.pp LParen
               ^^ pp_ws `None wslattr
               ^^ pattr
               ^^ pp_ws `None wattr
               ^^ Token.pp RParen),
          wsrattr,
          obs )
    | Token (Sig, wssig) :: obs -> (Token.pp Sig, wssig, obs)
    | _ -> invalid "record" in
  let withlparen, wslparen, obs =
    match obs with
    | Term x :: Token (Mapsto, wsmapsto) :: Token (LParen, wslparen) :: obs ->
        let px, wx = pp_term x in
        ( withattr
          ^^ group
               (pp_ws `Break wsattr
               ^^ px
               ^^ pp_ws `Nobreak wx
               ^^ Token.pp Mapsto
               ^^ pp_ws `Nobreak wsmapsto
               ^^ Token.pp LParen),
          wslparen,
          obs )
    | Token (LParen, wslparen) :: obs ->
        (withattr ^^ pp_ws `Nobreak wsattr ^^ Token.pp LParen, wslparen, obs)
    | _ -> invalid "record" in
  match obs with
  | [ Token (RParen, wsrparen) ] ->
      (* The empty record type fits all on one line *)
      (withlparen ^^ pp_ws `None wslparen ^^ Token.pp RParen, empty, wsrparen)
  | _ ->
      let doc, ws = pp_record_fields None empty obs in
      (withlparen, pp_ws `Break wslparen ^^ doc, ws)

let () =
  make record
    {
      name = "record";
      tree =
        Closed_entry
          (eop Sig
             (Inner
                {
                  empty_branch with
                  ops =
                    TokMap.of_list
                      [
                        (LParen, record_fields ());
                        ( Op "#",
                          op LParen
                            (term RParen
                               (Inner
                                  {
                                    empty_branch with
                                    ops = TokMap.singleton LParen (record_fields ());
                                    term =
                                      Some (TokMap.singleton Mapsto (op LParen (record_fields ())));
                                  })) );
                      ];
                  term = Some (TokMap.singleton Mapsto (op LParen (record_fields ())));
                }));
      processor = (fun ctx obs loc -> process_record ctx obs loc);
      print_term = None;
      print_case = Some pp_record;
      is_case = (fun _ -> true);
    }

(* ********************
   Datatypes
   ******************** *)

type (_, _, _) identity += Data : (closed, No.plus_omega, closed) identity

let data : (closed, No.plus_omega, closed) notation = (Data, Outfix)

let rec data_constrs bar_ok =
  Inner
    {
      empty_branch with
      ops =
        (if bar_ok then
           TokMap.of_list
             [ (Op "|", Lazy (lazy (data_constrs false))); (RBracket, Done_closed data) ]
         else TokMap.empty);
      term =
        Some
          (TokMap.of_list
             [ (Op "|", Lazy (lazy (data_constrs false))); (RBracket, Done_closed data) ]);
    }

(* Extract all the typed arguments of a constructor given before its colon. *)
let rec constr_tel :
    observation ->
    (string option list * wrapped_parse) list ->
    Constr.t located * (string option list * wrapped_parse) list =
 fun tel accum ->
  match tel with
  (* Found all the arguments and reached the constructor. *)
  | Term { value = Constr (c, _); loc } -> ({ value = Constr.intern c; loc }, accum)
  (* Each argument set is given with its type in parentheses. *)
  | Term { value = App { fn; arg = { value = Notn ((Parens, _), n); loc = _ }; _ }; loc = _ } -> (
      match args n with
      | [ Token (LParen, _); Term arg; Token (RParen, _) ] -> (
          match process_typed_vars arg.value with
          | Some (vars, _, ty) -> constr_tel (Term fn) ((List.map fst vars, ty) :: accum)
          | None -> fatal Parse_error)
      | _ -> invalid "tel")
  | _ -> fatal Parse_error

let rec process_dataconstr : type n.
    (string option, n) Bwv.t ->
    (string option list * wrapped_parse) list ->
    wrapped_parse option ->
    n Raw.dataconstr =
 fun ctx tel_args ty ->
  match (tel_args, ty) with
  | (vars, argty) :: tel_args, _ -> process_dataconstr_vars ctx vars argty tel_args ty
  | [], Some (Wrap ty) -> dataconstr_of_pi (process ctx ty)
  | [], None -> Dataconstr (Emp, None)

and process_dataconstr_vars : type n.
    (string option, n) Bwv.t ->
    string option list ->
    wrapped_parse ->
    (string option list * wrapped_parse) list ->
    wrapped_parse option ->
    n Raw.dataconstr =
 fun ctx vars (Wrap argty) tel_args ty ->
  match vars with
  | [] -> process_dataconstr ctx tel_args ty
  | x :: xs ->
      let newctx = Bwv.snoc ctx x in
      let (Dataconstr (args, body)) = process_dataconstr_vars newctx xs (Wrap argty) tel_args ty in
      let arg = process ctx argty in
      Dataconstr (Ext (x, arg, args), body)

let rec process_data : type n.
    (Constr.t, n Raw.dataconstr located) Abwd.t ->
    (string option, n) Bwv.t ->
    observation list ->
    Asai.Range.t option ->
    n check located =
 fun constrs ctx obs loc ->
  match obs with
  (* Found all the constructors, done *)
  | [ Token (RBracket, _) ] -> { value = Raw.Data constrs; loc }
  (* Found the next constructor *)
  | Token (Op "|", _) :: Term tel :: obs -> (
      (* The constructor might have an explicit type given by a colon. *)
      let Wrap tel, ty =
        match tel with
        | { value = Notn ((Asc, _), n); loc = _ } -> (
            match args n with
            | [ Term tel; Token (Colon, _); Term ty ] -> (Wrap tel, Some (Wrap ty))
            | _ -> invalid "data")
        | _ -> (Wrap tel, None) in
      let c, tel_args = constr_tel (Term tel) [] in
      match Abwd.find_opt c.value constrs with
      | Some _ -> fatal ?loc:c.loc (Duplicate_constructor_in_data c.value)
      | None ->
          let dc = process_dataconstr ctx tel_args ty in
          process_data
            (Abwd.add c.value ({ value = dc; loc = tel.loc } : n dataconstr located) constrs)
            ctx obs loc)
  | _ -> invalid "data"

let rec pp_data_constrs first prews accum obs =
  match obs with
  | [ Token (RBracket, wsrbrack) ] ->
      (accum ^^ optional (pp_ws `Nobreak) prews ^^ Token.pp RBracket, wsrbrack)
  | Token (Op "|", wsbar) :: Term constr :: obs ->
      let pconstr, wconstr = pp_term constr in
      pp_data_constrs false (Some wconstr)
        (accum
        ^^ optional (pp_ws `Break) prews
        (* Don't print the starting bar if we're in flat mode *)
        ^^ ifflat
             (group
                (nest 2
                   ((if first then pp_ws `None wsbar else Token.pp (Op "|") ^^ pp_ws `Nobreak wsbar)
                   ^^ pconstr)))
             (group (nest 2 (Token.pp (Op "|") ^^ pp_ws `Nobreak wsbar ^^ pconstr))))
        obs
  | _ -> invalid "data"

let pp_data _triv = function
  (* The empty datatype fits all on one line *)
  | [ Token (Data, wsdata); Token (LBracket, wslbrack); Token (RBracket, wsrbrack) ] ->
      ( Token.pp Data
        ^^ pp_ws `Nobreak wsdata
        ^^ Token.pp LBracket
        ^^ pp_ws `None wslbrack
        ^^ Token.pp RBracket,
        empty,
        wsrbrack )
  | Token (Data, wsdata) :: Token (LBracket, wslbrack) :: obs ->
      let doc, ws = pp_data_constrs true None empty (must_start_with (Op "|") obs) in
      (Token.pp Data ^^ pp_ws `Nobreak wsdata ^^ Token.pp LBracket, pp_ws `Break wslbrack ^^ doc, ws)
  | _ -> invalid "data"

let () =
  make data
    {
      name = "data";
      tree = Closed_entry (eop Data (op LBracket (data_constrs true)));
      processor =
        (fun ctx obs loc ->
          match obs with
          | [ Token (Data, _); Token (LBracket, _); Token (RBracket, _) ] ->
              { value = Raw.Data Emp; loc }
          | Token (Data, _) :: Token (LBracket, _) :: obs ->
              process_data Emp ctx (must_start_with (Op "|") obs) loc
          | _ -> invalid "data");
      print_term = None;
      print_case = Some pp_data;
      is_case = (fun _ -> true);
    }

(* ********************
   Generating the state
 ******************** *)

let builtins =
  ref
    (Situation.empty
    |> Situation.add parens
    |> Situation.add Postprocess.braces
    |> Situation.add letin
    |> Situation.add letrec
    |> Situation.add asc
    |> Situation.add abs
    |> Situation.add cubeabs
    |> Situation.add arrow
    |> Situation.add universe
    |> Situation.add coloneq
    |> Situation.add comatch
    |> Situation.add dot
    |> Situation.add implicit_mtch
    |> Situation.add explicit_mtch
    |> Situation.add mtchlam
    |> Situation.add empty_co_match
    |> Situation.add codata
    |> Situation.add record
    |> Situation.add data)

let run : type a. (unit -> a) -> a = fun f -> Situation.run_on !builtins f
