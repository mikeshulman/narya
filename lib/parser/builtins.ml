open Util
open Compile
open Print
open Format
open Core
open Raw
open Reporter
open Notation
open Monad.Ops (Monad.Maybe)

(* ********************
   Parentheses
 ******************** *)

let parens = make "parens" Outfix

let () =
  set_tree parens (Closed_entry (eop LParen (term RParen (Done_closed parens))));
  set_compiler parens
    {
      compile =
        (fun ctx obs ->
          let Wrap body, obs = get_term obs in
          let () = get_done obs in
          compile ctx body);
    };
  set_print parens (fun ppf obs ->
      let body, obs = get_term obs in
      let () = get_done obs in
      fprintf ppf "@[<hov 1>%a%a%a@]" pp_tok LParen pp_term body pp_tok RParen);
  set_print_as_case parens (fun ppf obs ->
      (* Parentheses should never be required in a case tree, so we omit them during reformatting. *)
      let body, obs = get_term obs in
      let () = get_done obs in
      pp_term ppf body)

(* ********************
   Let-binding
 ******************** *)

(* Let-in doesn't need to be right-associative in order to chain, because it is left-closed.  Declaring it to be nonassociative means that "let x := y in z : A" doesn't parse without parentheses, which I think is best as it looks ambiguous.  (The same idea applies to abstractions, although they are built into the parser rather than defined as mixfix notations.) *)

let letin = make "let" (Prefix No.minus_omega)

let () =
  set_tree letin
    (Closed_entry
       (eop Let
          (ident
             (ops
                [
                  (Coloneq, term In (Done_closed letin));
                  (Colon, term Coloneq (term In (Done_closed letin)));
                ]))));
  set_compiler letin
    {
      compile =
        (fun ctx obs ->
          let x, obs = get_ident obs in
          let Wrap ty_or_tm, obs = get_term obs in
          let Wrap tm_or_body, obs = get_term obs in
          match get_next obs with
          | `Term (Wrap body, obs) -> (
              let () = get_done obs in
              let ty, tm = (compile ctx ty_or_tm, compile ctx tm_or_body) in
              match compile (Snoc (ctx, x)) body with
              | Synth body -> Synth (Let (Asc (tm, ty), body))
              | _ -> fatal (Nonsynthesizing "body of let"))
          | `Done -> (
              let () = get_done obs in
              match compile ctx ty_or_tm with
              | Synth term -> (
                  match compile (Snoc (ctx, x)) tm_or_body with
                  | Synth body -> Synth (Let (term, body))
                  | _ -> fatal (Nonsynthesizing "body of let"))
              | _ -> fatal (Nonsynthesizing "value of let"))
          | _ -> fatal (Anomaly "impossible thing in let"));
    };
  set_print letin (fun ppf obs ->
      let rec pp_let ppf obs =
        let x, obs = get_ident obs in
        let ty_or_tm, obs = get_term obs in
        let tm_or_body, obs = get_term obs in
        match get_next obs with
        | `Term (body, obs) ->
            let () = get_done obs in
            let ty, tm = (ty_or_tm, tm_or_body) in
            fprintf ppf
              (match style () with
              | Compact -> "@[<hov 2>@[<hv 2>%a %a@ %a %a@ %a %a@]@ %a@]@ %a"
              | Noncompact -> "@[<hv 2>%a %a@ %a %a@ %a %a@ %a@]@ %a")
              pp_tok Let pp_var x pp_tok Colon pp_term ty pp_tok Coloneq pp_term tm pp_tok In
              pp_let_body body
        | `Done ->
            let () = get_done obs in
            let tm, body = (ty_or_tm, tm_or_body) in
            fprintf ppf
              (match style () with
              | Compact -> "@[<hov 2>%a %a %a@ %a@ %a@]@ %a"
              | Noncompact -> "@[<hv 2>%a %a %a@ %a@ %a@]@ %a")
              pp_tok Let pp_var x pp_tok Coloneq pp_term tm pp_tok In pp_let_body body
        | _ -> fatal (Anomaly "impossible thing in let")
      and pp_let_body ppf tr =
        match tr with
        | Wrap (Notn n) when equal n.notn letin -> pp_let ppf (args n)
        | _ -> pp_term ppf tr in
      fprintf ppf "@[<hv 0>%a@]" pp_let obs)

(* ********************
   Non-dependent function types
 ******************** *)

let arrow = make "arrow" (Infixr No.zero)

let () =
  set_tree arrow (Open_entry (eop Arrow (done_open arrow)));
  set_compiler arrow
    {
      compile =
        (fun ctx obs ->
          let Wrap dom, obs = get_term obs in
          let Wrap cod, obs = get_term obs in
          let () = get_done obs in
          let dom = compile ctx dom in
          let cod = compile (Snoc (ctx, None)) cod in
          Synth (Pi (dom, cod)));
    }

(* These are pretty-printed together with pi-types, see below. *)

(* ********************
   Pi-types
 ******************** *)

(* I think these are the only flags we're using, so if we could get rid of them, we could simplify by getting rid of flags completely. *)
type flag += Implicit_pi | Explicit_pi | Default_pi

let pi = make "pi" (Prefixr No.zero)

let rec explicit_pi () = Flag (Explicit_pi, ident (explicit_pi_vars ()))
and implicit_pi () = Flag (Implicit_pi, ident (implicit_pi_vars ()))

and explicit_pi_vars () =
  Inner
    {
      empty_branch with
      ops = TokMap.singleton Colon (term RParen (more_pi ()));
      ident = Some (Lazy (lazy (explicit_pi_vars ())));
    }

and implicit_pi_vars () =
  Inner
    {
      empty_branch with
      ops =
        TokMap.singleton Colon
          (terms
             [
               (Coloneq, Flag (Default_pi, term RBrace (Lazy (lazy (more_pi ())))));
               (RBrace, Lazy (lazy (more_pi ())));
             ]);
      ident = Some (Lazy (lazy (implicit_pi_vars ())));
    }

and more_pi () =
  ops
    [
      (LParen, Lazy (lazy (explicit_pi ())));
      (LBrace, Lazy (lazy (implicit_pi ())));
      (Arrow, Done_closed pi);
    ]

let () = set_tree pi (Closed_entry (eops [ (LParen, explicit_pi ()); (LBrace, implicit_pi ()) ]))

let rec compile_pi : type n. (string option, n) Bwv.t -> observation list -> n check =
 fun ctx obs ->
  let f = get_flag [ Explicit_pi; Implicit_pi ] obs in
  match f with
  | Some Implicit_pi -> fatal (Unimplemented "Implicit pi-types")
  | Some Explicit_pi -> compile_pi_names Zero ctx obs
  | _ ->
      let Wrap body, obs = get_term obs in
      let () = get_done obs in
      compile ctx body

and compile_pi_names :
    type m n mn. (m, n, mn) N.plus -> (string option, mn) Bwv.t -> observation list -> m check =
 fun mn ctx obs ->
  match get_next obs with
  | `Done -> fatal (Anomaly "Unexpected end of arguments")
  | `Ident (x, obs) -> compile_pi_names (Suc mn) (Snoc (ctx, x)) obs
  | `Constr _ | `Field _ -> fatal (Anomaly "Impossible thing in pi")
  | `Term (dom, obs) -> (
      let f = get_flag [ Default_pi ] obs in
      match f with
      | Some Default_pi -> fatal (Unimplemented "Default arguments not implemented")
      | _ ->
          let cod = compile_pi ctx obs in
          compile_pi_doms mn ctx dom cod)

and compile_pi_doms :
    type m n mn.
    (m, n, mn) N.plus -> (string option, mn) Bwv.t -> wrapped_parse -> mn check -> m check =
 fun mn ctx (Wrap dom) cod ->
  match (mn, ctx) with
  | Zero, _ -> cod
  | Suc mn, Snoc (ctx, _) ->
      let cdom = compile ctx dom in
      compile_pi_doms mn ctx (Wrap dom) (Synth (Pi (cdom, cod)))

let () = set_compiler pi { compile = compile_pi }

let rec pp_pi (arr : bool) (obs : observation list) :
    int * (formatter -> unit -> unit) * wrapped_parse =
  let f = get_flag [ Explicit_pi; Implicit_pi ] obs in
  match f with
  | Some Implicit_pi -> (
      let names, obs = get_idents obs in
      let ty, obs = get_term obs in
      let f = get_flag [ Default_pi ] obs in
      match f with
      | Some Default_pi -> fatal (Unimplemented "Default arguments not implemented")
      | _ ->
          let sp, rest, body = pp_pi false obs in
          ( 1,
            (fun ppf () ->
              if arr then pp_tok ppf Arrow;
              fprintf ppf "%a%a %a %a%a%t" pp_tok LBrace
                (pp_print_list ~pp_sep:pp_print_space pp_var)
                names pp_tok Colon pp_term ty pp_tok RBrace (fun ppf -> pp_print_break ppf sp 0);
              rest ppf ()),
            body ))
  | Some Explicit_pi -> (
      let idents, obs = get_idents obs in
      let ty, obs = get_term obs in
      let f = get_flag [ Default_pi ] obs in
      match f with
      | Some Default_pi -> fatal (Unimplemented "Default arguments not implemented")
      | _ ->
          let sp, rest, body = pp_pi false obs in
          ( 1,
            (fun ppf () ->
              if arr then fprintf ppf "%a " pp_tok Arrow;
              fprintf ppf "%a%a %a %a%a%t" pp_tok LParen
                (pp_print_list ~pp_sep:pp_print_space pp_var)
                idents pp_tok Colon pp_term ty pp_tok RParen (fun ppf -> pp_print_break ppf sp 0);
              rest ppf ()),
            body ))
  | _ -> (
      let Wrap body, obs = get_term obs in
      let () = get_done obs in
      match body with
      | Notn n when equal n.notn pi -> pp_pi false (args n)
      | Notn n when equal n.notn arrow ->
          let rest, body = pp_arrow true (args n) in
          (1, rest, body)
      | _ -> (0, (fun _ () -> ()), Wrap body))

and pp_arrow (arr : bool) (obs : observation list) : (formatter -> unit -> unit) * wrapped_parse =
  let dom, obs = get_term obs in
  let Wrap body, obs = get_term obs in
  let () = get_done obs in
  match body with
  | Notn n when equal n.notn pi ->
      let sp, rest, body = pp_pi true (args n) in
      ( (fun ppf () ->
          if arr then fprintf ppf "%a " pp_tok Arrow;
          fprintf ppf "%a%t" pp_term dom (fun ppf -> pp_print_break ppf sp 0);
          rest ppf ()),
        body )
  | Notn n when equal n.notn arrow ->
      let rest, body = pp_arrow true (args n) in
      ( (fun ppf () ->
          if arr then fprintf ppf "%a " pp_tok Arrow;
          fprintf ppf "%a@ " pp_term dom;
          rest ppf ()),
        body )
  | _ ->
      ( (fun ppf () ->
          if arr then fprintf ppf "%a " pp_tok Arrow;
          (* The @, here are the zero-space cuts that play the role of the returned 0s in the last case of pp_pi, so we don't need to return a number from pp_arrow. *)
          fprintf ppf "%a@," pp_term dom),
        Wrap body )

let () =
  set_print pi @@ fun ppf obs ->
  let _sp, pp_doms, body = pp_pi false obs in
  fprintf ppf "@[<b 1>@[<hov 2>%a@]%t%a %a@]" pp_doms ()
    (pp_print_custom_break ~fits:("", 1, "") ~breaks:("", 0, " "))
    pp_tok Arrow pp_term body

let () =
  set_print arrow @@ fun ppf obs ->
  let pp_doms, body = pp_arrow false obs in
  fprintf ppf "@[<b 1>@[<hov 2>%a@]%t%a %a@]" pp_doms ()
    (pp_print_custom_break ~fits:("", 1, "") ~breaks:("", 0, " "))
    pp_tok Arrow pp_term body

(* ********************
   Ascription
 ******************** *)

let asc = make "ascription" (Infix No.minus_omega)
let () = set_tree asc (Open_entry (eop Colon (done_open asc)))

let () =
  set_compiler asc
    {
      compile =
        (fun ctx obs ->
          let Wrap tm, obs = get_term obs in
          let Wrap ty, obs = get_term obs in
          let () = get_done obs in
          let tm = compile ctx tm in
          let ty = compile ctx ty in
          Synth (Asc (tm, ty)));
    };
  set_print asc @@ fun ppf obs ->
  let tm, obs = get_term obs in
  let ty, obs = get_term obs in
  let () = get_done obs in
  fprintf ppf "@[<b 0>%a@ %a %a" pp_term tm pp_tok Colon pp_term ty

(* ********************
   The universe
 ******************** *)

let universe = make "Type" Outfix

let () =
  set_tree universe (Closed_entry (eop (Ident "Type") (Done_closed universe)));
  set_compiler universe
    {
      compile =
        (fun _ obs ->
          let () = get_done obs in
          Synth UU);
    };
  set_print universe @@ fun ppf obs ->
  let () = get_done obs in
  pp_print_string ppf "Type"

(* ********************
   Degeneracies (refl and sym)
 ******************** *)

let refl = make "refl" Outfix

let () =
  set_tree refl
    (Closed_entry (eops [ (Ident "refl", Done_closed refl); (Ident "Id", Done_closed refl) ]));
  set_compiler refl
    {
      compile =
        (fun _ obs ->
          let () = get_done obs in
          Synth (Act ("refl", Dim.refl, None)));
    };
  set_print refl @@ fun ppf obs ->
  let () = get_done obs in
  pp_print_string ppf "refl"

let sym = make "sym" Outfix

let () =
  set_tree sym (Closed_entry (eop (Ident "sym") (Done_closed sym)));
  set_compiler sym
    {
      compile =
        (fun _ obs ->
          let () = get_done obs in
          Synth (Act ("sym", Dim.sym, None)));
    };
  set_print sym @@ fun ppf obs ->
  let () = get_done obs in
  pp_print_string ppf "sym"

(* ********************
   Anonymous structs and comatches
 ******************** *)

let struc = make "struc" Outfix

let () =
  set_tree struc
    (let rec struc_fields () =
       Inner
         {
           empty_branch with
           ops = TokMap.singleton RBrace (Done_closed struc);
           ident =
             Some
               (op Coloneq
                  (terms [ (Op ";", Lazy (lazy (struc_fields ()))); (RBrace, Done_closed struc) ]));
         } in
     let rec comatch_fields () =
       Inner
         {
           empty_branch with
           ops = TokMap.singleton RBrace (Done_closed struc);
           field =
             Some
               (op Mapsto
                  (terms [ (Op ";", Lazy (lazy (comatch_fields ()))); (RBrace, Done_closed struc) ]));
         } in
     Closed_entry
       (eop LBrace
          (Inner
             {
               empty_branch with
               ops = TokMap.singleton RBrace (Done_closed struc);
               ident =
                 Some
                   (op Coloneq
                      (terms
                         [ (Op ";", Lazy (lazy (struc_fields ()))); (RBrace, Done_closed struc) ]));
               field =
                 Some
                   (op Mapsto
                      (terms
                         [ (Op ";", Lazy (lazy (comatch_fields ()))); (RBrace, Done_closed struc) ]));
             })))

let rec compile_struc :
    type n. n check list Field.Map.t -> (string option, n) Bwv.t -> observation list -> n check =
 fun flds ctx obs ->
  match get_next obs with
  | `Done -> Raw.Struct flds
  | `Ident (Some x, obs) | `Field (x, obs) ->
      let Wrap tm, obs = get_term obs in
      let tm = compile ctx tm in
      compile_struc (flds |> Field.Map.add_to_list (Field.intern x) tm) ctx obs
  | `Ident (None, _) -> fatal Unnamed_field_in_struct
  | `Constr _ | `Term _ -> fatal (Anomaly "Impossible thing in struct")

let () = set_compiler struc { compile = (fun ctx obs -> compile_struc Field.Map.empty ctx obs) }

let rec pp_fld :
    type a.
    formatter ->
    (formatter -> a -> unit) ->
    a ->
    Token.t ->
    wrapped_parse ->
    observation list ->
    unit =
 fun ppf pp x tok tm obs ->
  fprintf ppf "@[<hov 2>%a %a@ %a@]%a" pp x pp_tok tok pp_term tm
    (pp_print_option (fun ppf -> fprintf ppf " %a@ " pp_tok))
    (if get_next obs = `Done then None else Some (Op ";"))

and pp_fields ppf obs =
  match get_next obs with
  | `Done -> ()
  | `Ident (Some x, obs) | `Field (x, obs) ->
      let tm, obs = get_term obs in
      (match state () with
      | Term -> pp_fld ppf pp_var (Some x) Coloneq tm obs
      | Case -> pp_fld ppf pp_field x Mapsto tm obs);
      pp_fields ppf obs
  | `Ident (None, _) -> fatal Unnamed_field_in_struct
  | `Constr _ | `Term _ -> fatal (Anomaly "Impossible thing in struct")

let pp_struc ppf obs =
  let style, state = (style (), state ()) in
  (match state with
  | Term ->
      if style = Noncompact then pp_open_box ppf 0;
      pp_open_hvbox ppf 2
  | Case -> pp_open_vbox ppf 2);
  pp_tok ppf LBrace;
  if style = Compact then pp_print_string ppf " " else pp_print_space ppf ();
  pp_fields ppf obs;
  (if style = Compact then pp_print_string ppf " "
   else
     match state with
     | Term ->
         pp_close_box ppf ();
         pp_print_custom_break ~fits:("", 1, "") ~breaks:(" ;", 0, "") ppf
     | Case -> pp_print_custom_break ~fits:("", 1, "") ~breaks:(" ;", -2, "") ppf);
  pp_tok ppf RBrace;
  pp_close_box ppf ()

(* In standard formatting, structures in case trees are written as copattern-matches with field dots and ↦, while those in terms are written without dots and with ≔. *)
let () =
  set_print struc pp_struc;
  set_print_as_case struc pp_struc

(* ********************
   Matches
 ******************** *)

let mtch = make "match" Outfix

let rec pattern_vars () =
  Inner
    {
      empty_branch with
      ident = Some (Lazy (lazy (pattern_vars ())));
      ops =
        TokMap.singleton Mapsto
          (terms [ (Op "|", Lazy (lazy (innermtch ()))); (RBracket, Done_closed mtch) ]);
    }

and innermtch () =
  Inner
    {
      empty_branch with
      ops = TokMap.of_list [ (RBracket, Done_closed mtch) ];
      constr = Some (pattern_vars ());
    }

let () =
  set_tree mtch
    (Closed_entry
       (eop LBracket
          (Inner
             {
               empty_branch with
               ops = TokMap.of_list [ (Op "|", innermtch ()); (RBracket, Done_closed mtch) ];
               ident =
                 Some
                   (Inner
                      {
                        ops =
                          TokMap.of_list [ (Op "|", innermtch ()); (RBracket, Done_closed mtch) ];
                        ident = None;
                        constr = None;
                        field = Some (op (Op "|") (innermtch ()));
                        term = None;
                      });
               constr = Some (pattern_vars ());
             })))

let rec compile_branch_names :
    type a b ab.
    (a, b, ab) N.plus ->
    (string option, ab) Bwv.t ->
    Constr.t ->
    observation list ->
    a Raw.branch * observation list =
 fun ab ctx c obs ->
  match get_next obs with
  | `Ident (a, obs) -> compile_branch_names (Suc ab) (Snoc (ctx, a)) c obs
  | `Term (Wrap t, obs) ->
      let tm = compile ctx t in
      (Branch (c, ab, tm), obs)
  | `Constr _ | `Field _ -> fatal (Anomaly "Impossible thing in match")
  | `Done -> fatal (Anomaly "Unexpected end of input")

let rec compile_branches : type n. (string option, n) Bwv.t -> observation list -> n Raw.branch list
    =
 fun ctx obs ->
  match get_next obs with
  | `Done -> []
  | `Constr (c, obs) -> compile_branch ctx c obs
  | `Field _ | `Term _ | `Ident _ -> fatal (Anomaly "Impossible thing in match")

and compile_branch :
    type n. (string option, n) Bwv.t -> string -> observation list -> n Raw.branch list =
 fun ctx c obs ->
  let br, obs = compile_branch_names Zero ctx (Constr.intern c) obs in
  let rest = compile_branches ctx obs in
  br :: rest

let () =
  set_compiler mtch
    {
      compile =
        (fun ctx obs ->
          match get_next obs with
          (* Can't match an underscore *)
          | `Ident (None, _) -> fatal Unnamed_variable_in_match
          | `Ident (Some ident, obs) -> (
              match Bwv.index (Some ident) ctx with
              | None -> fatal (Unbound_variable ident)
              | Some x ->
                  let fa, obs =
                    (* If the next thing looks like a field, it might mean a face of a cube variable. *)
                    match get_next obs with
                    | `Field (fld, obs) -> (
                        match Dim.sface_of_string fld with
                        | Some fa -> (Some fa, obs)
                        | None -> fatal Parse_error)
                    | _ -> (None, obs) in
                  let branches = compile_branches ctx obs in
                  Match ((x, fa), branches))
          (* If we went right to a constructor, then that means it's a matching lambda. *)
          | `Constr (c, obs) ->
              let branches = compile_branch (Snoc (ctx, None)) c obs in
              Lam (`Normal, Match ((Top, None), branches))
          (* If we went right to Done, that means it's a matching lambda with zero branches. *)
          | `Done -> Lam (`Normal, Match ((Top, None), []))
          | `Field _ | `Term _ -> fatal (Anomaly "Impossible thing in match"));
    }

let rec branch_vars obs =
  match get_next obs with
  | `Ident (x, obs) ->
      let rest, obs = branch_vars obs in
      (x :: rest, obs)
  | _ -> ([], obs)

let rec pp_branches brk ppf obs =
  match get_next obs with
  | `Constr (c, obs) ->
      let vars, obs = branch_vars obs in
      let Wrap tm, obs = get_term obs in
      let style = style () in
      if brk || style = Noncompact then pp_print_break ppf 0 2 else pp_print_string ppf " ";
      (match tm with
      | Notn n when equal n.notn mtch && style = Compact ->
          fprintf ppf "@[<hov 0>@[<hov 4>%a %a@ %a%a@] %a@]" pp_tok (Op "|") pp_constr c
            (fun ppf -> List.iter (fun x -> fprintf ppf "%a@ " pp_var x))
            vars pp_tok Mapsto (pp_match false) (args n)
      | _ ->
          fprintf ppf "@[<b 1>@[<hov 4>%a %a@ %a%a@]%t%a@]" pp_tok (Op "|") pp_constr c
            (fun ppf -> List.iter (fun x -> fprintf ppf "%a@ " pp_var x))
            vars pp_tok Mapsto
            (pp_print_custom_break ~fits:("", 1, "") ~breaks:("", 0, " "))
            pp_term (Wrap tm));
      pp_branches true ppf obs
  | `Done -> ()
  | _ -> fatal (Anomaly "Impossible thing in match")

and pp_match box ppf obs =
  match get_next obs with
  | `Ident (ident, obs) ->
      if box then pp_open_vbox ppf 0;
      pp_tok ppf LBracket;
      pp_print_string ppf " ";
      pp_var ppf ident;
      pp_branches true ppf obs;
      if style () = Compact then pp_print_string ppf " " else pp_print_cut ppf ();
      pp_tok ppf RBracket;
      if box then pp_close_box ppf ()
  | _ ->
      let style = style () in
      if box || style = Noncompact then pp_open_vbox ppf 0;
      pp_tok ppf LBracket;
      pp_branches ((not box) || style = Noncompact) ppf obs;
      if style = Compact then pp_print_string ppf " " else pp_print_cut ppf ();
      pp_tok ppf RBracket;
      if box || style = Noncompact then pp_close_box ppf ()

(* Matches are only valid in case trees. *)
let () = set_print_as_case mtch (pp_match true)

(* ********************
   Generating the state
 ******************** *)

let builtins =
  ref
    (State.empty
    |> State.add parens
    |> State.add letin
    |> State.add pi
    |> State.add asc
    |> State.add arrow
    |> State.add universe
    |> State.add refl
    |> State.add sym
    |> State.add struc
    |> State.add mtch)
