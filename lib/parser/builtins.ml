open Util
open Compile
open Print
open Format
open Notations
open Core
open Raw
open Reporter
open Monad.Ops (Monad.Maybe)

(* ********************
   Parentheses
 ******************** *)

let parens =
  make ~name:"()" ~tightness:Float.nan ~left:Closed ~right:Closed ~assoc:Non ~tree:(fun n ->
      eop LParen (term RParen (Done n)))

let () =
  add_compiler parens
    {
      compile =
        (fun ctx obs ->
          let body, obs = get_term obs in
          let () = get_done obs in
          compile ctx body);
    }

let () =
  add_term_pp parens @@ fun ppf obs ->
  let body, obs = get_term obs in
  let () = get_done obs in
  fprintf ppf "@[<hov 1>%a%a%a@]" pp_tok LParen pp_term body pp_tok RParen

(* Parentheses should never be required in a case tree, so we omit them during reformatting. *)
let () =
  add_case_pp parens @@ fun ppf obs ->
  let body, obs = get_term obs in
  let () = get_done obs in
  pp_case ppf body

(* ********************
   Let-binding
 ******************** *)

(* Let-in doesn't need to be right-associative in order to chain, because it is left-closed.  Declaring it to be nonassociative means that "let x := y in z : A" doesn't parse without parentheses, which I think is best as it looks ambiguous.  (The same idea applies to abstractions, although they are built into the parser rather than defined as mixfix notations.) *)
let letin =
  make ~name:"let" ~tightness:Float.neg_infinity ~left:Closed ~right:Open ~assoc:Non ~tree:(fun n ->
      eop Let (name (ops [ (Coloneq, term In (Done n)); (Colon, term Coloneq (term In (Done n))) ])))

let () =
  add_compiler letin
    {
      compile =
        (fun ctx obs ->
          let x, obs = get_name obs in
          let ty_or_tm, obs = get_term obs in
          let tm_or_body, obs = get_term obs in
          match get_next obs with
          | `Term (body, obs) -> (
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
    }

let rec pp_let ppf obs =
  let x, obs = get_name obs in
  let ty_or_tm, obs = get_term obs in
  let tm_or_body, obs = get_term obs in
  match get_next obs with
  | `Term (body, obs) ->
      let () = get_done obs in
      let ty, tm = (ty_or_tm, tm_or_body) in
      fprintf ppf
        (if compact () then "@[<hov 2>@[<hv 2>%a %a@ %a %a@ %a %a@]@ %a@]@ %a"
         else "@[<hv 2>%a %a@ %a %a@ %a %a@ %a@]@ %a")
        pp_tok Let pp_var x pp_tok Colon pp_term ty pp_tok Coloneq pp_term tm pp_tok In pp_let_body
        body
  | `Done ->
      let () = get_done obs in
      let tm, body = (ty_or_tm, tm_or_body) in
      fprintf ppf
        (if compact () then "@[<hov 2>%a %a %a@ %a@ %a@]@ %a" else "@[<hv 2>%a %a %a@ %a@ %a@]@ %a")
        pp_tok Let pp_var x pp_tok Coloneq pp_term tm pp_tok In pp_let_body body
  | _ -> fatal (Anomaly "impossible thing in let")

and pp_let_body ppf tr =
  match tr with
  | Notn (n, obs) when n = letin -> pp_let ppf obs
  | _ -> pp_term ppf tr

let () = add_term_pp letin @@ fun ppf obs -> fprintf ppf "@[<hv 0>%a@]" pp_let obs

(* ********************
   Non-dependent function types
 ******************** *)

let arrow =
  make ~name:"->" ~tightness:0. ~left:Open ~right:Open ~assoc:Right ~tree:(fun n ->
      eop Arrow (Done n))

let () =
  add_compiler arrow
    {
      compile =
        (fun ctx obs ->
          let dom, obs = get_term obs in
          let cod, obs = get_term obs in
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

let pi =
  make ~name:"pi" ~tightness:0. ~left:Closed ~right:Open ~assoc:Right ~tree:(fun n ->
      let rec explicit_pi () = Flag (Explicit_pi, name (explicit_pi_vars ()))
      and implicit_pi () = Flag (Implicit_pi, name (implicit_pi_vars ()))
      and explicit_pi_vars () =
        Inner
          {
            ops = TokMap.singleton Colon (term RParen (more_pi ()));
            constr = None;
            field = None;
            name = Some (Lazy (lazy (explicit_pi_vars ())));
            term = None;
          }
      and implicit_pi_vars () =
        Inner
          {
            ops =
              TokMap.singleton Colon
                (terms
                   [
                     (Coloneq, Flag (Default_pi, term RBrace (Lazy (lazy (more_pi ())))));
                     (RBrace, Lazy (lazy (more_pi ())));
                   ]);
            constr = None;
            field = None;
            name = Some (Lazy (lazy (implicit_pi_vars ())));
            term = None;
          }
      and more_pi () =
        ops
          [
            (LParen, Lazy (lazy (explicit_pi ())));
            (LBrace, Lazy (lazy (implicit_pi ())));
            (Arrow, Done n);
          ] in
      eops [ (LParen, explicit_pi ()); (LBrace, implicit_pi ()) ])

let rec compile_pi : type n. (string option, n) Bwv.t -> observation list -> n check =
 fun ctx obs ->
  let f = get_flag [ Explicit_pi; Implicit_pi ] obs in
  match f with
  | Some Implicit_pi -> fatal (Unimplemented "Implicit pi-types")
  | Some Explicit_pi -> compile_pi_names Zero ctx obs
  | _ ->
      let body, obs = get_term obs in
      let () = get_done obs in
      compile ctx body

and compile_pi_names :
    type m n mn. (m, n, mn) N.plus -> (string option, mn) Bwv.t -> observation list -> m check =
 fun mn ctx obs ->
  match get_next obs with
  | `Done -> fatal (Anomaly "Unexpected end of arguments")
  | `Name (x, obs) -> compile_pi_names (Suc mn) (Snoc (ctx, x)) obs
  | `Constr _ | `Field _ -> fatal (Anomaly "Impossible thing in pi")
  | `Term (dom, obs) -> (
      let f = get_flag [ Default_pi ] obs in
      match f with
      | Some Default_pi -> fatal (Unimplemented "Default arguments not implemented")
      | _ ->
          let cod = compile_pi ctx obs in
          compile_pi_doms mn ctx dom cod)

and compile_pi_doms :
    type m n mn. (m, n, mn) N.plus -> (string option, mn) Bwv.t -> parse_tree -> mn check -> m check
    =
 fun mn ctx dom cod ->
  match (mn, ctx) with
  | Zero, _ -> cod
  | Suc mn, Snoc (ctx, _) ->
      let cdom = compile ctx dom in
      compile_pi_doms mn ctx dom (Synth (Pi (cdom, cod)))

let () = add_compiler pi { compile = compile_pi }

let rec pp_pi (arr : bool) (obs : observation list) : int * (formatter -> unit -> unit) * parse_tree
    =
  let f = get_flag [ Explicit_pi; Implicit_pi ] obs in
  match f with
  | Some Implicit_pi -> (
      let names, obs = get_names obs in
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
      let names, obs = get_names obs in
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
                names pp_tok Colon pp_term ty pp_tok RParen (fun ppf -> pp_print_break ppf sp 0);
              rest ppf ()),
            body ))
  | _ -> (
      let body, obs = get_term obs in
      let () = get_done obs in
      match body with
      | Notn (n, obs) when n = pi -> pp_pi false obs
      | Notn (n, obs) when n = arrow ->
          let rest, body = pp_arrow true obs in
          (1, rest, body)
      | _ -> (0, (fun _ () -> ()), body))

and pp_arrow (arr : bool) (obs : observation list) : (formatter -> unit -> unit) * parse_tree =
  let dom, obs = get_term obs in
  let body, obs = get_term obs in
  let () = get_done obs in
  match body with
  | Notn (n, obs) when n = pi ->
      let sp, rest, body = pp_pi true obs in
      ( (fun ppf () ->
          if arr then fprintf ppf "%a " pp_tok Arrow;
          fprintf ppf "%a%t" pp_term dom (fun ppf -> pp_print_break ppf sp 0);
          rest ppf ()),
        body )
  | Notn (n, obs) when n = arrow ->
      let rest, body = pp_arrow true obs in
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
        body )

let () =
  add_term_pp pi @@ fun ppf obs ->
  let _sp, pp_doms, body = pp_pi false obs in
  fprintf ppf "@[<b 1>@[<hov 2>%a@]%t%a %a@]" pp_doms ()
    (pp_print_custom_break ~fits:("", 1, "") ~breaks:("", 0, " "))
    pp_tok Arrow pp_term body

let () =
  add_term_pp arrow @@ fun ppf obs ->
  let pp_doms, body = pp_arrow false obs in
  fprintf ppf "@[<b 1>@[<hov 2>%a@]%t%a %a@]" pp_doms ()
    (pp_print_custom_break ~fits:("", 1, "") ~breaks:("", 0, " "))
    pp_tok Arrow pp_term body

(* ********************
   Ascription
 ******************** *)

let asc =
  make ~name:":" ~tightness:Float.neg_infinity ~left:Open ~right:Open ~assoc:Non ~tree:(fun n ->
      eop Colon (Done n))

let () =
  add_compiler asc
    {
      compile =
        (fun ctx obs ->
          let tm, obs = get_term obs in
          let ty, obs = get_term obs in
          let () = get_done obs in
          let tm = compile ctx tm in
          let ty = compile ctx ty in
          Synth (Asc (tm, ty)));
    };
  add_term_pp asc @@ fun ppf obs ->
  let tm, obs = get_term obs in
  let ty, obs = get_term obs in
  let () = get_done obs in
  fprintf ppf "@[<b 0>%a@ %a %a" pp_term tm pp_tok Colon pp_term ty

(* ********************
   The universe
 ******************** *)

let universe =
  make ~name:"Type" ~tightness:Float.nan ~left:Closed ~right:Closed ~assoc:Non ~tree:(fun n ->
      eop (Name "Type") (Done n))

let () =
  add_compiler universe
    {
      compile =
        (fun _ obs ->
          let () = get_done obs in
          Synth UU);
    };
  add_term_pp universe @@ fun ppf obs ->
  let () = get_done obs in
  pp_print_string ppf "Type"

(* ********************
   Degeneracies (refl and sym)
 ******************** *)

let refl =
  make ~name:"refl" ~tightness:Float.nan ~left:Closed ~right:Closed ~assoc:Non ~tree:(fun n ->
      eops [ (Name "refl", Done n); (Name "Id", Done n) ])

let () =
  add_compiler refl
    {
      compile =
        (fun _ obs ->
          let () = get_done obs in
          Synth (Act ("refl", Dim.refl, None)));
    };
  add_term_pp refl @@ fun ppf obs ->
  let () = get_done obs in
  pp_print_string ppf "refl"

let sym =
  make ~name:"sym" ~tightness:Float.nan ~left:Closed ~right:Closed ~assoc:Non ~tree:(fun n ->
      eop (Name "sym") (Done n))

let () =
  add_compiler sym
    {
      compile =
        (fun _ obs ->
          let () = get_done obs in
          Synth (Act ("sym", Dim.sym, None)));
    };
  add_term_pp sym @@ fun ppf obs ->
  let () = get_done obs in
  pp_print_string ppf "sym"

(* ********************
   Anonymous structs and comatches
 ******************** *)

let struc =
  make ~name:"struc" ~tightness:Float.nan ~left:Closed ~right:Closed ~assoc:Non ~tree:(fun n ->
      let rec struc_fields () =
        Inner
          {
            ops = TokMap.singleton RBrace (Done n);
            name =
              Some
                (op Coloneq (terms [ (Op ";", Lazy (lazy (struc_fields ()))); (RBrace, Done n) ]));
            constr = None;
            field = None;
            term = None;
          } in
      let rec comatch_fields () =
        Inner
          {
            ops = TokMap.singleton RBrace (Done n);
            field =
              Some
                (op Mapsto (terms [ (Op ";", Lazy (lazy (comatch_fields ()))); (RBrace, Done n) ]));
            constr = None;
            name = None;
            term = None;
          } in
      eop LBrace
        (Inner
           {
             ops = TokMap.singleton RBrace (Done n);
             name =
               Some
                 (op Coloneq (terms [ (Op ";", Lazy (lazy (struc_fields ()))); (RBrace, Done n) ]));
             field =
               Some
                 (op Mapsto (terms [ (Op ";", Lazy (lazy (comatch_fields ()))); (RBrace, Done n) ]));
             constr = None;
             term = None;
           }))

let rec compile_struc :
    type n. n check list Field.Map.t -> (string option, n) Bwv.t -> observation list -> n check =
 fun flds ctx obs ->
  match get_next obs with
  | `Done -> Raw.Struct flds
  | `Name (Some x, obs) | `Field (x, obs) ->
      let tm, obs = get_term obs in
      let tm = compile ctx tm in
      compile_struc (flds |> Field.Map.add_to_list (Field.intern x) tm) ctx obs
  | `Name (None, _) -> fatal Unnamed_field_in_struct
  | `Constr _ | `Term _ -> fatal (Anomaly "Impossible thing in struct")

let () = add_compiler struc { compile = (fun ctx obs -> compile_struc Field.Map.empty ctx obs) }

type style = Term | Case

let pp_style = function
  | Term -> pp_term
  | Case -> pp_case

let rec pp_fld :
    type a.
    style ->
    formatter ->
    (formatter -> a -> unit) ->
    a ->
    Token.t ->
    parse_tree ->
    observation list ->
    unit =
 fun style ppf pp x tok tm obs ->
  fprintf ppf "@[<hov 2>%a %a@ %a@]%a" pp x pp_tok tok (pp_style style) tm
    (pp_print_option (fun ppf -> fprintf ppf " %a@ " pp_tok))
    (if get_next obs = `Done then None else Some (Op ";"))

and pp_fields style ppf obs =
  match get_next obs with
  | `Done -> ()
  | `Name (Some x, obs) | `Field (x, obs) ->
      let tm, obs = get_term obs in
      (match style with
      | Term -> pp_fld style ppf pp_var (Some x) Coloneq tm obs
      | Case -> pp_fld style ppf pp_field x Mapsto tm obs);
      pp_fields style ppf obs
  | `Name (None, _) -> fatal Unnamed_field_in_struct
  | `Constr _ | `Term _ -> fatal (Anomaly "Impossible thing in struct")

let pp_struc style ppf obs =
  let cpt = compact () in
  (match style with
  | Term ->
      if not cpt then pp_open_box ppf 0;
      pp_open_hvbox ppf 2
  | Case -> pp_open_vbox ppf 2);
  pp_tok ppf LBrace;
  if cpt then pp_print_string ppf " " else pp_print_space ppf ();
  pp_fields style ppf obs;
  (if cpt then pp_print_string ppf " "
   else
     match style with
     | Term ->
         pp_close_box ppf ();
         pp_print_custom_break ~fits:("", 1, "") ~breaks:(" ;", 0, "") ppf
     | Case -> pp_print_custom_break ~fits:("", 1, "") ~breaks:(" ;", -2, "") ppf);
  pp_tok ppf RBrace;
  pp_close_box ppf ()

(* In standard formatting, structures in case trees are written as copattern-matches with field dots and ↦, while those in terms are written without dots and with ≔. *)
let () =
  add_term_pp struc (pp_struc Term);
  add_case_pp struc (pp_struc Case)

(* ********************
   Matches
 ******************** *)

let rec pattern_vars n =
  Inner
    {
      name = Some (Lazy (lazy (pattern_vars n)));
      constr = None;
      field = None;
      term = None;
      ops =
        TokMap.singleton Mapsto (terms [ (Op "|", Lazy (lazy (innermtch n))); (RBracket, Done n) ]);
    }

and innermtch n =
  Inner
    {
      ops = TokMap.of_list [ (RBracket, Done n) ];
      constr = Some (pattern_vars n);
      field = None;
      name = None;
      term = None;
    }

let mtch =
  make ~name:"match" ~tightness:Float.nan ~left:Closed ~right:Closed ~assoc:Non ~tree:(fun n ->
      eop LBracket
        (Inner
           {
             ops = TokMap.of_list [ (Op "|", innermtch n); (RBracket, Done n) ];
             name = Some (op (Op "|") (innermtch n));
             constr = Some (pattern_vars n);
             field = None;
             term = None;
           }))

let rec compile_branch_names :
    type a b ab.
    (a, b, ab) N.plus ->
    (string option, ab) Bwv.t ->
    Constr.t ->
    observation list ->
    a branch * observation list =
 fun ab ctx c obs ->
  match get_next obs with
  | `Name (a, obs) -> compile_branch_names (Suc ab) (Snoc (ctx, a)) c obs
  | `Term (t, obs) ->
      let tm = compile ctx t in
      (Branch (c, ab, tm), obs)
  | `Constr _ | `Field _ -> fatal (Anomaly "Impossible thing in match")
  | `Done -> fatal (Anomaly "Unexpected end of input")

let rec compile_branches : type n. (string option, n) Bwv.t -> observation list -> n branch list =
 fun ctx obs ->
  match get_next obs with
  | `Done -> []
  | `Constr (c, obs) -> compile_branch ctx c obs
  | `Field _ | `Term _ | `Name _ -> fatal (Anomaly "Impossible thing in match")

and compile_branch : type n. (string option, n) Bwv.t -> string -> observation list -> n branch list
    =
 fun ctx c obs ->
  let br, obs = compile_branch_names Zero ctx (Constr.intern c) obs in
  let rest = compile_branches ctx obs in
  br :: rest

let () =
  add_compiler mtch
    {
      compile =
        (fun ctx obs ->
          match get_next obs with
          (* Can't match an underscore *)
          | `Name (None, _) -> fatal Unnamed_variable_in_match
          | `Name (Some name, obs) -> (
              match Bwv.index (Some name) ctx with
              | None -> fatal (Unbound_variable name)
              | Some x ->
                  let branches = compile_branches ctx obs in
                  (* TODO: Allow matching on boundaries of cube variables. *)
                  Match ((x, None), branches))
          | `Constr (c, obs) ->
              let branches = compile_branch (Snoc (ctx, None)) c obs in
              Lam (`Normal, Match ((Top, None), branches))
          | `Done -> Lam (`Normal, Match ((Top, None), []))
          | `Field _ | `Term _ -> fatal (Anomaly "Impossible thing in match"));
    }

let rec branch_vars obs =
  match get_next obs with
  | `Name (x, obs) ->
      let rest, obs = branch_vars obs in
      (x :: rest, obs)
  | _ -> ([], obs)

let rec pp_branches brk ppf obs =
  match get_next obs with
  | `Constr (c, obs) ->
      let vars, obs = branch_vars obs in
      let tm, obs = get_term obs in
      let cpt = compact () in
      if brk || not cpt then pp_print_break ppf 0 2 else pp_print_string ppf " ";
      (match tm with
      | Notn (n, brobs) when n = mtch && cpt ->
          fprintf ppf "@[<hov 0>@[<hov 4>%a %a@ %a%a@] %a@]" pp_tok (Op "|") pp_constr c
            (fun ppf -> List.iter (fun x -> fprintf ppf "%a@ " pp_var x))
            vars pp_tok Mapsto (pp_match false) brobs
      | _ ->
          fprintf ppf "@[<b 1>@[<hov 4>%a %a@ %a%a@]%t%a@]" pp_tok (Op "|") pp_constr c
            (fun ppf -> List.iter (fun x -> fprintf ppf "%a@ " pp_var x))
            vars pp_tok Mapsto
            (pp_print_custom_break ~fits:("", 1, "") ~breaks:("", 0, " "))
            pp_case tm);
      pp_branches true ppf obs
  | `Done -> ()
  | _ -> fatal (Anomaly "Impossible thing in match")

and pp_match box ppf obs =
  match get_next obs with
  | `Name (name, obs) ->
      if box then pp_open_vbox ppf 0;
      pp_tok ppf LBracket;
      pp_print_string ppf " ";
      pp_var ppf name;
      pp_branches true ppf obs;
      if compact () then pp_print_string ppf " " else pp_print_cut ppf ();
      pp_tok ppf RBracket;
      if box then pp_close_box ppf ()
  | _ ->
      let cpt = compact () in
      if box || not cpt then pp_open_vbox ppf 0;
      pp_tok ppf LBracket;
      pp_branches ((not box) || not cpt) ppf obs;
      if cpt then pp_print_string ppf " " else pp_print_cut ppf ();
      pp_tok ppf RBracket;
      if box || not cpt then pp_close_box ppf ()

(* Matches are only valid in case trees. *)
let () = add_case_pp mtch (pp_match true)

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
