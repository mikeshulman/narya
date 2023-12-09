open Util
open Postprocess
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
  set_processor parens
    {
      process =
        (fun ctx obs ->
          match obs with
          | [ Term body ] -> process ctx body
          | _ -> fatal (Anomaly "invalid notation arguments for parens"));
    };
  set_print parens (fun ppf obs ->
      match obs with
      | [ body ] -> fprintf ppf "@[<hov 1>%a%a%a@]" pp_tok LParen pp_term body pp_tok RParen
      | _ -> fatal (Anomaly "invalid notation arguments for parens"));
  set_print_as_case parens (fun ppf obs ->
      match obs with
      (* Parentheses should never be required in a case tree, so we omit them during reformatting. *)
      | [ body ] -> pp_term ppf body
      | _ -> fatal (Anomaly "invalid notation arguments for parens"))

(* ********************
   Let-binding
 ******************** *)

(* Let-in doesn't need to be right-associative in order to chain, because it is left-closed, but we make it right-associative anyway for consistency.  *)

let letin = make "let" (Prefixr No.minus_omega)

let () =
  set_tree letin
    (Closed_entry
       (eop Let
          (terms
             [
               (Coloneq, term In (Done_closed letin));
               (Colon, term Coloneq (term In (Done_closed letin)));
             ])));
  set_processor letin
    {
      process =
        (fun ctx obs ->
          match obs with
          | [ Term x; Term ty; Term tm; Term body ] -> (
              let x = get_var x in
              let ty, tm = (process ctx ty, process ctx tm) in
              match process (Snoc (ctx, x)) body with
              | Synth body -> Synth (Let (Asc (tm, ty), body))
              | _ -> fatal (Nonsynthesizing "body of let"))
          | [ Term x; Term tm; Term body ] -> (
              let x = get_var x in
              match process ctx tm with
              | Synth term -> (
                  match process (Snoc (ctx, x)) body with
                  | Synth body -> Synth (Let (term, body))
                  | _ -> fatal (Nonsynthesizing "body of let"))
              | _ -> fatal (Nonsynthesizing "value of let"))
          | _ -> fatal (Anomaly "invalid notation arguments for let"));
    };
  set_print letin (fun ppf obs ->
      let rec pp_let : formatter -> observation list -> unit =
       fun ppf obs ->
        match obs with
        | [ x; ty; tm; body ] ->
            fprintf ppf
              (match style () with
              | Compact -> "@[<hov 2>@[<hv 2>%a %a@ %a %a@ %a %a@]@ %a@]@ %a"
              | Noncompact -> "@[<hv 2>%a %a@ %a %a@ %a %a@ %a@]@ %a")
              pp_tok Let pp_term x pp_tok Colon pp_term ty pp_tok Coloneq pp_term tm pp_tok In
              pp_let_body body
        | [ x; tm; body ] ->
            fprintf ppf
              (match style () with
              | Compact -> "@[<hov 2>%a %a %a@ %a@ %a@]@ %a"
              | Noncompact -> "@[<hv 2>%a %a %a@ %a@ %a@]@ %a")
              pp_tok Let pp_term x pp_tok Coloneq pp_term tm pp_tok In pp_let_body body
        | _ -> fatal (Anomaly "invalid notation arguments for let")
      and pp_let_body ppf tr =
        match tr with
        | Term (Notn n) when equal (notn n) letin -> pp_let ppf (args n)
        | _ -> pp_term ppf tr in
      fprintf ppf "@[<hv 0>%a@]" pp_let obs)

(* ********************
   Ascription
 ******************** *)

let asc = make "ascription" (Infix No.minus_omega)
let () = set_tree asc (Open_entry (eop Colon (done_open asc)))

let () =
  set_processor asc
    {
      process =
        (fun ctx obs ->
          match obs with
          | [ Term tm; Term ty ] ->
              let tm = process ctx tm in
              let ty = process ctx ty in
              Synth (Asc (tm, ty))
          | _ -> fatal (Anomaly "invalid notation arguments for ascription"));
    };
  set_print asc @@ fun ppf obs ->
  match obs with
  | [ tm; ty ] -> fprintf ppf "@[<b 0>%a@ %a %a" pp_term tm pp_tok Colon pp_term ty
  | _ -> fatal (Anomaly "invalid notation arguments for ascription")

(* ****************************************
   Function types (dependent and non)
 **************************************** *)

let arrow = make "arrow" (Infixr No.zero)

exception Not_a_pi_arg

(* Inspect 'xs', expecting it to be a spine of valid bindable local variables or underscores, and produce a list of those variables, consing it onto the accumulator argument. *)
let rec get_pi_vars :
    type lt ls rt rs. (lt, ls, rt, rs) parse -> string option list -> string option list =
 fun xs vars ->
  match xs with
  | Ident x -> if Token.variableable x then Some x :: vars else fatal (Invalid_variable x)
  | Placeholder -> None :: vars
  | App { fn; arg = Ident x; _ } ->
      (* There's a choice here: an invalid variable name could still be a valid term, so we could allow for instance (x.y : A) → B to be parsed as a non-dependent function type.  But that seems a recipe for confusion. *)
      if Token.variableable x then get_pi_vars fn (Some x :: vars) else fatal (Invalid_variable x)
  | _ -> raise Not_a_pi_arg

(* Inspect 'arg', expecting it to be of the form 'x y z : A', and return the list of variables and the type. *)
let get_pi_arg : type lt ls rt rs. (lt, ls, rt, rs) parse -> string option list * observation =
 fun arg ->
  match arg with
  | Notn n when equal (notn n) asc -> (
      match args n with
      | [ Term xs; dom ] -> (get_pi_vars xs [], dom)
      | _ -> fatal (Anomaly "invalid notation arguments for arrow"))
  | _ -> raise Not_a_pi_arg

(* Inspect 'doms', expecting it to be of the form (x:A)(y:B) etc, and produce a list of variables with types, prepending that list onto the front of the given accumulation list.  If it isn't of that form, interpret it as the single domain type of a non-dependent function-type and cons it onto the list. *)
let rec get_pi_args :
    type lt ls rt rs.
    (lt, ls, rt, rs) parse ->
    (string option list option * observation) list ->
    (string option list option * observation) list =
 fun doms vars ->
  try
    match doms with
    | Notn n when equal (notn n) parens -> (
        match args n with
        | [ Term body ] ->
            let xs, tys = get_pi_arg body in
            (Some xs, tys) :: vars
        | _ -> fatal (Anomaly "invalid notation arguments for arrow"))
    | App { fn; arg = Notn n; _ } when equal (notn n) parens -> (
        match args n with
        | [ Term body ] ->
            let xs, tys = get_pi_arg body in
            get_pi_args fn ((Some xs, tys) :: vars)
        | _ -> fatal (Anomaly "invalid notation arguments for arrow"))
    | _ -> raise Not_a_pi_arg
  with Not_a_pi_arg -> (None, Term doms) :: vars

(* Get all the domains and eventual codomain from a right-associated iterated function-type. *)
let rec get_pi :
    type lt ls rt rs.
    observation list -> (string option list option * observation) list * observation = function
  | [ Term dom; Term cod ] ->
      let doms, cod =
        match cod with
        | Notn n when equal (notn n) arrow -> get_pi (args n)
        | _ -> ([], Term cod) in
      (get_pi_args dom doms, cod)
  | _ -> fatal (Anomaly "invalid notation arguments for arrow")

(* Given the variables with domains and the codomain of a pi-type, process it into a raw term. *)
let rec process_pi :
    type n lt ls rt rs.
    (string option, n) Bwv.t ->
    (string option list option * observation) list ->
    (lt, ls, rt, rs) parse ->
    n check =
 fun ctx doms cod ->
  match doms with
  | [] -> process ctx cod
  | (Some [], _) :: doms -> process_pi ctx doms cod
  | (None, dom) :: doms -> process_pi ctx ((Some (None :: []), dom) :: doms) cod
  | (Some (x :: xs), Term dom) :: doms ->
      let cdom = process ctx dom in
      let ctx = Bwv.Snoc (ctx, x) in
      let cod = process_pi ctx ((Some xs, Term dom) :: doms) cod in
      Synth (Pi (x, cdom, cod))

let () =
  set_tree arrow (Open_entry (eop Arrow (done_open arrow)));
  set_processor arrow
    {
      process =
        (fun ctx obs ->
          let doms, Term cod = get_pi obs in
          process_pi ctx doms cod);
    }

(* Pretty-print the domains of a right-associated iterated function-type *)
let rec pp_doms :
    [ `Start | `Dep | `Nondep ] ->
    formatter ->
    (string option list option * observation) list ->
    unit =
 fun prev ppf doms ->
  match doms with
  | [] -> ()
  | (vars, dom) :: doms -> (
      match vars with
      | None ->
          if prev = `Dep || prev = `Nondep then fprintf ppf "@ %a " pp_tok Arrow;
          fprintf ppf "%a" pp_term dom;
          pp_doms `Nondep ppf doms
      | Some xs ->
          if prev = `Nondep then fprintf ppf "@ %a " pp_tok Arrow;
          if prev = `Dep then pp_print_space ppf ();
          fprintf ppf "%a%a %a %a%a" pp_tok LParen
            (pp_print_list ~pp_sep:pp_print_space pp_var)
            xs pp_tok Colon pp_term dom pp_tok RParen;
          pp_doms `Dep ppf doms)

let () =
  set_print arrow @@ fun ppf obs ->
  let doms, cod = get_pi obs in
  fprintf ppf "@[<b 1>@[<hov 2>%a@]%t%a %a@]" (pp_doms `Start) doms
    (pp_print_custom_break ~fits:("", 1, "") ~breaks:("", 0, " "))
    pp_tok Arrow pp_term cod

(* ********************
   Abstraction
 ******************** *)

(* Abstractions are encoded as a right-associative infix operator that inspects its left-hand argument deeply before compiling it, expecting it to look like an application spine of variables, and then instead binds those variables in its right-hand argument. *)

let abs = make "abstraction" (Infixr No.minus_omega)
let () = set_tree abs (Open_entry (eop Mapsto (done_open abs)))
let cubeabs = make "cube_abstraction" (Infixr No.minus_omega)
let () = set_tree cubeabs (Open_entry (eop DblMapsto (done_open cubeabs)))

type _ extended_ctx =
  | Extctx : ('n, 'm, 'nm) N.plus * (string option, 'nm) Bwv.t -> 'n extended_ctx

let rec get_vars :
    type n lt1 ls1 rt1 rs1. (string option, n) Bwv.t -> (lt1, ls1, rt1, rs1) parse -> n extended_ctx
    =
 fun ctx vars ->
  match vars with
  | Ident x ->
      if Token.variableable x then Extctx (Suc Zero, Snoc (ctx, Some x))
        (* TODO: Can we report the range for errors produced here? *)
      else fatal (Invalid_variable x)
  | Placeholder -> Extctx (Suc Zero, Snoc (ctx, None))
  | App { fn; arg = Ident x; _ } ->
      if Token.variableable x then
        let (Extctx (ab, ctx)) = get_vars ctx fn in
        Extctx (Suc ab, Snoc (ctx, Some x))
      else fatal (Invalid_variable x)
  | App { fn; arg = Placeholder; _ } ->
      let (Extctx (ab, ctx)) = get_vars ctx fn in
      Extctx (Suc ab, Snoc (ctx, None))
  | _ -> fatal Parse_error

let process_abs cube =
  {
    process =
      (fun ctx obs ->
        match obs with
        | [ Term vars; Term body ] ->
            let (Extctx (ab, ctx)) = get_vars ctx vars in
            raw_lam ctx cube ab (process ctx body)
        | _ -> fatal (Anomaly "invalid notation arguments for abstraction"));
  }

let pp_abs cube ppf obs =
  match obs with
  | [ vars; body ] ->
      fprintf ppf "@[<b 0>@[<hov 2>%a %a@]@ %a@]" pp_term vars pp_tok
        (match cube with
        | `Normal -> Mapsto
        | `Cube -> DblMapsto)
        pp_term body
  | _ -> fatal (Anomaly "invalid notation arguments for abstraction")

let () =
  set_processor abs (process_abs `Normal);
  set_processor cubeabs (process_abs `Cube);
  set_print abs (pp_abs `Normal);
  set_print cubeabs (pp_abs `Cube);
  set_print_as_case abs (pp_abs `Normal);
  set_print_as_case cubeabs (pp_abs `Cube)

(* ********************
   The universe
 ******************** *)

let universe = make "Type" Outfix

let () =
  set_tree universe (Closed_entry (eop (Ident "Type") (Done_closed universe)));
  set_processor universe
    {
      process =
        (fun _ obs ->
          match obs with
          | [] -> Synth UU
          | _ -> fatal (Anomaly "invalid notation arguments for Type"));
    };
  set_print universe @@ fun ppf obs ->
  match obs with
  | [] -> pp_print_string ppf "Type"
  | _ -> fatal (Anomaly "invalid notation arguments for Type")

(* ********************
   Degeneracies (refl and sym)
 ******************** *)

let refl = make "refl" Outfix

let () =
  set_tree refl
    (Closed_entry (eops [ (Ident "refl", Done_closed refl); (Ident "Id", Done_closed refl) ]));
  set_processor refl
    {
      process =
        (fun _ obs ->
          match obs with
          | [] -> Synth (Act ("refl", Dim.refl, None))
          | _ -> fatal (Anomaly "invalid notation arguments for refl"));
    };
  set_print refl @@ fun ppf obs ->
  match obs with
  | [] -> pp_print_string ppf "refl"
  | _ -> fatal (Anomaly "invalid notation arguments for refl")

let sym = make "sym" Outfix

let () =
  set_tree sym (Closed_entry (eop (Ident "sym") (Done_closed sym)));
  set_processor sym
    {
      process =
        (fun _ obs ->
          match obs with
          | [] -> Synth (Act ("sym", Dim.sym, None))
          | _ -> fatal (Anomaly "invalid notation arguments for sym"));
    };
  set_print sym @@ fun ppf obs ->
  match obs with
  | [] -> pp_print_string ppf "sym"
  | _ -> fatal (Anomaly "invalid notation arguments for sym")

(* ********************
   Anonymous structs and comatches
 ******************** *)

let struc = make "struc" Outfix

let rec struc_fields () =
  Inner
    {
      empty_branch with
      ops = TokMap.singleton RBrace (Done_closed struc);
      term =
        Some
          (TokMap.singleton Coloneq
             (terms [ (Op ";", Lazy (lazy (struc_fields ()))); (RBrace, Done_closed struc) ]));
    }

let rec comatch_fields () =
  Inner
    {
      empty_branch with
      ops = TokMap.singleton RBrace (Done_closed struc);
      field =
        Some
          (op Mapsto
             (terms [ (Op ";", Lazy (lazy (comatch_fields ()))); (RBrace, Done_closed struc) ]));
    }

let () =
  set_tree struc
    (Closed_entry
       (eop LBrace
          (Inner
             {
               ops = TokMap.singleton RBrace (Done_closed struc);
               term =
                 Some
                   (TokMap.singleton Coloneq
                      (terms
                         [ (Op ";", Lazy (lazy (struc_fields ()))); (RBrace, Done_closed struc) ]));
               field =
                 Some
                   (op Mapsto
                      (terms
                         [ (Op ";", Lazy (lazy (comatch_fields ()))); (RBrace, Done_closed struc) ]));
             })))

let rec process_struc :
    type n. n check list Field.Map.t -> (string option, n) Bwv.t -> observation list -> n check =
 fun flds ctx obs ->
  match obs with
  | [] -> Raw.Struct flds
  | Term (Ident x) :: obs | Term (Field x) :: obs -> (
      match obs with
      | Term tm :: obs ->
          let tm = process ctx tm in
          process_struc (flds |> Field.Map.add_to_list (Field.intern x) tm) ctx obs
      | _ -> fatal (Anomaly "invalid notation arguments for struct"))
  | Term Placeholder :: _ -> fatal Unnamed_field_in_struct
  | _ -> fatal (Anomaly "invalid notation arguments for struct")

let () = set_processor struc { process = (fun ctx obs -> process_struc Field.Map.empty ctx obs) }

let rec pp_fld :
    type a.
    formatter -> (formatter -> a -> unit) -> a -> Token.t -> observation -> observation list -> unit
    =
 fun ppf pp x tok tm obs ->
  fprintf ppf "@[<hov 2>%a %a@ %a@]%a" pp x pp_tok tok pp_term tm
    (pp_print_option (fun ppf -> fprintf ppf " %a@ " pp_tok))
    (if obs = [] then None else Some (Op ";"))

and pp_fields : formatter -> observation list -> unit =
 fun ppf obs ->
  match obs with
  | [] -> ()
  | Term (Ident x) :: obs | Term (Field x) :: obs -> (
      match obs with
      | tm :: obs ->
          (match state () with
          | Term -> pp_fld ppf pp_var (Some x) Coloneq tm obs
          | Case -> pp_fld ppf pp_field x Mapsto tm obs);
          pp_fields ppf obs
      | _ -> fatal (Anomaly "invalid notation arguments for struct"))
  | Term Placeholder :: _ -> fatal Unnamed_field_in_struct
  | _ -> fatal (Anomaly "invalid notation arguments for struct")

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

let rec innermtch () =
  Inner
    {
      empty_branch with
      ops = TokMap.of_list [ (RBracket, Done_closed mtch) ];
      term =
        Some
          (TokMap.singleton Mapsto
             (terms [ (Op "|", Lazy (lazy (innermtch ()))); (RBracket, Done_closed mtch) ]));
    }

let () =
  set_tree mtch
    (Closed_entry
       (eop LBracket
          (Inner
             {
               empty_branch with
               ops = TokMap.of_list [ (Op "|", innermtch ()); (RBracket, Done_closed mtch) ];
               term =
                 Some
                   (TokMap.of_list
                      [
                        (Op "|", innermtch ());
                        (RBracket, Done_closed mtch);
                        ( Mapsto,
                          terms
                            [ (Op "|", Lazy (lazy (innermtch ()))); (RBracket, Done_closed mtch) ]
                        );
                      ]);
             })))

let rec get_pattern :
    type n lt1 ls1 rt1 rs1.
    (string option, n) Bwv.t -> (lt1, ls1, rt1, rs1) parse -> Constr.t * n extended_ctx =
 fun ctx pat ->
  match pat with
  | Constr c -> (Constr.intern c, Extctx (Zero, ctx))
  | App { fn; arg = Ident x; _ } ->
      if Token.variableable x then
        let c, Extctx (ab, ctx) = get_pattern ctx fn in
        (c, Extctx (Suc ab, Snoc (ctx, Some x)))
      else fatal (Invalid_variable x)
  | App { fn; arg = Placeholder; _ } ->
      let c, Extctx (ab, ctx) = get_pattern ctx fn in
      (c, Extctx (Suc ab, Snoc (ctx, None)))
  | _ -> fatal Parse_error

let rec process_branches : type n. (string option, n) Bwv.t -> observation list -> n Raw.branch list
    =
 fun ctx obs ->
  match obs with
  | [] -> []
  | Term pat :: Term body :: obs ->
      let c, Extctx (ab, ectx) = get_pattern ctx pat in
      Branch (c, ab, process ectx body) :: process_branches ctx obs
  | _ -> fatal (Anomaly "invalid notation arguments for match")

let () =
  set_processor mtch
    {
      process =
        (fun ctx obs ->
          match obs with
          (* If the first thing is an ident, then it's the match variable. *)
          | Term (Ident ident) :: obs -> (
              match Bwv.index (Some ident) ctx with
              | None -> fatal (Unbound_variable ident)
              | Some x -> Match ((x, None), process_branches ctx obs))
          (* If the first thing is a field of an ident, it must mean a face of a cube variable. *)
          | Term (App { fn = Ident ident; arg = Field fld; _ }) :: obs -> (
              match (Bwv.index (Some ident) ctx, Dim.sface_of_string fld) with
              | Some x, Some fa -> Match ((x, Some fa), process_branches ctx obs)
              | None, _ -> fatal (Unbound_variable ident)
              | _ -> fatal Parse_error)
          (* Otherwise, it's a matching lambda. *)
          | _ ->
              let branches = process_branches (Snoc (ctx, None)) obs in
              Lam (None, `Normal, Match ((Top, None), branches)));
    }

let rec pp_branches : bool -> formatter -> observation list -> unit =
 fun brk ppf obs ->
  match obs with
  | pat :: body :: obs ->
      let style = style () in
      if brk || style = Noncompact then pp_print_break ppf 0 2 else pp_print_string ppf " ";
      (match body with
      | Term (Notn n) when equal (notn n) mtch && style = Compact ->
          fprintf ppf "@[<hov 0>@[<hov 4>%a %a@ %a@] %a@]" pp_tok (Op "|") pp_term pat pp_tok Mapsto
            (pp_match false) (args n)
      | _ ->
          fprintf ppf "@[<b 1>@[<hov 4>%a %a@ %a@]%t%a@]" pp_tok (Op "|") pp_term pat pp_tok Mapsto
            (pp_print_custom_break ~fits:("", 1, "") ~breaks:("", 0, " "))
            pp_term body);
      pp_branches true ppf obs
  | [] -> ()
  | _ -> fatal (Anomaly "invalid notation arguments for match")

and pp_match box ppf obs =
  match obs with
  | (Term (Ident _) as x) :: obs ->
      if box then pp_open_vbox ppf 0;
      pp_tok ppf LBracket;
      pp_print_string ppf " ";
      pp_term ppf x;
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
    |> State.add asc
    |> State.add abs
    |> State.add cubeabs
    |> State.add arrow
    |> State.add universe
    |> State.add refl
    |> State.add sym
    |> State.add struc
    |> State.add mtch)
