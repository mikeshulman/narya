open Util
open Dim
open Postprocess
open Print
open Format
open Core
open Syntax
open Raw
open Reporter
open Notation
open Monad.Ops (Monad.Maybe)
open Printconfig

type 'a located = 'a Asai.Range.located

(* ********************
   Parentheses
 ******************** *)

let parens = make "parens" Outfix

let () =
  set_tree parens (Closed_entry (eop LParen (term RParen (Done_closed parens))));
  set_processor parens
    {
      process =
        (fun ctx obs _loc _ ->
          (* The location of the parentheses can be ignored. *)
          match obs with
          | [ Term body ] -> process ctx body
          | _ -> fatal (Anomaly "invalid notation arguments for parens"));
    }

let pp_parens space ppf obs ws =
  match obs with
  | [ body ] ->
      let wslparen, ws = take ws in
      let wsrparen, _ = take ws in
      pp_open_hovbox ppf 1;
      if true then (
        pp_tok ppf LParen;
        pp_ws `None ppf wslparen;
        pp_term `None ppf body;
        pp_tok ppf RParen);
      pp_close_box ppf ();
      pp_ws space ppf wsrparen
  | _ -> fatal (Anomaly "invalid notation arguments for parens")

let () =
  set_print parens pp_parens;
  set_print_as_case parens pp_parens

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
        (fun ctx obs loc _ ->
          match obs with
          | [ Term x; Term ty; Term tm; Term body ] -> (
              let x = get_var x.value in
              let ty, tm = (process ctx ty, process ctx tm) in
              match process (Snoc (ctx, x)) body with
              | { value = Synth body; loc = body_loc } ->
                  {
                    value =
                      Synth
                        (Let
                           ( x,
                             { value = Asc (tm, ty); loc = Range.merge_opt ty.loc tm.loc },
                             { value = body; loc = body_loc } ));
                    loc;
                  }
              | _ -> fatal (Nonsynthesizing "body of let"))
          | [ Term x; Term tm; Term body ] -> (
              let x = get_var x.value in
              match process ctx tm with
              | { value = Synth term; loc = term_loc } -> (
                  match process (Snoc (ctx, x)) body with
                  | { value = Synth body; loc = body_loc } ->
                      {
                        value =
                          Synth
                            (Let
                               ( x,
                                 { value = term; loc = term_loc },
                                 { value = body; loc = body_loc } ));
                        loc;
                      }
                  | _ -> fatal (Nonsynthesizing "body of let"))
              | _ -> fatal (Nonsynthesizing "value of let"))
          | _ -> fatal (Anomaly "invalid notation arguments for let"));
    };
  set_print letin (fun space ppf obs ws ->
      let rec pp_let space ppf obs ws =
        let style = style () in
        match obs with
        | [ x; ty; tm; body ] ->
            let wslet, ws = take ws in
            let wscolon, ws = take ws in
            let wscoloneq, ws = take ws in
            let wsin, _ = take ws in
            if style = `Compact then pp_open_hovbox ppf 2;
            if true then (
              pp_open_hvbox ppf 2;
              if true then (
                pp_tok ppf Let;
                pp_ws `Nobreak ppf wslet;
                pp_term `Break ppf x;
                pp_tok ppf Colon;
                pp_ws `Nobreak ppf wscolon;
                pp_term `Break ppf ty;
                pp_tok ppf Coloneq;
                pp_ws `Nobreak ppf wscoloneq;
                pp_term (if style = `Compact then `Nobreak else `Break) ppf tm);
              if style = `Compact then pp_close_box ppf ();
              pp_tok ppf In);
            pp_close_box ppf ();
            pp_ws `Break ppf wsin;
            pp_let_body space ppf body
        | [ x; tm; body ] ->
            let wslet, ws = take ws in
            let wscoloneq, ws = take ws in
            let wsin, _ = take ws in
            if style = `Compact then pp_open_hovbox ppf 2 else pp_open_hvbox ppf 2;
            if true then (
              pp_tok ppf Let;
              pp_ws `Nobreak ppf wslet;
              pp_term `Break ppf x;
              pp_tok ppf Coloneq;
              pp_ws `Nobreak ppf wscoloneq;
              pp_term (if style = `Compact then `Nobreak else `Break) ppf tm;
              pp_tok ppf In);
            pp_close_box ppf ();
            pp_ws `Break ppf wsin;
            pp_let_body space ppf body
        | _ -> fatal (Anomaly "invalid notation arguments for let")
      and pp_let_body space ppf tr =
        match tr with
        | Term { value = Notn n; _ } when equal (notn n) letin ->
            pp_let space ppf (args n) (whitespace n)
        | _ -> pp_term space ppf tr in
      pp_open_hvbox ppf 0;
      pp_let space ppf obs ws;
      pp_close_box ppf ())

(* ********************
   Ascription
 ******************** *)

let asc = make "ascription" (Infix No.minus_omega)
let () = set_tree asc (Open_entry (eop Colon (done_open asc)))

let () =
  set_processor asc
    {
      process =
        (fun ctx obs loc _ ->
          match obs with
          | [ Term tm; Term ty ] ->
              let tm = process ctx tm in
              let ty = process ctx ty in
              { value = Synth (Asc (tm, ty)); loc }
          | _ -> fatal (Anomaly "invalid notation arguments for ascription"));
    };
  set_print asc @@ fun space ppf obs ws ->
  match obs with
  | [ tm; ty ] ->
      let ws, _ = take ws in
      pp_open_box ppf 0;
      if true then (
        pp_term `Break ppf tm;
        pp_tok ppf Colon;
        pp_ws `Nobreak ppf ws;
        pp_term space ppf ty);
      pp_close_box ppf ()
  | _ -> fatal (Anomaly "invalid notation arguments for ascription")

(* ****************************************
   Function types (dependent and non)
 **************************************** *)

let arrow = make "arrow" (Infixr No.zero)

exception Not_a_pi_arg

type arrow_opt = [ `Arrow of Whitespace.t list | `Noarrow | `First ]

type pi_dom =
  | Dep of {
      wsarrow : arrow_opt;
      vars : (string option * Whitespace.t list) list;
      ty : observation;
      wslparen : Whitespace.t list;
      wscolon : Whitespace.t list;
      wsrparen : Whitespace.t list;
    }
  | Nondep of { wsarrow : arrow_opt; ty : observation }

(* Inspect 'xs', expecting it to be a spine of valid bindable local variables or underscores, and produce a list of those variables, consing it onto the accumulator argument 'vars'. *)
let rec get_pi_vars :
    type lt ls rt rs.
    (lt, ls, rt, rs) parse ->
    (string option * Whitespace.t list) list ->
    (string option * Whitespace.t list) list =
 fun xs vars ->
  match xs with
  | Ident ([ x ], w) -> (Some x, w) :: vars
  | Placeholder w -> (None, w) :: vars
  | App { fn; arg = { value = Ident ([ x ], w); _ }; _ } ->
      get_pi_vars fn.value ((Some x, w) :: vars)
  | App { fn; arg = { value = Placeholder w; _ }; _ } -> get_pi_vars fn.value ((None, w) :: vars)
  (* There's a choice here: an invalid variable name could still be a valid term, so we could allow for instance (x.y : A) → B to be parsed as a non-dependent function type.  But that seems a recipe for confusion. *)
  | Ident (xs, _) -> fatal (Invalid_variable xs)
  | App { arg = { value = Ident (xs, _); _ }; _ } -> fatal (Invalid_variable xs)
  | _ -> raise Not_a_pi_arg

(* Inspect 'arg', expecting it to be of the form 'x y z : A', and return the list of variables and the type. *)
let get_pi_arg :
    type lt ls rt rs.
    wsarrow:arrow_opt ->
    (lt, ls, rt, rs) parse ->
    wslparen:Whitespace.t list ->
    wsrparen:Whitespace.t list ->
    pi_dom =
 fun ~wsarrow arg ~wslparen ~wsrparen ->
  match arg with
  | Notn n when equal (notn n) asc -> (
      match args n with
      | [ Term xs; dom ] ->
          let wscolon, _ = take (whitespace n) in
          let vars = get_pi_vars xs.value [] in
          Dep { wsarrow; vars; ty = dom; wslparen; wscolon; wsrparen }
      | _ -> fatal (Anomaly "invalid notation arguments for arrow"))
  | _ -> raise Not_a_pi_arg

(* Inspect 'doms', expecting it to be of the form (x:A)(y:B) etc, and produce a list of variables with types, prepending that list onto the front of the given accumulation list, with the first one having an arrow attached (before it front) if 'wsarrow' is given.  If it isn't of that form, interpret it as the single domain type of a non-dependent function-type and cons it onto the list. *)
let rec get_pi_args :
    type lt ls rt rs. arrow_opt -> (lt, ls, rt, rs) parse located -> pi_dom list -> pi_dom list =
 fun wsarrow doms vars ->
  try
    match doms.value with
    | Notn n when equal (notn n) parens -> (
        match args n with
        | [ Term body ] ->
            let wslparen, ws = take (whitespace n) in
            let wsrparen, _ = take ws in
            get_pi_arg ~wsarrow body.value ~wslparen ~wsrparen :: vars
        | _ -> fatal (Anomaly "invalid notation arguments for arrow"))
    | App { fn; arg = { value = Notn n; _ }; _ } when equal (notn n) parens -> (
        match args n with
        | [ Term body ] ->
            let wslparen, ws = take (whitespace n) in
            let wsrparen, _ = take ws in
            get_pi_args wsarrow fn
              (get_pi_arg ~wsarrow:`Noarrow body.value ~wslparen ~wsrparen :: vars)
        | _ -> fatal (Anomaly "invalid notation arguments for arrow"))
    | _ -> raise Not_a_pi_arg
  with Not_a_pi_arg -> Nondep { wsarrow; ty = Term doms } :: vars

(* Get all the domains and eventual codomain from a right-associated iterated function-type. *)
let rec get_pi :
    type lt ls rt rs.
    arrow_opt ->
    observation list ->
    Whitespace.t list list ->
    pi_dom list * Whitespace.t list * observation =
 fun prev_arr obs ws ->
  match obs with
  | [ Term doms; Term cod ] ->
      let wsarrow, _ = take ws in
      let vars, ws, cod =
        match cod.value with
        | Notn n when equal (notn n) arrow -> get_pi (`Arrow wsarrow) (args n) (whitespace n)
        | _ -> ([], wsarrow, Term cod) in
      (get_pi_args prev_arr doms vars, ws, cod)
  | _ -> fatal (Anomaly "invalid notation arguments for arrow")

(* Given the variables with domains and the codomain of a pi-type, process it into a raw term. *)
let rec process_pi :
    type n lt ls rt rs.
    (string option, n) Bwv.t -> pi_dom list -> (lt, ls, rt, rs) parse located -> n check located =
 fun ctx doms cod ->
  match doms with
  | [] -> process ctx cod
  | Nondep { ty = Term dom; _ } :: doms ->
      let cdom = process ctx dom in
      let ctx = Bwv.Snoc (ctx, None) in
      let cod = process_pi ctx doms cod in
      let loc = Range.merge_opt cdom.loc cod.loc in
      { value = Synth (Pi (None, cdom, cod)); loc }
  | Dep ({ vars = (x, _) :: xs; ty = Term dom; _ } as data) :: doms ->
      let cdom = process ctx dom in
      let ctx = Bwv.Snoc (ctx, x) in
      let cod = process_pi ctx (Dep { data with vars = xs } :: doms) cod in
      let loc = Range.merge_opt cdom.loc cod.loc in
      { value = Synth (Pi (x, cdom, cod)); loc }
  | Dep { vars = []; _ } :: doms -> process_pi ctx doms cod

let () =
  set_tree arrow (Open_entry (eop Arrow (done_open arrow)));
  set_processor arrow
    {
      process =
        (fun ctx obs _loc ws ->
          (* We don't need the loc parameter here, since we can reconstruct the location of each pi-type from its arguments. *)
          let doms, _, Term cod = get_pi `First obs ws in
          process_pi ctx doms cod);
    }

(* Pretty-print the domains of a right-associated iterated function-type *)
let rec pp_doms : formatter -> pi_dom list -> unit =
 fun ppf doms ->
  match doms with
  | [] -> ()
  | Dep { wsarrow; vars; ty; wslparen; wscolon; wsrparen } :: doms ->
      (match wsarrow with
      | `Arrow _ | `Noarrow -> pp_print_space ppf ()
      | `First -> ());
      pp_open_hbox ppf ();
      if true then (
        (match wsarrow with
        | `Arrow wsarrow ->
            pp_tok ppf Arrow;
            pp_ws `Nobreak ppf wsarrow
        | `Noarrow | `First -> ());
        pp_open_hovbox ppf 1;
        if true then (
          pp_tok ppf LParen;
          pp_ws `None ppf wslparen;
          List.iter
            (fun (x, w) ->
              pp_var ppf x;
              pp_ws `Break ppf w)
            vars;
          pp_tok ppf Colon;
          pp_ws `Nobreak ppf wscolon;
          pp_term `None ppf ty;
          pp_tok ppf RParen);
        pp_close_box ppf ());
      pp_close_box ppf ();
      pp_ws `None ppf wsrparen;
      pp_doms ppf doms
  | Nondep { wsarrow; ty } :: doms ->
      (match wsarrow with
      | `Arrow wsarrow ->
          pp_print_space ppf ();
          pp_tok ppf Arrow;
          pp_ws `Nobreak ppf wsarrow
      | `Noarrow -> pp_print_space ppf ()
      | `First -> ());
      pp_term `None ppf ty;
      pp_doms ppf doms

let () =
  set_print arrow @@ fun space ppf obs ws ->
  let doms, wsarrow, cod = get_pi `First obs ws in
  pp_open_box ppf 1;
  if true then (
    (*  *)
    pp_open_hovbox ppf 2;
    pp_doms ppf doms;
    pp_close_box ppf ();
    (*  *)
    pp_print_custom_break ppf ~fits:("", 1, "") ~breaks:("", 0, " ");
    pp_tok ppf Arrow;
    pp_ws `Nobreak ppf wsarrow;
    pp_term space ppf cod);
  pp_close_box ppf ()

(* ********************
   Abstraction
 ******************** *)

(* Abstractions are encoded as a right-associative infix operator that inspects its left-hand argument deeply before compiling it, expecting it to look like an application spine of variables, and then instead binds those variables in its right-hand argument. *)

let abs = make "abstraction" (Infixr No.minus_omega)
let () = set_tree abs (Open_entry (eop Mapsto (done_open abs)))
let cubeabs = make "cube_abstraction" (Infixr No.minus_omega)
let () = set_tree cubeabs (Open_entry (eop DblMapsto (done_open cubeabs)))

type _ extended_ctx =
  | Extctx :
      ('n, 'm, 'nm) N.plus * (Asai.Range.t option, 'm) Bwv.t * (string option, 'nm) Bwv.t
      -> 'n extended_ctx

let rec get_vars :
    type n lt1 ls1 rt1 rs1.
    (string option, n) Bwv.t -> (lt1, ls1, rt1, rs1) parse located -> n extended_ctx =
 fun ctx vars ->
  match vars.value with
  | Ident ([ x ], _) -> Extctx (Suc Zero, Snoc (Emp, vars.loc), Snoc (ctx, Some x))
  | Ident (xs, _) -> fatal (Invalid_variable xs)
  | Placeholder _ -> Extctx (Suc Zero, Snoc (Emp, vars.loc), Snoc (ctx, None))
  | App { fn; arg = { value = Ident ([ x ], _); _ }; _ } ->
      let (Extctx (ab, locs, ctx)) = get_vars ctx fn in
      Extctx (Suc ab, Snoc (locs, vars.loc), Snoc (ctx, Some x))
  | App { arg = { value = Ident (xs, _); _ }; _ } -> fatal (Invalid_variable xs)
  | App { fn; arg = { value = Placeholder _; _ }; _ } ->
      let (Extctx (ab, locs, ctx)) = get_vars ctx fn in
      Extctx (Suc ab, Snoc (locs, vars.loc), Snoc (ctx, None))
  | _ -> fatal Parse_error

let rec raw_lam :
    type a b ab.
    (string option, ab) Bwv.t ->
    [ `Cube | `Normal ] ->
    (a, b, ab) N.plus ->
    (Asai.Range.t option, b) Bwv.t ->
    ab check located ->
    a check located =
 fun names cube ab locs tm ->
  match (names, ab, locs) with
  | _, Zero, Emp -> tm
  | Snoc (names, x), Suc ab, Snoc (locs, loc) ->
      raw_lam names cube ab locs { value = Lam (x, cube, tm); loc = Range.merge_opt loc tm.loc }

let process_abs cube =
  {
    process =
      (fun ctx obs _loc _ ->
        (* The loc argument isn't used here since we can deduce the locations of each lambda by merging its variables with its body. *)
        match obs with
        | [ Term vars; Term body ] ->
            let (Extctx (ab, locs, ctx)) = get_vars ctx vars in
            raw_lam ctx cube ab locs (process ctx body)
        | _ -> fatal (Anomaly "invalid notation arguments for abstraction"));
  }

let pp_abs cube space ppf obs ws =
  match obs with
  | [ vars; body ] ->
      let wsmapsto, _ = take ws in
      pp_open_box ppf 0;
      if true then (
        pp_open_hovbox ppf 2;
        if true then (
          pp_term `Nobreak ppf vars;
          pp_tok ppf
            (match cube with
            | `Normal -> Mapsto
            | `Cube -> DblMapsto));
        pp_close_box ppf ();
        pp_ws `Break ppf wsmapsto;
        pp_term space ppf body);
      pp_close_box ppf ()
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
  set_tree universe (Closed_entry (eop (Ident [ "Type" ]) (Done_closed universe)));
  set_processor universe
    {
      process =
        (fun _ obs loc _ ->
          match obs with
          | [] -> { value = Synth UU; loc }
          | _ -> fatal (Anomaly "invalid notation arguments for Type"));
    };
  set_print universe @@ fun space ppf obs ws ->
  match obs with
  | [] ->
      let ws, _ = take ws in
      pp_print_string ppf "Type";
      pp_ws space ppf ws
  | _ -> fatal (Anomaly (Printf.sprintf "invalid notation arguments for Type: %d" (List.length ws)))

(* ********************
   Degeneracies
   ******************** *)

let degen = make "degeneracy" (Postfix No.plus_omega)

let () =
  set_tree degen (Open_entry (eop (Op "^") (op LBrace (term RBrace (done_open degen)))));
  set_processor degen
    {
      process =
        (fun ctx obs loc _ ->
          match obs with
          | [ Term tm; Term d ] -> (
              match d.value with
              | Ident ([ str ], _) -> (
                  match deg_of_string str with
                  | Some (Any s) -> (
                      match process ctx tm with
                      | { value = Synth x; loc = x_loc } ->
                          { value = Synth (Act (str, s, { value = x; loc = x_loc })); loc }
                      | _ -> fatal (Nonsynthesizing "argument of degeneracy"))
                  | None -> fatal Parse_error)
              | _ -> fatal Parse_error)
          | _ -> fatal (Anomaly "invalid notation arguments for degeneracy"));
    };
  set_print degen @@ fun space ppf obs ws ->
  match obs with
  | [ tm; Term { value = Ident ([ str ], w); _ } ] ->
      let wscaret, ws = take ws in
      let wslbrace, ws = take ws in
      let wsrbrace, _ = take ws in
      pp_term `None ppf tm;
      pp_tok ppf (Op "^");
      pp_ws `None ppf wscaret;
      pp_tok ppf LBrace;
      pp_ws `None ppf wslbrace;
      pp_print_string ppf str;
      pp_ws `None ppf w;
      pp_tok ppf RBrace;
      pp_ws space ppf wsrbrace
  | _ -> fatal (Anomaly "invalid notation arguments for degeneracy")

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
    type n.
    n check located Field.Map.t ->
    (string option, n) Bwv.t ->
    observation list ->
    Asai.Range.t option ->
    n check located =
 fun flds ctx obs loc ->
  match obs with
  | [] -> { value = Raw.Struct flds; loc }
  | Term { value = Ident ([ x ], _); _ } :: obs | Term { value = Field (x, _); _ } :: obs -> (
      match obs with
      | Term tm :: obs ->
          let tm = process ctx tm in
          let fld = Field.intern x in
          process_struc
            (Field.Map.update fld
               (function
                 | None -> Some tm
                 | Some _ -> fatal (Duplicate_field_in_struct fld))
               flds)
            ctx obs loc
      | _ -> fatal (Anomaly "invalid notation arguments for struct"))
  | _ :: _ -> fatal Invalid_field_in_struct

let () =
  set_processor struc { process = (fun ctx obs loc _ -> process_struc Field.Map.empty ctx obs loc) }

let rec pp_fld :
    type a.
    formatter ->
    (formatter -> a -> unit) ->
    a ->
    Whitespace.t list ->
    Token.t ->
    Whitespace.t list ->
    observation ->
    observation list ->
    Whitespace.t list list ->
    Whitespace.t list list =
 fun ppf pp x w tok wstok tm obs ws ->
  pp_open_hovbox ppf 2;
  if true then (
    pp ppf x;
    pp_ws `Nobreak ppf w;
    pp_tok ppf tok;
    pp_ws `Break ppf wstok;
    pp_term (if List.is_empty obs then `None else `Nobreak) ppf tm);
  pp_close_box ppf ();
  match obs with
  | [] -> ws
  | _ ->
      let wssemi, ws = take ws in
      pp_tok ppf (Op ";");
      pp_ws `Break ppf wssemi;
      ws

and pp_fields : formatter -> observation list -> Whitespace.t list list -> Whitespace.t list =
 fun ppf obs ws ->
  match obs with
  | [] ->
      let wsrbrace, _ = take ws in
      wsrbrace
  | Term { value = Ident ([ x ], w); _ } :: obs | Term { value = Field (x, w); _ } :: obs -> (
      let wstok, ws = take ws in
      match obs with
      | tm :: obs ->
          let ws =
            match state () with
            | `Term -> pp_fld ppf pp_var (Some x) w Coloneq wstok tm obs ws
            | `Case -> pp_fld ppf pp_field x w Mapsto wstok tm obs ws in
          pp_fields ppf obs ws
      | _ -> fatal (Anomaly "invalid notation arguments for struct"))
  | _ :: _ -> fatal Invalid_field_in_struct

let pp_struc space ppf obs ws =
  let style, state = (style (), state ()) in
  (match state with
  | `Term ->
      if style = `Noncompact then pp_open_box ppf 0;
      pp_open_hvbox ppf 2
  | `Case -> pp_open_vbox ppf 2);
  pp_tok ppf LBrace;
  if style = `Compact then pp_print_string ppf " " else pp_print_space ppf ();
  let wsrbrace = pp_fields ppf obs ws in
  (if style = `Compact then pp_print_string ppf " "
   else
     match state with
     | `Term ->
         pp_close_box ppf ();
         pp_print_custom_break ~fits:("", 1, "") ~breaks:(" ;", 0, "") ppf
     | `Case -> pp_print_custom_break ~fits:("", 1, "") ~breaks:(" ;", -2, "") ppf);
  pp_tok ppf RBrace;
  pp_close_box ppf ();
  pp_ws space ppf wsrbrace

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
    (string option, n) Bwv.t ->
    (lt1, ls1, rt1, rs1) parse located ->
    Constr.t located * n extended_ctx =
 fun ctx pat ->
  match pat.value with
  | Constr (c, _) -> ({ value = Constr.intern c; loc = pat.loc }, Extctx (Zero, Emp, ctx))
  | App { fn; arg = { value = Ident ([ x ], _); loc }; _ } ->
      let c, Extctx (ab, locs, ctx) = get_pattern ctx fn in
      (c, Extctx (Suc ab, Snoc (locs, loc), Snoc (ctx, Some x)))
  | App { arg = { value = Ident (xs, _); _ }; _ } -> fatal (Invalid_variable xs)
  | App { fn; arg = { value = Placeholder _; loc }; _ } ->
      let c, Extctx (ab, locs, ctx) = get_pattern ctx fn in
      (c, Extctx (Suc ab, Snoc (locs, loc), Snoc (ctx, None)))
  | _ -> fatal Parse_error

let rec process_branches : type n. (string option, n) Bwv.t -> observation list -> n Raw.branch list
    =
 fun ctx obs ->
  match obs with
  | [] -> []
  | Term pat :: Term body :: obs ->
      let c, Extctx (ab, _locs, ectx) = get_pattern ctx pat in
      Branch (c, { value = ab; loc = pat.loc }, process ectx body) :: process_branches ctx obs
  | _ -> fatal (Anomaly "invalid notation arguments for match")

let () =
  set_processor mtch
    {
      process =
        (fun ctx obs loc _ ->
          match obs with
          (* If the first thing is a valid local variable or cube variable, then it's the match variable. *)
          | Term { value = Ident ([ ident ], _); _ } :: obs -> (
              match Bwv.find (Some ident) ctx with
              | None -> fatal (Unbound_variable ident)
              | Some x -> { value = Match ((x, None), process_branches ctx obs); loc })
          | Term { value = Ident ([ ident; fld ], _); _ } :: obs -> (
              match (Bwv.find (Some ident) ctx, Dim.sface_of_string fld) with
              | Some x, Some fa -> { value = Match ((x, Some fa), process_branches ctx obs); loc }
              | None, _ -> fatal (Unbound_variable ident)
              | _ -> fatal Parse_error)
          (* Otherwise, it's a matching lambda. *)
          | _ ->
              let branches = process_branches (Snoc (ctx, None)) obs in
              { value = Lam (None, `Normal, { value = Match ((Top, None), branches); loc }); loc });
    }

let rec pp_branches :
    bool -> formatter -> observation list -> Whitespace.t list list -> Whitespace.t list =
 fun brk ppf obs ws ->
  match obs with
  | pat :: body :: obs ->
      let wsbar, ws = take ws in
      let wsmapsto, ws = take ws in
      let style = style () in
      if brk || style = `Noncompact then pp_print_break ppf 0 2 else pp_print_string ppf " ";
      (match body with
      | Term { value = Notn n; _ } when equal (notn n) mtch && style = `Compact ->
          pp_open_hovbox ppf 0;
          if true then (
            pp_open_hovbox ppf 4;
            if true then (
              pp_tok ppf (Op "|");
              pp_ws `Nobreak ppf wsbar;
              pp_term `Break ppf pat;
              pp_tok ppf Mapsto);
            pp_close_box ppf ();
            pp_ws `Nobreak ppf wsmapsto;
            pp_match false `None ppf (args n) (whitespace n));
          pp_close_box ppf ()
      | _ ->
          pp_open_box ppf 1;
          if true then (
            pp_open_hovbox ppf 4;
            if true then (
              pp_tok ppf (Op "|");
              pp_ws `Nobreak ppf wsbar;
              pp_term `Break ppf pat;
              pp_tok ppf Mapsto);
            pp_close_box ppf ();
            pp_ws `None ppf wsmapsto;
            pp_print_custom_break ppf ~fits:("", 1, "") ~breaks:("", 0, " ");
            pp_term `None ppf body);
          pp_close_box ppf ());
      pp_branches true ppf obs ws
  | [] ->
      let wsrbrack, _ = take ws in
      wsrbrack
  | _ -> fatal (Anomaly "invalid notation arguments for match")

and pp_match box space ppf obs ws =
  let wslbrack, ws = take ws in
  let style = style () in
  match obs with
  | (Term { value = Ident _; _ } as x) :: obs ->
      if box then pp_open_vbox ppf 0;
      if true then (
        pp_tok ppf LBracket;
        pp_ws `Nobreak ppf wslbrack;
        pp_term `None ppf x;
        let wsrbrack = pp_branches true ppf obs ws in
        if style = `Noncompact then pp_print_cut ppf () else pp_print_char ppf ' ';
        pp_tok ppf RBracket;
        pp_ws space ppf wsrbrack);
      if box then pp_close_box ppf ()
  | _ ->
      if box || style = `Noncompact then pp_open_vbox ppf 0;
      if true then (
        pp_tok ppf LBracket;
        pp_ws `None ppf wslbrack;
        let wsrbrack = pp_branches ((not box) || style = `Noncompact) ppf obs ws in
        if style = `Noncompact then pp_print_cut ppf () else pp_print_char ppf ' ';
        pp_tok ppf RBracket;
        pp_ws space ppf wsrbrack);
      if box || style = `Noncompact then pp_close_box ppf ()

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
    |> State.add degen
    |> State.add struc
    |> State.add mtch)

let run : type a. (unit -> a) -> a = fun f -> State.run_on !builtins f
