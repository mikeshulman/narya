open Bwd
open Util
open Dim
open Postprocess
open Print
open Format
open Core
open Raw
open Reporter
open Notation
open Monad.Ops (Monad.Maybe)
open Printconfig
open Range
module StringSet = Set.Make (String)

(* ********************
   Parentheses
 ******************** *)

let parens = make "parens" Outfix

(* Parentheses are parsed, processed, and printed along with tuples, since their notation overlaps.  *)

(* ********************
   Let-binding
 ******************** *)

(* Let-in doesn't need to be right-associative in order to chain, because it is left-closed, but we make it right-associative anyway for consistency.  *)

let letin = make "let" (Prefixr No.minus_omega)
let letrec = make "letrec" (Prefixr No.minus_omega)

let process_let :
    type n. (string option, n) Bwv.t -> observation list -> Asai.Range.t option -> n check located =
 fun ctx obs loc ->
  match obs with
  | [ Term x; Term ty; Term tm; Term body ] ->
      let x = get_var x in
      let ty = process ctx ty in
      let tm = process ctx tm in
      let body = process (Bwv.snoc ctx x) body in
      let v : n synth located = { value = Asc (tm, ty); loc = Range.merge_opt ty.loc tm.loc } in
      { value = Synth (Let (x, v, body)); loc }
  | [ Term x; Term tm; Term body ] ->
      let x = get_var x in
      let term = process_synth ctx tm "value of let" in
      let body = process (Bwv.snoc ctx x) body in
      { value = Synth (Let (x, term, body)); loc }
  | _ -> fatal (Anomaly "invalid notation arguments for let")

let pp_let toks space ppf obs ws =
  let rec pp_let toks space ppf obs ws =
    let style = style () in
    let ws, wslets =
      List.fold_left_map
        (fun ws tok ->
          let wstok, ws = take tok ws in
          (ws, (tok, wstok)))
        ws toks in
    match obs with
    | [ x; ty; tm; body ] ->
        let wscolon, ws = take Colon ws in
        let wscoloneq, ws = take Coloneq ws in
        let wsin, ws = take In ws in
        taken_last ws;
        if style = `Compact then pp_open_hovbox ppf 2;
        if true then (
          pp_open_hvbox ppf 2;
          if true then (
            List.iter
              (fun (tok, wstok) ->
                pp_tok ppf tok;
                pp_ws `Nobreak ppf wstok)
              wslets;
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
        let wscoloneq, ws = take Coloneq ws in
        let wsin, ws = take In ws in
        taken_last ws;
        if style = `Compact then pp_open_hovbox ppf 2 else pp_open_hvbox ppf 2;
        if true then (
          List.iter
            (fun (tok, wstok) ->
              pp_tok ppf tok;
              pp_ws `Nobreak ppf wstok)
            wslets;
          pp_term `Break ppf x;
          pp_tok ppf Coloneq;
          pp_ws `Nobreak ppf wscoloneq;
          pp_term (if style = `Compact then `Nobreak else `Break) ppf tm;
          pp_tok ppf In);
        pp_close_box ppf ();
        pp_ws `Break ppf wsin;
        pp_let_body space ppf body
    | x :: ty :: tm :: rest when toks = [ Let; Rec ] || toks = [ And ] ->
        let wscolon, ws = take Colon ws in
        let wscoloneq, ws = take Coloneq ws in
        if style = `Compact then pp_open_hovbox ppf 2;
        if true then (
          pp_open_hvbox ppf 2;
          if true then (
            List.iter
              (fun (tok, wstok) ->
                pp_tok ppf tok;
                pp_ws `Nobreak ppf wstok)
              wslets;
            pp_term `Break ppf x;
            pp_tok ppf Colon;
            pp_ws `Nobreak ppf wscolon;
            pp_term `Break ppf ty;
            pp_tok ppf Coloneq;
            pp_ws `Nobreak ppf wscoloneq;
            pp_term (if style = `Compact then `Nobreak else `Break) ppf tm);
          if style = `Compact then pp_close_box ppf ());
        pp_close_box ppf ();
        pp_let [ And ] space ppf rest ws
    | _ -> fatal (Anomaly "invalid notation arguments for let")
  and pp_let_body space ppf tr =
    match tr with
    | Term { value = Notn n; _ } when equal (notn n) letin ->
        pp_let [ Let ] space ppf (args n) (whitespace n)
    | Term { value = Notn n; _ } when equal (notn n) letrec ->
        pp_let [ Let; Rec ] space ppf (args n) (whitespace n)
    | _ -> pp_term space ppf tr in
  pp_open_hvbox ppf 0;
  pp_let toks space ppf obs ws;
  pp_close_box ppf ()

let () =
  set_tree letin
    (Closed_entry
       (eop Let
          (terms
             [
               (Coloneq, term In (Done_closed letin));
               (Colon, term Coloneq (term In (Done_closed letin)));
             ])));
  set_processor letin { process = (fun ctx obs loc _ -> process_let ctx obs loc) };
  set_print letin (pp_let [ Let ])

(* ********************
   Let rec
 ******************** *)

type (_, _) letrec_terms =
  | Letrec_terms :
      ('a, 'b, 'ab) tel
      * ('c, 'b, 'cb) Fwn.fplus
      * ('ab check located, 'cb) Vec.t
      * 'ab check located
      -> ('c, 'a) letrec_terms

let rec process_letrec :
    type c a.
    (string option, a) Bwv.t ->
    observation list ->
    (observation, c) Bwv.t ->
    c N.t ->
    (c, a) letrec_terms =
 fun ctx obs terms c ->
  match obs with
  | Term x :: Term ty :: tm :: rest ->
      let x = get_var x in
      let ty = process ctx ty in
      let (Letrec_terms (tel, Suc cb, terms, body)) =
        process_letrec (Snoc (ctx, x)) rest (Snoc (terms, tm)) (N.suc c) in
      Letrec_terms (Ext (x, ty, tel), cb, terms, body)
  | [ Term body ] ->
      let (Fplus cb) = Fwn.fplus c in
      let body = process ctx body in
      let terms = Bwv.mmap (fun [ Term t ] -> process ctx t) [ terms ] in
      Letrec_terms (Emp, cb, Bwv.prepend cb terms [], body)
  | _ -> fatal (Anomaly "invalid notation arguments for let-rec")

let rec letrec_terms () =
  term Colon
    (term Coloneq (terms [ (And, Lazy (lazy (letrec_terms ()))); (In, Done_closed letrec) ]))

let () =
  set_tree letrec (Closed_entry (eop Let (op Rec (letrec_terms ()))));
  set_processor letrec
    {
      process =
        (fun ctx obs loc _ ->
          let (Letrec_terms (tys, Zero, tms, body)) = process_letrec ctx obs Emp N.zero in
          locate (Synth (Letrec (tys, tms, body))) loc);
    };
  set_print letrec (pp_let [ Let; Rec ])

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
      let w, ws = take Colon ws in
      taken_last ws;
      pp_open_box ppf 0;
      if true then (
        pp_term `Break ppf tm;
        pp_tok ppf Colon;
        pp_ws `Nobreak ppf w;
        pp_term space ppf ty);
      pp_close_box ppf ()
  | _ -> fatal (Anomaly "invalid notation arguments for ascription")

(* ********************
   Telescopes
   ******************** *)

exception Invalid_telescope

(* Inspect 'xs', expecting it to be a spine of valid bindable local variables or underscores, and produce a list of those variables, consing it onto the accumulator argument 'vars'. *)
let rec process_var_list :
    type lt ls rt rs.
    (lt, ls, rt, rs) parse located ->
    (string option * Whitespace.t list) list ->
    (string option * Whitespace.t list) list =
 fun { value; loc } vars ->
  match value with
  | Ident ([ x ], w) -> (Some x, w) :: vars
  | Placeholder w -> (None, w) :: vars
  | App { fn; arg = { value = Ident ([ x ], w); _ }; _ } -> process_var_list fn ((Some x, w) :: vars)
  | App { fn; arg = { value = Placeholder w; _ }; _ } -> process_var_list fn ((None, w) :: vars)
  (* There's a choice here: an invalid variable name could still be a valid term, so we could allow for instance (x.y : A) → B to be parsed as a non-dependent function type.  But that seems a recipe for confusion. *)
  | Ident (name, _) -> fatal ?loc (Invalid_variable name)
  | App { arg = { value = Ident (xs, _); loc }; _ } -> fatal ?loc (Invalid_variable xs)
  | _ -> raise Invalid_telescope

(* Inspect 'arg', expecting it to be of the form 'x y z : A', and return the list of variables, the type, and the whitespace of the colon. *)
let process_typed_vars :
    type lt ls rt rs.
    (lt, ls, rt, rs) parse ->
    (string option * Whitespace.t list) list * Whitespace.t list * observation =
 fun arg ->
  match arg with
  | Notn n when equal (notn n) asc -> (
      match args n with
      | [ Term xs; ty ] ->
          let wscolon, ws = take Colon (whitespace n) in
          taken_last ws;
          (process_var_list xs [], wscolon, ty)
      | _ -> fatal (Anomaly "invalid notation arguments for telescope"))
  | _ -> raise Invalid_telescope

(* ****************************************
   Function types (dependent and non)
 **************************************** *)

let arrow = make "arrow" (Infixr No.zero)

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

(* Inspect 'doms', expecting it to be of the form (x:A)(y:B) etc, and produce a list of variables with types, prepending that list onto the front of the given accumulation list, with the first one having an arrow attached (before it front) if 'wsarrow' is given.  If it isn't of that form, interpret it as the single domain type of a non-dependent function-type and cons it onto the list. *)
let rec get_pi_args :
    type lt ls rt rs. arrow_opt -> (lt, ls, rt, rs) parse located -> pi_dom list -> pi_dom list =
 fun wsarrow doms accum ->
  try
    match doms.value with
    | Notn n when equal (notn n) parens -> (
        match args n with
        | [ Term body ] ->
            let wslparen, ws = take LParen (whitespace n) in
            let wsrparen, ws = take RParen ws in
            taken_last ws;
            let vars, wscolon, ty = process_typed_vars body.value in
            Dep { wsarrow; vars; ty; wslparen; wscolon; wsrparen } :: accum
        | _ -> fatal (Anomaly "invalid notation arguments for arrow"))
    | App { fn; arg = { value = Notn n; _ }; _ } when equal (notn n) parens -> (
        match args n with
        | [ Term body ] ->
            let wslparen, ws = take LParen (whitespace n) in
            let wsrparen, ws = take RParen ws in
            taken_last ws;
            let vars, wscolon, ty = process_typed_vars body.value in
            get_pi_args wsarrow fn
              (Dep { wsarrow = `Noarrow; vars; ty; wslparen; wscolon; wsrparen } :: accum)
        | _ -> fatal (Anomaly "invalid notation arguments for arrow"))
    | _ -> raise Invalid_telescope
  with Invalid_telescope -> Nondep { wsarrow; ty = Term doms } :: accum

(* Get all the domains and eventual codomain from a right-associated iterated function-type. *)
let rec get_pi :
    type lt ls rt rs.
    arrow_opt ->
    observation list ->
    Whitespace.alist ->
    pi_dom list * Whitespace.t list * observation =
 fun prev_arr obs ws ->
  match obs with
  | [ Term doms; Term cod ] ->
      let wsarrow, ws = take Arrow ws in
      taken_last ws;
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
      let ctx = Bwv.snoc ctx None in
      let cod = process_pi ctx doms cod in
      let loc = Range.merge_opt cdom.loc cod.loc in
      { value = Synth (Pi (None, cdom, cod)); loc }
  | Dep ({ vars = (x, _) :: xs; ty = Term dom; _ } as data) :: doms ->
      let cdom = process ctx dom in
      let ctx = Bwv.snoc ctx x in
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

let rec raw_lam :
    type a b ab.
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
      let wsmapsto, ws = take Mapsto ws in
      taken_last ws;
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
      let wstype, ws = take (Ident [ "Type" ]) ws in
      taken_last ws;
      pp_print_string ppf "Type";
      pp_ws space ppf wstype
  | _ -> fatal (Anomaly (Printf.sprintf "invalid notation arguments for Type: %d" (List.length ws)))

(* ********************
   Anonymous tuples
 ******************** *)

let coloneq = make "coloneq" (Infixr No.minus_omega)

let () =
  set_tree coloneq (Open_entry (eop Coloneq (done_open coloneq)));
  set_processor coloneq { process = (fun _ _ _ _ -> fatal Parse_error) }

(* The notation for tuples is "( x ≔ M, y ≔ N, z ≔ P )".  The parentheses don't conflict with ordinary parentheses, since ≔ and , are not term-forming operators all by themselves.  The 0-ary tuple "()" is included, and also doesn't conflict since ordinary parentheses must contain a term.  We also allow some of the components of the tuple to be unlabeled, as in "(M, N, P)"; these are assigned to the fields that don't have a corresponding labeled component in the order they appear in the record type.  The only thing that's not allowed is an unlabeled 1-tuple "(M)" since that would conflict with ordinary parentheses.  (TODO: We could essentially allow that by making the tupling and projection of a 1-ary record type implicit coercions.) *)

let rec tuple_fields () =
  Inner
    {
      empty_branch with
      ops = TokMap.singleton RParen (Done_closed parens);
      term =
        Some
          (TokMap.of_list [ (Op ",", Lazy (lazy (tuple_fields ()))); (RParen, Done_closed parens) ]);
    }

let () = set_tree parens (Closed_entry (eop LParen (tuple_fields ())))

let rec process_tuple :
    type n.
    bool ->
    (Field.t option, n check located) Abwd.t ->
    Field.Set.t ->
    (string option, n) Bwv.t ->
    observation list ->
    Asai.Range.t option ->
    Whitespace.alist ->
    n check located =
 fun first flds found ctx obs loc ws ->
  match obs with
  | [] -> { value = Raw.Struct (Eta, flds); loc }
  | Term { value = Notn n; loc } :: obs when equal (notn n) coloneq -> (
      let ws = Option.fold ~none:ws ~some:snd (take_opt (Op ",") ws) in
      match args n with
      | [ Term { value = Ident ([ x ], _); loc = xloc }; Term tm ] ->
          let tm = process ctx tm in
          let fld = Field.intern x in
          if Field.Set.mem fld found then fatal ?loc:xloc (Duplicate_field_in_tuple fld)
          else
            process_tuple false (Abwd.add (Some fld) tm flds) (Field.Set.add fld found) ctx obs loc
              ws
      | [ Term { value = Placeholder _; _ }; Term tm ] ->
          let tm = process ctx tm in
          process_tuple false (Abwd.add None tm flds) found ctx obs loc ws
      | Term x :: _ -> fatal ?loc:x.loc Invalid_field_in_tuple
      | _ -> fatal (Anomaly "invalid notation arguments for tuple"))
  | [ Term body ] when first && Option.is_none (take_opt (Op ",") ws) -> process ctx body
  | Term tm :: obs ->
      let tm = process ctx tm in
      let ws = Option.fold ~none:ws ~some:snd (take_opt (Op ",") ws) in
      process_tuple false (Abwd.add None tm flds) found ctx obs loc ws

let () =
  set_processor parens
    {
      process =
        (fun ctx obs loc ws ->
          let _, ws = take LParen ws in
          process_tuple true Abwd.empty Field.Set.empty ctx obs loc ws);
    }

let pp_coloneq space ppf obs ws =
  let wscoloneq, ws = take Coloneq ws in
  taken_last ws;
  match obs with
  | [ x; body ] ->
      pp_open_hovbox ppf 2;
      if true then (
        pp_term `Nobreak ppf x;
        pp_tok ppf Coloneq;
        pp_ws `Break ppf wscoloneq;
        pp_term space ppf body);
      pp_close_box ppf ()
  | _ -> fatal (Anomaly "invalid notation arguments for tuple")

let () = set_print coloneq pp_coloneq

let rec pp_fields : formatter -> observation list -> Whitespace.alist -> Whitespace.alist =
 fun ppf obs ws ->
  match obs with
  | [] -> ws
  | tm :: obs -> (
      pp_term `None ppf tm;
      match obs with
      | [] -> ws
      | _ ->
          let wscomma, ws = take (Op ",") ws in
          pp_tok ppf (Op ",");
          pp_ws
            (match spacing () with
            | `Wide -> `Break
            | `Narrow -> `Custom (("", 0, ""), ("", 0, "")))
            ppf wscomma;
          pp_fields ppf obs ws)

let pp_tuple space ppf obs ws =
  match obs with
  | [] ->
      let wslparen, ws = take LParen ws in
      let wsrparen, ws = take RParen ws in
      taken_last ws;
      pp_tok ppf LParen;
      pp_ws `None ppf wslparen;
      pp_tok ppf RParen;
      pp_ws `None ppf wsrparen
  | [ body ] ->
      let wslparen, ws = take LParen ws in
      let wsrparen, ws = take RParen ws in
      taken_last ws;
      pp_open_hovbox ppf 1;
      if true then (
        pp_tok ppf LParen;
        pp_ws `None ppf wslparen;
        pp_term `None ppf body;
        pp_tok ppf RParen);
      pp_close_box ppf ();
      pp_ws space ppf wsrparen
  | _ :: _ ->
      let style, state, spacing = (style (), state (), spacing ()) in
      (match state with
      | `Term ->
          if style = `Noncompact then pp_open_box ppf 0;
          pp_open_hvbox ppf 2
      | `Case -> pp_open_vbox ppf 2);
      pp_tok ppf LParen;
      let wslparen, ws = take LParen ws in
      pp_ws
        (match (style, spacing) with
        | `Compact, `Wide -> `Nobreak
        | `Compact, `Narrow -> `None
        | `Noncompact, _ -> `Break)
        ppf wslparen;
      let ws = pp_fields ppf obs ws in
      (match (style, spacing, state) with
      | `Compact, `Wide, _ -> pp_print_string ppf " "
      | `Compact, `Narrow, _ -> ()
      | `Noncompact, _, `Term ->
          pp_close_box ppf ();
          pp_print_custom_break ~fits:("", 1, "") ~breaks:(",", 0, "") ppf
      | `Noncompact, _, `Case -> pp_print_custom_break ~fits:("", 1, "") ~breaks:(",", -2, "") ppf);
      let ws =
        match take_opt (Op ",") ws with
        | Some (wscomma, ws) ->
            pp_ws `None ppf wscomma;
            ws
        | None -> ws in
      pp_tok ppf RParen;
      let wsrparen, ws = take RParen ws in
      taken_last ws;
      pp_ws space ppf wsrparen;
      pp_close_box ppf ()

let () =
  set_print parens pp_tuple;
  set_print_as_case parens pp_tuple

(* ********************
   Comatches
   ******************** *)

let comatch = make "comatch" Outfix

let rec comatch_fields () =
  field
    (op Mapsto
       (terms [ (Op "|", Lazy (lazy (comatch_fields ()))); (RBracket, Done_closed comatch) ]))

let () =
  set_tree comatch
    (Closed_entry
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
                           (Op "|", Lazy (lazy (comatch_fields ()))); (RBracket, Done_closed comatch);
                         ]));
             })))

let rec process_comatch :
    type n.
    (Field.t option, n check located) Abwd.t * Field.Set.t ->
    (string option, n) Bwv.t ->
    observation list ->
    Asai.Range.t option ->
    n check located =
 fun (flds, found) ctx obs loc ->
  match obs with
  | [] -> { value = Raw.Struct (Noeta, flds); loc }
  | Term { value = Field (x, [], _); loc } :: Term tm :: obs ->
      let tm = process ctx tm in
      let fld = Field.intern x in
      if Field.Set.mem fld found then fatal ?loc (Duplicate_method_in_comatch fld)
        (* Comatches can't have unlabeled fields *)
      else process_comatch (Abwd.add (Some fld) tm flds, Field.Set.add fld found) ctx obs loc
  | Term { value = Field (_, _ :: _, _); _ } :: _ :: _ ->
      fatal (Unimplemented "parsing higher fields in comatch")
  | _ :: _ -> fatal (Anomaly "invalid notation arguments for comatch")

let () =
  set_processor comatch
    { process = (fun ctx obs loc _ -> process_comatch (Abwd.empty, Field.Set.empty) ctx obs loc) }

(* Comatches will be printed with a different instantiation of the functions that print matches. *)

let empty_co_match = make "empty_co_match" Outfix

let () =
  set_tree empty_co_match (Closed_entry (eop LBracket (op RBracket (Done_closed empty_co_match))));
  set_processor empty_co_match { process = (fun _ _ loc _ -> { value = Empty_co_match; loc }) }

(* ********************
   Matches
 ******************** *)

(* A dot is used for refutation branches. *)

let dot = make "dot" Outfix

let () =
  set_tree dot (Closed_entry (eop Dot (Done_closed dot)));
  set_processor dot { process = (fun _ _ _ _ -> fatal Parse_error) }

(* Parsing for implicit matches, explicit (including nondependent) matches, and pattern-matching lambdas shares some code. *)

let implicit_mtch = make "implicit_match" Outfix
let explicit_mtch = make "explicit_match" Outfix
let mtchlam = make "matchlam" Outfix

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

(* Implicit matches can be multiple and deep matches, with multiple discriminees and multiple patterns. *)
let () = set_tree implicit_mtch (Closed_entry (eop Match (discriminees ())))

(* Empty matches [ ] are not allowed for mtchlam, because they are parsed separately as empty_co_match. *)
let () = set_tree mtchlam (Closed_entry (eop LBracket (mtch_branches mtchlam true false true)))

(* Explicitly typed matches can be deep, but not (yet) multiple. *)
let () =
  set_tree explicit_mtch
    (Closed_entry
       (eop Match
          (Inner
             {
               empty_branch with
               term =
                 Some
                   (TokMap.singleton Return
                      (term LBracket (mtch_branches explicit_mtch true true false)));
             })))

(* A pattern is either a variable name or a constructor with some number of pattern arguments. *)
module Pattern = struct
  type t =
    | Var : string option located -> t
    | Constr : Constr.t located * (t, 'n) Vec.t located -> t
end

type pattern = Pattern.t

let get_pattern : type lt1 ls1 rt1 rs1. (lt1, ls1, rt1, rs1) parse located -> pattern =
 fun pat ->
  let rec go :
      type n lt1 ls1 rt1 rs1.
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
    | Notn n when equal (notn n) parens -> (
        match args n with
        | [ Term arg ] -> go arg pats
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
type ('a, 'n) branch = 'a Matchscope.t * (pattern, 'n) Vec.t * observation

(* An ('a, 'm, 'n) cbranch is a branch, with scope of 'a variables, that starts with a constructor (unspecified) having 'm arguments and proceeds with 'n other patterns.  *)
type ('a, 'm, 'n) cbranch =
  'a Matchscope.t * (pattern, 'm) Vec.t located * (pattern, 'n) Vec.t * observation

(* An ('a, 'n) cbranches is a Bwd of branches that start with the same constructor, which always has the same number of arguments, along with a scope of 'a variables common to those branches. *)
type (_, _) cbranches =
  | CBranches : Constr.t located * ('a, 'm, 'n) cbranch Bwd.t -> ('a, 'n) cbranches

let process_ix : type a. a Matchscope.t -> int -> a synth located =
 fun ctx i ->
  match Matchscope.lookup_num i ctx with
  | Some k -> unlocated (Raw.Var (k, None))
  | None -> fatal (Anomaly "invalid parse-level in processing match")

let process_obs_or_ix : type a. a Matchscope.t -> (observation, int) Either.t -> a synth located =
 fun ctx -> function
  | Left (Term x) -> process_synth (Matchscope.names ctx) x "discriminee of match"
  | Right i -> (
      match Matchscope.lookup_num i ctx with
      | Some k -> unlocated (Raw.Var (k, None))
      | None -> fatal (Anomaly "invalid parse-level in processing match"))

(* Given a scope of 'a variables, a vector of 'n not-yet-processed discriminees or previous match variables, and a list of branches with 'n patterns each, compile them into a nested match.  The scope given as an argument to this function is used only for the discriminees; it is the original scope extended by unnamed variables (since the discriminees can't actually depend on the pattern variables).  The scopes used for the branches, which also include pattern variables, are stored in the branch data structures. *)
let rec process_branches :
    type a n.
    a Matchscope.t ->
    ((observation, int) Either.t, n) Vec.t ->
    int Bwd.t ->
    (a, n) branch list ->
    Asai.Range.t option ->
    [ `Implicit | `Explicit of observation | `Nondep of int located ] ->
    a check located =
 fun xctx xs seen branches loc sort ->
  match branches with
  (* An empty match, having no branches, compiles to a refutation that will check by looking for any discriminee with an empty type.  This can only happen as the top-level call, so 'seen' should be empty and we really can just take all the discriminees. *)
  | [] -> (
      let tms = Vec.to_list_map (process_obs_or_ix xctx) xs in
      match (sort, xs) with
      | `Implicit, _ -> locate (Refute (tms, `Implicit)) loc
      | `Explicit (Term motive), [ Left (Term tm) ] -> (
          let ctx = Matchscope.names xctx in
          let sort = `Explicit (process ctx motive) in
          match process ctx tm with
          | { value = Synth tm; loc } ->
              locate
                (Synth (Match { tm = locate tm loc; sort; branches = Emp; refutables = None }))
                loc
          | _ -> fatal (Nonsynthesizing "motive of explicit match"))
      | `Nondep i, [ Left (Term tm) ] -> (
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
  | [ (_, [], Term { value = Notn n; loc }) ] when equal (notn n) dot ->
      let [] = xs in
      let tms = Bwd_extra.to_list_map (process_ix xctx) seen in
      locate (Refute (tms, `Explicit)) loc
  (* Otherwise, the result is just the body of that branch. *)
  | [ (bodyctx, [], Term body) ] ->
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
      | Left (Term tm) ->
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
        | `Explicit (Term motive) -> `Explicit (process (Matchscope.names xctx) motive) in
      locate (Synth (Match { tm; sort; branches; refutables })) loc

let rec get_discriminees :
    observation list ->
    Whitespace.alist ->
    (observation, int) Either.t Vec.wrapped * observation list * Whitespace.alist =
 fun obs ws ->
  match obs with
  | tm :: obs -> (
      match take_opt (Op ",") ws with
      | Some (_, ws) ->
          let Wrap xs, obs, ws = get_discriminees obs ws in
          (Wrap (Left tm :: xs), obs, ws)
      | None -> (Wrap [ Left tm ], obs, ws))
  | [] -> fatal (Anomaly "invalid notation arguments for match")

let rec get_patterns :
    type n.
    n Fwn.t ->
    observation list ->
    Whitespace.alist ->
    (pattern, n) Vec.t * observation list * Whitespace.alist =
 fun n obs ws ->
  match (n, obs) with
  | _, [] | Zero, _ -> fatal (Anomaly "invalid notation arguments for match")
  | Suc Zero, Term tm :: obs -> (
      match take_opt Mapsto ws with
      | Some (_, ws) -> ([ get_pattern tm ], obs, ws)
      | None ->
          let loc =
            match obs with
            | Term tm :: _ -> tm.loc
            | [] -> tm.loc in
          fatal ?loc Parse_error)
  | Suc (Suc _ as n), Term tm :: obs -> (
      match take_opt (Op ",") ws with
      | Some (_, ws) ->
          let pats, obs, ws = get_patterns n obs ws in
          (get_pattern tm :: pats, obs, ws)
      | None -> fatal ?loc:tm.loc Wrong_number_of_patterns)

let rec get_branches :
    type a n.
    a Matchscope.t -> n Fwn.t -> observation list -> Whitespace.alist -> (a, n) branch list =
 fun ctx n obs ws ->
  match obs with
  | [] ->
      let _, ws = take RBracket ws in
      taken_last ws;
      []
  | _ :: _ -> (
      let _, ws = take (Op "|") ws in
      let pats, obs, ws = get_patterns n obs ws in
      match obs with
      | body :: obs ->
          let branches = get_branches ctx n obs ws in
          (ctx, pats, body) :: branches
      | [] -> fatal (Anomaly "invalid notation arguments for match"))

let () =
  set_processor implicit_mtch
    {
      process =
        (fun ctx obs loc ws ->
          let ctx = Matchscope.make ctx in
          let _, ws = take Match ws in
          let Wrap xs, obs, ws = get_discriminees obs ws in
          let _, ws = take LBracket ws in
          let branches =
            match take_opt RBracket ws with
            | Some (_, ws) ->
                taken_last ws;
                []
            | None ->
                let ws = must_start_with (Op "|") ws in
                get_branches ctx (Vec.length xs) obs ws in
          process_branches ctx xs Emp branches loc `Implicit);
    };
  set_processor explicit_mtch
    {
      process =
        (fun ctx obs loc ws ->
          let ctx = Matchscope.make ctx in
          let _, ws = take Match ws in
          match obs with
          | tm :: (Term { value = Notn n; loc = mloc } as motive) :: obs ->
              if equal (notn n) abs then
                let _, ws = take Return ws in
                let _, ws = take LBracket ws in
                let branches =
                  match take_opt RBracket ws with
                  | Some (_, ws) ->
                      taken_last ws;
                      []
                  | None ->
                      let ws = must_start_with (Op "|") ws in
                      get_branches ctx Fwn.one obs ws in
                let sort =
                  match args n with
                  | [ Term vars; Term { value = Placeholder _; _ } ] ->
                      let (Extctx (mn, _, _)) = get_vars (Matchscope.names ctx) vars in
                      `Nondep ({ value = N.to_int (N.plus_right mn); loc = vars.loc } : int located)
                  | _ -> `Explicit motive in
                process_branches ctx [ Left tm ] Emp branches loc sort
              else fatal ?loc:mloc Parse_error
          | _ -> fatal (Anomaly "invalid notation arguments for match"));
    }

(* A version of get_patterns that doesn't require a specific number of patterns in advance. *)
let rec get_any_patterns :
    type n.
    observation list ->
    Whitespace.alist ->
    pattern Vec.wrapped * observation list * Whitespace.alist =
 fun obs ws ->
  match obs with
  | [] -> fatal (Anomaly "invalid notation arguments for match")
  | Term tm :: obs -> (
      match take_opt Mapsto ws with
      | Some (_, ws) -> (Wrap [ get_pattern tm ], obs, ws)
      | None -> (
          match take_opt (Op ",") ws with
          | Some (_, ws) ->
              let Wrap pats, obs, ws = get_any_patterns obs ws in
              (Wrap (get_pattern tm :: pats), obs, ws)
          | None -> fatal (Anomaly "invalid notation arguments for match")))

let () =
  set_processor mtchlam
    {
      process =
        (fun ctx obs loc ws ->
          let _, ws = take LBracket ws in
          (* Empty matching lambdas are a different notation, empty_co_match, so here there must be at least one branch. *)
          let ws = must_start_with (Op "|") ws in
          let _, ws = take (Op "|") ws in
          (* We get the *number* of patterns from the first branch. *)
          let Wrap pats, obs, ws = get_any_patterns obs ws in
          match obs with
          | body :: obs ->
              let n = Vec.length pats in
              let (Bplus an) = Raw.Indexed.bplus n in
              let ctx, xs = Matchscope.exts an (Matchscope.make ctx) in
              let branches = get_branches ctx n obs ws in
              let mtch =
                process_branches ctx
                  (Vec.mmap (fun [ i ] -> Either.Right i) [ xs ])
                  Emp ((ctx, pats, body) :: branches) loc `Implicit in
              Raw.lams an (Vec.init (fun () -> (unlocated None, ())) n ()) mtch loc
          | [] -> fatal (Anomaly "invalid notation arguments for match"));
    }

let rec pp_patterns obs ws =
  match obs with
  | [] -> fatal (Anomaly "invalid notation arguments for (co)match 2")
  | pat :: obs -> (
      match take_opt (Op ",") ws with
      | None -> (obs, ws, fun ppf -> pp_term `Break ppf pat)
      | Some (wscomma, ws) ->
          let obs, ws, cont = pp_patterns obs ws in
          ( obs,
            ws,
            fun ppf ->
              pp_term `Break ppf pat;
              pp_tok ppf (Op ",");
              pp_ws `Nobreak ppf wscomma;
              cont ppf ))

let rec pp_branches : bool -> formatter -> observation list -> Whitespace.alist -> Whitespace.t list
    =
 fun brk ppf obs ws ->
  match obs with
  | _ :: _ :: _ -> (
      let wsbar, ws = take (Op "|") ws in
      let obs, ws, pp_my_patterns = pp_patterns obs ws in
      let wsmapsto, ws = take Mapsto ws in
      match obs with
      | body :: obs ->
          let style = style () in
          if brk || style = `Noncompact then pp_print_break ppf 0 2 else pp_print_string ppf " ";
          (match body with
          | Term { value = Notn n; _ }
            when (equal (notn n) implicit_mtch
                 || equal (notn n) explicit_mtch
                 || equal (notn n) comatch)
                 && style = `Compact ->
              pp_open_hovbox ppf 0;
              if true then (
                pp_open_hovbox ppf 4;
                if true then (
                  pp_tok ppf (Op "|");
                  pp_ws `Nobreak ppf wsbar;
                  pp_my_patterns ppf;
                  pp_tok ppf Mapsto);
                pp_close_box ppf ();
                pp_ws `Nobreak ppf wsmapsto;
                pp_match false `Break ppf (args n) (whitespace n));
              pp_close_box ppf ()
          | _ ->
              pp_open_box ppf 1;
              if true then (
                pp_open_hovbox ppf 4;
                if true then (
                  pp_tok ppf (Op "|");
                  pp_ws `Nobreak ppf wsbar;
                  pp_my_patterns ppf;
                  pp_tok ppf Mapsto);
                pp_close_box ppf ();
                pp_ws `None ppf wsmapsto;
                pp_print_custom_break ppf ~fits:("", 1, "") ~breaks:("", 0, " ");
                pp_term `Nobreak ppf body);
              pp_close_box ppf ());
          pp_branches true ppf obs ws
      | _ -> fatal (Anomaly "invalid notation arguments for (co)match 2"))
  | [] ->
      let wsrbrack, ws = take RBracket ws in
      taken_last ws;
      wsrbrack
  | _ -> fatal (Anomaly "invalid notation arguments for (co)match 2")

and pp_discriminees ppf obs ws =
  match obs with
  | (Term { value = Ident _; _ } as x) :: obs -> (
      pp_term `Nobreak ppf x;
      match take_opt (Op ",") ws with
      | None -> (obs, ws)
      | Some (wscomma, ws) ->
          pp_tok ppf (Op ",");
          pp_ws `Nobreak ppf wscomma;
          pp_discriminees ppf obs ws)
  | _ -> fatal (Anomaly "missing variable in match")

and pp_match box space ppf obs ws =
  let style = style () in
  match take_opt Match ws with
  | Some (wsmtch, ws) ->
      if box then pp_open_vbox ppf 0;
      if true then (
        pp_tok ppf Match;
        pp_ws `Nobreak ppf wsmtch;
        let obs, ws = pp_discriminees ppf obs ws in
        let ws, obs =
          match (take_opt Return ws, obs) with
          | Some (wsret, ws), motive :: obs ->
              pp_tok ppf Return;
              pp_ws `Nobreak ppf wsret;
              pp_term `Nobreak ppf motive;
              (ws, obs)
          | _ -> (ws, obs) in
        let wslbrack, ws = take LBracket ws in
        pp_tok ppf LBracket;
        pp_ws `Nobreak ppf wslbrack;
        let ws = must_start_with (Op "|") ws in
        let wsrbrack = pp_branches true ppf obs ws in
        if style = `Noncompact then pp_print_cut ppf ();
        pp_tok ppf RBracket;
        pp_ws space ppf wsrbrack);
      if box then pp_close_box ppf ()
  | None ->
      let wslbrack, ws = take LBracket ws in
      let box = box || style = `Noncompact in
      if box then pp_open_vbox ppf 0;
      if true then (
        pp_tok ppf LBracket;
        pp_ws (if box then `None else `Nobreak) ppf wslbrack;
        let ws = must_start_with (Op "|") ws in
        let wsrbrack = pp_branches ((not box) || style = `Noncompact) ppf obs ws in
        if style = `Noncompact then pp_print_cut ppf ();
        pp_tok ppf RBracket;
        pp_ws space ppf wsrbrack);
      if box then pp_close_box ppf ()

(* Matches and comatches are only valid in case trees. *)
let () =
  set_print_as_case implicit_mtch (pp_match true);
  set_print_as_case explicit_mtch (pp_match true);
  set_print_as_case mtchlam (pp_match true);
  set_print_as_case comatch (pp_match true);
  set_print_as_case empty_co_match (pp_match true)

(* ********************
   Codatatypes
   ******************** *)

let codata = make "codata" Outfix

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

let () = set_tree codata (Closed_entry (eop Codata (op LBracket (codata_fields true))))

let rec process_codata :
    type n.
    (Field.t, n Raw.codatafield) Abwd.t ->
    (string option, n) Bwv.t ->
    observation list ->
    Asai.Range.t option ->
    n check located =
 fun flds ctx obs loc ->
  match obs with
  | [] -> { value = Raw.Codata flds; loc }
  | Term
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
    :: Term ty
    :: obs -> (
      with_loc loc @@ fun () ->
      let x =
        match x with
        | Ident ([ x ], _) -> Some x
        | Placeholder _ -> None
        | Ident (x, _) -> fatal ?loc:xloc (Invalid_variable x)
        | _ -> fatal ?loc:xloc Parse_error in
      let fld = Field.intern fstr in
      match dim_of_string (String.concat "" fdstr) with
      | Some (Any fdim) -> (
          match Abwd.find_opt fld flds with
          | Some _ -> fatal ?loc:fldloc (Duplicate_method_in_codata fld)
          | None ->
              let ty = process (Bwv.snoc ctx x) ty in
              process_codata (Abwd.add fld (Raw.Codatafield (x, fdim, ty)) flds) ctx obs loc)
      | None -> fatal (Invalid_field (String.concat "." ("" :: fstr :: fdstr))))
  | _ :: _ -> fatal (Anomaly "invalid notation arguments for codata")

let () = set_processor codata { process = (fun ctx obs loc _ -> process_codata Emp ctx obs loc) }

let rec pp_codata_fields ppf obs ws =
  match obs with
  | [] ->
      let wsrbrack, ws = take RBracket ws in
      taken_last ws;
      wsrbrack
  | varfld :: body :: obs ->
      pp_open_hvbox ppf 2;
      let wsbar, ws = take (Op "|") ws in
      pp_tok ppf (Op "|");
      pp_ws `Nobreak ppf wsbar;
      pp_term `Break ppf varfld;
      let wscolon, ws = take Colon ws in
      pp_tok ppf Colon;
      pp_ws `Nobreak ppf wscolon;
      pp_close_box ppf ();
      pp_term (if style () = `Compact && List.is_empty obs then `Nobreak else `Break) ppf body;
      pp_codata_fields ppf obs ws
  | _ :: _ -> fatal (Anomaly "invalid notation arguments for codata")

let pp_codata space ppf obs ws =
  pp_open_vbox ppf 0;
  let wscodata, ws = take Codata ws in
  pp_tok ppf Codata;
  pp_ws `Nobreak ppf wscodata;
  let wslbrack, ws = take LBracket ws in
  pp_tok ppf LBracket;
  pp_ws `Break ppf wslbrack;
  let ws = must_start_with (Op "|") ws in
  let wsrbrack = pp_codata_fields ppf obs ws in
  pp_tok ppf RBracket;
  pp_ws space ppf wsrbrack;
  pp_close_box ppf ()

let () = set_print codata pp_codata

(* ********************
   Record types
   ******************** *)

let record = make "record" Outfix

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

let () =
  set_tree record
    (Closed_entry
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
             })))

type _ any_tel = Any_tel : ('a, 'c, 'ac) Raw.tel -> 'a any_tel

let rec process_tel :
    type a. (string option, a) Bwv.t -> StringSet.t -> observation list -> a any_tel =
 fun ctx seen obs ->
  match obs with
  | [] -> Any_tel Emp
  | Term { value = Ident ([ name ], _); loc } :: Term ty :: obs ->
      if StringSet.mem name seen then fatal ?loc (Duplicate_field_in_record (Field.intern name));
      let ty = process ctx ty in
      let ctx = Bwv.snoc ctx (Some name) in
      let (Any_tel tel) = process_tel ctx (StringSet.add name seen) obs in
      Any_tel (Ext (Some name, ty, tel))
  | _ :: _ :: _ -> fatal Parse_error
  | _ :: [] -> fatal (Anomaly "invalid notation arguments for record")

let () =
  set_processor record
    {
      process =
        (fun ctx obs loc ws ->
          let _, ws = take Sig ws in
          let opacity, ws, obs =
            match (take_opt (Op "#") ws, obs) with
            | None, _ -> (`Opaque, ws, obs)
            | Some (_, ws), Term attr :: obs ->
                let _, ws = take LParen ws in
                let _, ws = take RParen ws in
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
                (opacity, ws, obs)
            | _ -> fatal (Anomaly "invalid notation arguments for record") in
          match take_opt Mapsto ws with
          | None ->
              let ctx = Bwv.snoc ctx None in
              let (Any_tel tel) = process_tel ctx StringSet.empty obs in
              { value = Record ({ value = [ None ]; loc }, tel, opacity); loc }
          | Some _ -> (
              match obs with
              | Term x :: obs ->
                  with_loc x.loc @@ fun () ->
                  let (Wrap vars) = Vec.of_list (List.map fst (process_var_list x [ (None, []) ])) in
                  let (Bplus ac) = Fwn.bplus (Vec.length vars) in
                  let ctx = Bwv.append ac ctx vars in
                  let (Any_tel tel) = process_tel ctx StringSet.empty obs in
                  Range.locate
                    (Record (locate_opt x.loc (namevec_of_vec ac vars), tel, opacity))
                    loc
              | _ -> fatal (Anomaly "invalid notation arguments for record")));
    }

let rec pp_record_fields ppf obs ws =
  match obs with
  | [] ->
      let wsrparen, ws = take RParen ws in
      taken_last ws;
      wsrparen
  | var :: body :: obs ->
      pp_open_hvbox ppf 2;
      pp_term `Break ppf var;
      let wscolon, ws = take Colon ws in
      pp_tok ppf Colon;
      pp_ws `Nobreak ppf wscolon;
      pp_close_box ppf ();
      let ws = must_start_with (Op ",") ws in
      let wscomma, ws = take (Op ",") ws in
      pp_term `None ppf body;
      if style () = `Compact && List.is_empty obs then pp_ws `None ppf wscomma
      else (
        pp_tok ppf (Op ",");
        pp_ws `Break ppf wscomma);
      pp_record_fields ppf obs ws
  | [ _ ] -> fatal (Anomaly "invalid notation arguments for record")

let pp_record space ppf obs ws =
  pp_open_vbox ppf 2;
  let wssig, ws = take Sig ws in
  pp_tok ppf Sig;
  pp_ws `Nobreak ppf wssig;
  let wslparen, ws = take LParen ws in
  pp_tok ppf LParen;
  pp_ws `Break ppf wslparen;
  let wsrparen = pp_record_fields ppf obs ws in
  pp_tok ppf RParen;
  pp_ws space ppf wsrparen;
  pp_close_box ppf ()

let () = set_print record pp_record

(* ********************
   Datatypes
   ******************** *)

let data = make "data" Outfix

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

let () = set_tree data (Closed_entry (eop Data (op LBracket (data_constrs true))))

let rec constr_tel :
    observation ->
    (string option list * observation) list ->
    Constr.t located * (string option list * observation) list =
 fun tel accum ->
  match tel with
  | Term { value = Constr (c, _); loc } -> ({ value = Constr.intern c; loc }, accum)
  | Term { value = App { fn; arg = { value = Notn n; loc = _ }; _ }; loc = _ }
    when equal (notn n) parens -> (
      match args n with
      | [ Term arg ] ->
          let vars, _, ty = process_typed_vars arg.value in
          constr_tel (Term fn) ((List.map fst vars, ty) :: accum)
      | _ -> fatal (Anomaly "invalid notation arguments for tel"))
  | _ -> fatal Parse_error

let rec process_dataconstr :
    type n.
    (string option, n) Bwv.t ->
    (string option list * observation) list ->
    observation option ->
    n Raw.dataconstr =
 fun ctx tel_args ty ->
  match (tel_args, ty) with
  | (vars, argty) :: tel_args, _ -> process_dataconstr_vars ctx vars argty tel_args ty
  | [], Some (Term ty) -> dataconstr_of_pi (process ctx ty)
  | [], None -> Dataconstr (Emp, None)

and process_dataconstr_vars :
    type n.
    (string option, n) Bwv.t ->
    string option list ->
    observation ->
    (string option list * observation) list ->
    observation option ->
    n Raw.dataconstr =
 fun ctx vars (Term argty) tel_args ty ->
  match vars with
  | [] -> process_dataconstr ctx tel_args ty
  | x :: xs ->
      let newctx = Bwv.snoc ctx x in
      let (Dataconstr (args, body)) = process_dataconstr_vars newctx xs (Term argty) tel_args ty in
      let arg = process ctx argty in
      Dataconstr (Ext (x, arg, args), body)

let rec process_data :
    type n.
    (Constr.t, n Raw.dataconstr located) Abwd.t ->
    (string option, n) Bwv.t ->
    observation list ->
    Asai.Range.t option ->
    n check located =
 fun constrs ctx obs loc ->
  match obs with
  | [] -> { value = Raw.Data constrs; loc }
  | Term tel :: obs -> (
      let Term tel, ty =
        match tel with
        | { value = Notn n; loc = _ } when equal (notn n) asc -> (
            match args n with
            | [ tel; ty ] -> (tel, Some ty)
            | _ -> fatal (Anomaly "invalid notation arguments for data"))
        | _ -> (Term tel, None) in
      let c, tel_args = constr_tel (Term tel) [] in
      match Abwd.find_opt c.value constrs with
      | Some _ -> fatal ?loc:c.loc (Duplicate_constructor_in_data c.value)
      | None ->
          let dc = process_dataconstr ctx tel_args ty in
          process_data
            (Abwd.add c.value ({ value = dc; loc = tel.loc } : n dataconstr located) constrs)
            ctx obs loc)

let () = set_processor data { process = (fun ctx obs loc _ -> process_data Emp ctx obs loc) }

let rec pp_data_constrs ppf obs ws =
  match obs with
  | [] ->
      let wsrbrack, ws = take RBracket ws in
      taken_last ws;
      wsrbrack
  | constr :: obs ->
      pp_open_hvbox ppf 2;
      let wsbar, ws = take (Op "|") ws in
      pp_tok ppf (Op "|");
      pp_ws `Nobreak ppf wsbar;
      if List.is_empty obs then (
        if style () = `Compact then pp_term `Nobreak ppf constr else pp_term `Break ppf constr;
        pp_close_box ppf ())
      else (
        pp_term `Break ppf constr;
        pp_close_box ppf ();
        (* I don't understand why this seems to be necessary.  The `Break in the previous line should insert a break, and it does in the case of codata, but for some reason not here. *)
        pp_print_cut ppf ());
      pp_data_constrs ppf obs ws

let pp_data space ppf obs ws =
  pp_open_vbox ppf 0;
  let wsdata, ws = take Data ws in
  pp_tok ppf Data;
  pp_ws `Nobreak ppf wsdata;
  let wslbrack, ws = take LBracket ws in
  pp_tok ppf LBracket;
  pp_ws `Break ppf wslbrack;
  (* We can't use "must_start_with" since there are no operators inside other than "|", so we compare lengths to make sure there are the right *number* of "|"s. *)
  let ws = if List.length ws <= List.length obs then (Token.Op "|", []) :: ws else ws in
  let wsrbrack = pp_data_constrs ppf obs ws in
  pp_tok ppf RBracket;
  pp_ws space ppf wsrbrack;
  pp_close_box ppf ()

let () = set_print data pp_data

(* ********************
   Forwards Lists
   ******************** *)

let fwd = make "list" Outfix

(* We define the notation tree and printing functions for lists to be parametric over the notation and direction symbol, so that we can re-use them for both forwards and backwards lists. *)

let rec inner_lst s n =
  Inner
    {
      empty_branch with
      ops = TokMap.singleton (Op s) (op RBracket (Done_closed n));
      term =
        Some
          (TokMap.of_list
             [ (Op ",", Lazy (lazy (inner_lst s n))); (Op s, op RBracket (Done_closed n)) ]);
    }

let rec process_fwd :
    type n. (string option, n) Bwv.t -> observation list -> Asai.Range.t option -> n check located =
 fun ctx obs loc ->
  match obs with
  | [] -> { value = Constr ({ value = Constr.intern "nil"; loc }, []); loc }
  | Term tm :: tms ->
      let cdr = process_fwd ctx tms loc in
      let car = process ctx tm in
      { value = Constr ({ value = Constr.intern "cons"; loc }, [ car; cdr ]); loc }

let rec pp_elts : Format.formatter -> observation list -> Whitespace.alist -> Whitespace.alist =
 fun ppf obs ws ->
  match obs with
  | [] -> ws
  | [ tm ] ->
      pp_term `None ppf tm;
      let ws = must_start_with (Op ",") ws in
      let wscomma, ws = take (Op ",") ws in
      (* TODO: If the last entry in a vboxed list is followed by a comment, then it doesn't get a comma after it the way it should in a vbox case. *)
      pp_ws (`Custom (("", 1, ""), (",", -2, ""))) ppf wscomma;
      ws
  | tm :: obs ->
      pp_term `None ppf tm;
      let wscomma, ws = take (Op ",") ws in
      pp_tok ppf (Op ",");
      pp_ws `Break ppf wscomma;
      pp_elts ppf obs ws

let pp_lst : string -> space -> Format.formatter -> observation list -> Whitespace.alist -> unit =
 fun s space ppf obs ws ->
  pp_open_hvbox ppf 2;
  if true then (
    pp_tok ppf LBracket;
    let wslbracket, ws = take LBracket ws in
    pp_ws `None ppf wslbracket;
    pp_tok ppf (Op s);
    let wsangle, ws = take (Op s) ws in
    pp_ws `Break ppf wsangle;
    let ws = pp_elts ppf obs ws in
    pp_tok ppf (Op s);
    let wsangle, ws = take (Op s) ws in
    pp_ws `None ppf wsangle;
    pp_tok ppf RBracket;
    let wsrbracket, ws = take RBracket ws in
    pp_ws space ppf wsrbracket;
    taken_last ws);
  pp_close_box ppf ()

let () =
  set_tree fwd (Closed_entry (eop LBracket (op (Op ">") (inner_lst ">" fwd))));
  set_processor fwd { process = (fun ctx obs loc _ -> process_fwd ctx obs loc) };
  set_print fwd (pp_lst ">")

(* ********************
   Backwards Lists
   ******************** *)

let bwd = make "bwd" Outfix

let rec process_bwd :
    type n. (string option, n) Bwv.t -> observation Bwd.t -> Asai.Range.t option -> n check located
    =
 fun ctx obs loc ->
  match obs with
  | Emp -> { value = Constr ({ value = Constr.intern "emp"; loc }, []); loc }
  | Snoc (tms, Term tm) ->
      let rdc = process_bwd ctx tms loc in
      let rac = process ctx tm in
      { value = Constr ({ value = Constr.intern "snoc"; loc }, [ rdc; rac ]); loc }

let () =
  set_tree bwd (Closed_entry (eop LBracket (op (Op "<") (inner_lst "<" bwd))));
  set_processor bwd { process = (fun ctx obs loc _ -> process_bwd ctx (Bwd.of_list obs) loc) };
  set_print bwd (pp_lst "<")

(* ********************
   Holes
 ******************** *)

let hole = make "hole" Outfix

let () =
  set_tree hole (Closed_entry (eop Query (Done_closed hole)));
  set_processor hole
    {
      process =
        (fun ctx obs loc _ ->
          match obs with
          | [] -> { value = Hole (ctx, locate () loc); loc }
          | _ -> fatal (Anomaly "invalid notation arguments for hole"));
    };
  set_print hole @@ fun space ppf obs ws ->
  match obs with
  | [] ->
      let wshole, ws = take Query ws in
      taken_last ws;
      pp_print_string ppf "?";
      pp_ws space ppf wshole
  | _ -> fatal (Anomaly (Printf.sprintf "invalid notation arguments for hole: %d" (List.length ws)))

(* ********************
   Generating the state
 ******************** *)

let builtins =
  ref
    (Situation.empty
    |> Situation.add parens
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
    |> Situation.add data
    |> Situation.add fwd
    |> Situation.add bwd
    |> Situation.add hole)

let run : type a. (unit -> a) -> a = fun f -> Situation.run_on !builtins f
