open Bwd
open Util
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
module StringSet = Set.Make (String)

type 'a located = 'a Asai.Range.located

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
              let x = get_var x in
              let ty, tm = (process ctx ty, process ctx tm) in
              match process (Bwv.snoc ctx x) body with
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
              let x = get_var x in
              match process ctx tm with
              | { value = Synth term; loc = term_loc } -> (
                  match process (Bwv.snoc ctx x) body with
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
            let wslet, ws = take Let ws in
            let wscolon, ws = take Colon ws in
            let wscoloneq, ws = take Coloneq ws in
            let wsin, ws = take In ws in
            taken_last ws;
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
            let wslet, ws = take Let ws in
            let wscoloneq, ws = take Coloneq ws in
            let wsin, ws = take In ws in
            taken_last ws;
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
    n check located =
 fun first flds found ctx obs loc ->
  match obs with
  | [] -> { value = Raw.Struct (Eta, flds); loc }
  | Term { value = Notn n; loc } :: obs when equal (notn n) coloneq -> (
      match args n with
      | [ Term { value = Ident ([ x ], _); loc = xloc }; Term tm ] ->
          let tm = process ctx tm in
          let fld = Field.intern x in
          if Field.Set.mem fld found then fatal ?loc:xloc (Duplicate_field_in_tuple fld)
          else
            process_tuple false (Abwd.add (Some fld) tm flds) (Field.Set.add fld found) ctx obs loc
      | [ Term { value = Placeholder _; _ }; Term tm ] ->
          let tm = process ctx tm in
          process_tuple false (Abwd.add None tm flds) found ctx obs loc
      | Term x :: _ -> fatal ?loc:x.loc Invalid_field_in_tuple
      | _ -> fatal (Anomaly "invalid notation arguments for tuple"))
  | [ Term body ] when first -> process ctx body
  | Term tm :: obs ->
      let tm = process ctx tm in
      process_tuple false (Abwd.add None tm flds) found ctx obs loc

let () =
  set_processor parens
    { process = (fun ctx obs loc _ -> process_tuple true Abwd.empty Field.Set.empty ctx obs loc) }

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
          pp_ws `Break ppf wscomma;
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
      let style, state = (style (), state ()) in
      (match state with
      | `Term ->
          if style = `Noncompact then pp_open_box ppf 0;
          pp_open_hvbox ppf 2
      | `Case -> pp_open_vbox ppf 2);
      pp_tok ppf LParen;
      let wslparen, ws = take LParen ws in
      pp_ws (if style = `Compact then `Nobreak else `Break) ppf wslparen;
      let ws = pp_fields ppf obs ws in
      (if style = `Compact then pp_print_string ppf " "
       else
         match state with
         | `Term ->
             pp_close_box ppf ();
             pp_print_custom_break ~fits:("", 1, "") ~breaks:(",", 0, "") ppf
         | `Case -> pp_print_custom_break ~fits:("", 1, "") ~breaks:(",", -2, "") ppf);
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
  | Term { value = Field (x, _); loc } :: Term tm :: obs ->
      let tm = process ctx tm in
      let fld = Field.intern x in
      if Field.Set.mem fld found then fatal ?loc (Duplicate_method_in_comatch fld)
        (* Comatches can't have unlabeled fields *)
      else process_comatch (Abwd.add (Some fld) tm flds, Field.Set.add fld found) ctx obs loc
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

let mtch = make "match" Outfix

let rec mtch_branches notn bar_ok end_ok =
  Inner
    {
      empty_branch with
      ops =
        TokMap.of_list
          ((if end_ok then [ ((RBracket : Token.t), Done_closed notn) ] else [])
          @ if bar_ok then [ (Op "|", mtch_branches notn false false) ] else []);
      term =
        Some
          (TokMap.singleton Mapsto
             (terms
                [
                  (Op "|", Lazy (lazy (mtch_branches notn false false)));
                  (RBracket, Done_closed notn);
                ]));
    }

let () =
  set_tree mtch
    (Closed_entry
       (eop Match
          (Inner
             {
               empty_branch with
               term = Some (TokMap.singleton LBracket (mtch_branches mtch true true));
             })))

let mtchlam = make "matchlam" Outfix
let () = set_tree mtchlam (Closed_entry (eop LBracket (mtch_branches mtchlam true false)))

let rec get_pattern :
    type n lt1 ls1 rt1 rs1.
    (lt1, ls1, rt1, rs1) parse located ->
    string option list ->
    Constr.t located * string option list =
 fun pat vars ->
  match pat.value with
  | Constr (c, _) -> ({ value = Constr.intern c; loc = pat.loc }, vars)
  | App { fn; arg = { value = Ident ([ x ], _); loc = _ }; _ } -> get_pattern fn (Some x :: vars)
  | App { arg = { value = Ident (xs, _); _ }; _ } -> fatal (Invalid_variable xs)
  | App { fn; arg = { value = Placeholder _; loc = _ }; _ } -> get_pattern fn (None :: vars)
  | _ -> fatal Parse_error

let rec process_branches : type n. (string option, n) Bwv.t -> observation list -> n Raw.branch list
    =
 fun ctx obs ->
  match obs with
  | [] -> []
  | Term pat :: Term body :: obs ->
      let c, vars = get_pattern pat [] in
      let (Wrap xs) = Vec.of_list vars in
      let (Bplus ab) = Fwn.bplus (Vec.length xs) in
      let ectx = Bwv.append ab ctx xs in
      Branch (c, xs, { value = ab; loc = pat.loc }, process ectx body) :: process_branches ctx obs
  | _ -> fatal (Anomaly "invalid notation arguments for (co)match 1")

let () =
  set_processor mtch
    {
      process =
        (fun ctx obs loc _ ->
          match obs with
          (* The first thing must be a valid local variable or cube variable to match against. *)
          | Term { value = Ident ([ ident ], _); _ } :: obs -> (
              match Bwv.find_opt (fun y -> y = Some ident) ctx with
              | None -> fatal (Unbound_variable ident)
              | Some (_, x) -> { value = Match ((x, None), process_branches ctx obs); loc })
          | Term { value = Ident ([ ident; fld ], _); _ } :: obs -> (
              match (Bwv.find_opt (fun y -> y = Some ident) ctx, Dim.sface_of_string fld) with
              | Some (_, x), Some fa ->
                  { value = Match ((x, Some fa), process_branches ctx obs); loc }
              | None, _ -> fatal (Unbound_variable ident)
              | _ -> fatal Parse_error)
          | Term { loc; _ } :: _ -> fatal ?loc Parse_error
          | [] -> fatal Parse_error);
    }

let () =
  set_processor mtchlam
    {
      process =
        (fun ctx obs loc _ ->
          let branches = process_branches (Bwv.snoc ctx None) obs in
          {
            value =
              Lam
                ( { value = None; loc = None },
                  `Normal,
                  { value = Match ((Top, None), branches); loc } );
            loc;
          });
    }

let rec pp_branches : bool -> formatter -> observation list -> Whitespace.alist -> Whitespace.t list
    =
 fun brk ppf obs ws ->
  match obs with
  | pat :: body :: obs ->
      let wsbar, ws = take (Op "|") ws in
      let wsmapsto, ws = take Mapsto ws in
      let style = style () in
      if brk || style = `Noncompact then pp_print_break ppf 0 2 else pp_print_string ppf " ";
      (match body with
      | Term { value = Notn n; _ }
        when (equal (notn n) mtch || equal (notn n) comatch) && style = `Compact ->
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
            pp_match false `Break ppf (args n) (whitespace n));
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
            pp_term `Nobreak ppf body);
          pp_close_box ppf ());
      pp_branches true ppf obs ws
  | [] ->
      let wsrbrack, ws = take RBracket ws in
      taken_last ws;
      wsrbrack
  | _ -> fatal (Anomaly "invalid notation arguments for (co)match 2")

and pp_match box space ppf obs ws =
  let style = style () in
  match take_opt Match ws with
  | Some (wsmtch, ws) -> (
      match obs with
      | (Term { value = Ident _; _ } as x) :: obs ->
          let wslbrack, ws = take LBracket ws in
          if box then pp_open_vbox ppf 0;
          if true then (
            pp_tok ppf Match;
            pp_ws `Nobreak ppf wsmtch;
            pp_term `Nobreak ppf x;
            pp_tok ppf LBracket;
            pp_ws `Nobreak ppf wslbrack;
            let ws = must_start_with (Op "|") ws in
            let wsrbrack = pp_branches true ppf obs ws in
            if style = `Noncompact then pp_print_cut ppf ();
            pp_tok ppf RBracket;
            pp_ws space ppf wsrbrack);
          if box then pp_close_box ppf ()
      | _ -> fatal (Anomaly "missing variable in match"))
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
  set_print_as_case mtch (pp_match true);
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
    (Field.t, string option * n N.suc check located) Abwd.t ->
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
          App { fn = { value = x; loc = xloc }; arg = { value = Field (fld, _); loc = fldloc }; _ };
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
      let fld = Field.intern fld in
      match Abwd.find_opt fld flds with
      | Some _ -> fatal ?loc:fldloc (Duplicate_method_in_codata fld)
      | None ->
          let ty = process (Bwv.snoc ctx x) ty in
          process_codata (Abwd.add fld (x, ty) flds) ctx obs loc)
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
               ops = TokMap.singleton LParen (record_fields ());
               term = Some (TokMap.of_list [ (Mapsto, op LParen (record_fields ())) ]);
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
          match take_opt Mapsto ws with
          | None ->
              let ctx = Bwv.snoc ctx None in
              let (Any_tel tel) = process_tel ctx StringSet.empty obs in
              { value = Record ({ value = Suc Zero; loc }, [ None ], tel); loc }
          | Some _ -> (
              match obs with
              | Term x :: obs ->
                  with_loc x.loc @@ fun () ->
                  let (Wrap vars) = Vec.of_list (List.map fst (process_var_list x [ (None, []) ])) in
                  let (Bplus ac) = Fwn.bplus (Vec.length vars) in
                  let ctx = Bwv.append ac ctx vars in
                  let (Any_tel tel) = process_tel ctx StringSet.empty obs in
                  Range.locate (Record ({ value = ac; loc = x.loc }, vars, tel)) loc
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
  | [] -> { value = Constr ({ value = Constr.intern "nil"; loc }, Emp); loc }
  | Term tm :: tms ->
      let cdr = process_fwd ctx tms loc in
      let car = process ctx tm in
      { value = Constr ({ value = Constr.intern "cons"; loc }, Snoc (Snoc (Emp, car), cdr)); loc }

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

let cons = make "cons" (Infixr No.zero)

let () =
  set_tree cons (Open_entry (eop (Op ":>") (done_open cons)));
  set_processor cons
    {
      process =
        (fun ctx obs loc _ ->
          match obs with
          | [ Term car; Term cdr ] ->
              let car = process ctx car in
              let cdr = process ctx cdr in
              {
                value = Constr ({ value = Constr.intern "cons"; loc }, Snoc (Snoc (Emp, car), cdr));
                loc;
              }
          | _ -> fatal (Anomaly "invalid notation arguments for cons"));
    }

let rec pp_cons : space -> Format.formatter -> observation list -> Whitespace.alist -> unit =
 fun space ppf obs ws ->
  match obs with
  | [ car; cdr ] -> (
      pp_term `Nobreak ppf car;
      pp_tok ppf (Op ":>");
      let wscons, ws = take (Op ":>") ws in
      taken_last ws;
      pp_ws `Break ppf wscons;
      match cdr with
      | Term { value = Notn n; _ } when equal (notn n) cons ->
          pp_cons space ppf (args n) (whitespace n)
      | _ ->
          pp_term space ppf cdr;
          pp_close_box ppf ())
  | _ -> fatal (Anomaly "invalid notation arguments for cons")

let () =
  set_print cons (fun space ppf obs ws ->
      pp_open_hvbox ppf 0;
      pp_cons space ppf obs ws)

(* ********************
   Backwards Lists
   ******************** *)

let bwd = make "bwd" Outfix

let rec process_bwd :
    type n. (string option, n) Bwv.t -> observation Bwd.t -> Asai.Range.t option -> n check located
    =
 fun ctx obs loc ->
  match obs with
  | Emp -> { value = Constr ({ value = Constr.intern "emp"; loc }, Emp); loc }
  | Snoc (tms, Term tm) ->
      let rdc = process_bwd ctx tms loc in
      let rad = process ctx tm in
      { value = Constr ({ value = Constr.intern "snoc"; loc }, Snoc (Snoc (Emp, rdc), rad)); loc }

let () =
  set_tree bwd (Closed_entry (eop LBracket (op (Op "<") (inner_lst "<" bwd))));
  set_processor bwd { process = (fun ctx obs loc _ -> process_bwd ctx (Bwd.of_list obs) loc) };
  set_print bwd (pp_lst "<")

let snoc = make "snoc" (Infixl No.zero)

let () =
  set_tree snoc (Open_entry (eop (Op "<:") (done_open snoc)));
  set_processor snoc
    {
      process =
        (fun ctx obs loc _ ->
          match obs with
          | [ Term rdc; Term rac ] ->
              let rdc = process ctx rdc in
              let rac = process ctx rac in
              {
                value = Constr ({ value = Constr.intern "snoc"; loc }, Snoc (Snoc (Emp, rdc), rac));
                loc;
              }
          | _ -> fatal (Anomaly "invalid notation arguments for snoc"));
    }

let rec pp_snoc : space -> Format.formatter -> observation list -> Whitespace.alist -> unit =
 fun space ppf obs ws ->
  match obs with
  | [ rdc; rac ] ->
      (match rdc with
      | Term { value = Notn n; _ } when equal (notn n) snoc ->
          pp_snoc `Break ppf (args n) (whitespace n)
      | _ ->
          pp_open_hvbox ppf 0;
          pp_term `Break ppf rdc);
      pp_tok ppf (Op "<:");
      let wssnoc, ws = take (Op "<:") ws in
      taken_last ws;
      pp_ws `Nobreak ppf wssnoc;
      pp_term space ppf rac
  | _ -> fatal (Anomaly "invalid notation arguments for snoc")

let () =
  set_print snoc (fun space ppf obs ws ->
      pp_snoc space ppf obs ws;
      pp_close_box ppf ())

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
          | [] -> { value = Hole ctx; loc }
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
    (State.empty
    |> State.add parens
    |> State.add letin
    |> State.add asc
    |> State.add abs
    |> State.add cubeabs
    |> State.add arrow
    |> State.add universe
    |> State.add coloneq
    |> State.add comatch
    |> State.add mtch
    |> State.add mtchlam
    |> State.add empty_co_match
    |> State.add codata
    |> State.add record
    |> State.add data
    |> State.add fwd
    |> State.add bwd
    |> State.add_user "cons" (Infixr No.zero)
         [ `Var ("x", `Break, []); `Op (Op ":>", `Nobreak, []); `Var ("xs", `None, []) ]
         (`Constr (Constr.intern "cons"))
         [ "x"; "xs" ]
    |> State.add_user "snoc" (Infixl No.zero)
         [ `Var ("xs", `Break, []); `Op (Op "<:", `Nobreak, []); `Var ("x", `None, []) ]
         (`Constr (Constr.intern "snoc"))
         [ "xs"; "x" ]
    |> State.add hole)

let run : type a. (unit -> a) -> a = fun f -> State.run_on !builtins f
