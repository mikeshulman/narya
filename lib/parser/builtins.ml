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

(* ********************
   Parentheses
 ******************** *)

let parens = make "parens" Outfix

let () =
  set_tree parens (Closed_entry (eop LParen (term RParen (Done_closed parens))));
  set_processor parens
    {
      process =
        (fun ctx obs _ ->
          match obs with
          | [ Term body ] -> process ctx body
          | _ -> fatal (Anomaly "invalid notation arguments for parens"));
    }

let pp_parens space ppf obs ws =
  match obs with
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
        (fun ctx obs _ ->
          match obs with
          | [ Term x; Term ty; Term tm; Term body ] -> (
              let x = get_var x in
              let ty, tm = (process ctx ty, process ctx tm) in
              match process (Snoc (ctx, x)) body with
              | Synth body -> Synth (Let (x, Asc (tm, ty), body))
              | _ -> fatal (Nonsynthesizing "body of let"))
          | [ Term x; Term tm; Term body ] -> (
              let x = get_var x in
              match process ctx tm with
              | Synth term -> (
                  match process (Snoc (ctx, x)) body with
                  | Synth body -> Synth (Let (x, term, body))
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
        | Term (Notn n) when equal (notn n) letin -> pp_let space ppf (args n) (whitespace n)
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
        (fun ctx obs _ ->
          match obs with
          | [ Term tm; Term ty ] ->
              let tm = process ctx tm in
              let ty = process ctx ty in
              Synth (Asc (tm, ty))
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
  | App { fn; arg = Ident ([ x ], w); _ } -> get_pi_vars fn ((Some x, w) :: vars)
  | App { fn; arg = Placeholder w; _ } -> get_pi_vars fn ((None, w) :: vars)
  (* There's a choice here: an invalid variable name could still be a valid term, so we could allow for instance (x.y : A) → B to be parsed as a non-dependent function type.  But that seems a recipe for confusion. *)
  | Ident (xs, _) -> fatal (Invalid_variable xs)
  | App { arg = Ident (xs, _); _ } -> fatal (Invalid_variable xs)
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
          let wscolon, ws = take Colon (whitespace n) in
          taken_last ws;
          let vars = get_pi_vars xs [] in
          Dep { wsarrow; vars; ty = dom; wslparen; wscolon; wsrparen }
      | _ -> fatal (Anomaly "invalid notation arguments for arrow"))
  | _ -> raise Not_a_pi_arg

(* Inspect 'doms', expecting it to be of the form (x:A)(y:B) etc, and produce a list of variables with types, prepending that list onto the front of the given accumulation list, with the first one having an arrow attached (before it front) if 'wsarrow' is given.  If it isn't of that form, interpret it as the single domain type of a non-dependent function-type and cons it onto the list. *)
let rec get_pi_args :
    type lt ls rt rs. arrow_opt -> (lt, ls, rt, rs) parse -> pi_dom list -> pi_dom list =
 fun wsarrow doms vars ->
  try
    match doms with
    | Notn n when equal (notn n) parens -> (
        match args n with
        | [ Term body ] ->
            let wslparen, ws = take LParen (whitespace n) in
            let wsrparen, ws = take RParen ws in
            taken_last ws;
            get_pi_arg ~wsarrow body ~wslparen ~wsrparen :: vars
        | _ -> fatal (Anomaly "invalid notation arguments for arrow"))
    | App { fn; arg = Notn n; _ } when equal (notn n) parens -> (
        match args n with
        | [ Term body ] ->
            let wslparen, ws = take LParen (whitespace n) in
            let wsrparen, ws = take RParen ws in
            taken_last ws;
            get_pi_args wsarrow fn (get_pi_arg ~wsarrow:`Noarrow body ~wslparen ~wsrparen :: vars)
        | _ -> fatal (Anomaly "invalid notation arguments for arrow"))
    | _ -> raise Not_a_pi_arg
  with Not_a_pi_arg -> Nondep { wsarrow; ty = Term doms } :: vars

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
        match cod with
        | Notn n when equal (notn n) arrow -> get_pi (`Arrow wsarrow) (args n) (whitespace n)
        | _ -> ([], wsarrow, Term cod) in
      (get_pi_args prev_arr doms vars, ws, cod)
  | _ -> fatal (Anomaly "invalid notation arguments for arrow")

(* Given the variables with domains and the codomain of a pi-type, process it into a raw term. *)
let rec process_pi :
    type n lt ls rt rs. (string option, n) Bwv.t -> pi_dom list -> (lt, ls, rt, rs) parse -> n check
    =
 fun ctx doms cod ->
  match doms with
  | [] -> process ctx cod
  | Nondep { ty = Term dom; _ } :: doms ->
      let cdom = process ctx dom in
      let ctx = Bwv.Snoc (ctx, None) in
      let cod = process_pi ctx doms cod in
      Synth (Pi (None, cdom, cod))
  | Dep ({ vars = (x, _) :: xs; ty = Term dom; _ } as data) :: doms ->
      let cdom = process ctx dom in
      let ctx = Bwv.Snoc (ctx, x) in
      let cod = process_pi ctx (Dep { data with vars = xs } :: doms) cod in
      Synth (Pi (x, cdom, cod))
  | Dep { vars = []; _ } :: doms -> process_pi ctx doms cod

let () =
  set_tree arrow (Open_entry (eop Arrow (done_open arrow)));
  set_processor arrow
    {
      process =
        (fun ctx obs ws ->
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
  | Extctx : ('n, 'm, 'nm) N.plus * (string option, 'nm) Bwv.t -> 'n extended_ctx

let rec get_vars :
    type n lt1 ls1 rt1 rs1. (string option, n) Bwv.t -> (lt1, ls1, rt1, rs1) parse -> n extended_ctx
    =
 fun ctx vars ->
  match vars with
  | Ident ([ x ], _) ->
      (* TODO: Can we report the range for errors produced here? *)
      Extctx (Suc Zero, Snoc (ctx, Some x))
  | Ident (xs, _) -> fatal (Invalid_variable xs)
  | Placeholder _ -> Extctx (Suc Zero, Snoc (ctx, None))
  | App { fn; arg = Ident ([ x ], _); _ } ->
      let (Extctx (ab, ctx)) = get_vars ctx fn in
      Extctx (Suc ab, Snoc (ctx, Some x))
  | App { arg = Ident (xs, _); _ } -> fatal (Invalid_variable xs)
  | App { fn; arg = Placeholder _; _ } ->
      let (Extctx (ab, ctx)) = get_vars ctx fn in
      Extctx (Suc ab, Snoc (ctx, None))
  | _ -> fatal Parse_error

let process_abs cube =
  {
    process =
      (fun ctx obs _ ->
        match obs with
        | [ Term vars; Term body ] ->
            let (Extctx (ab, ctx)) = get_vars ctx vars in
            raw_lam ctx cube ab (process ctx body)
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
        (fun _ obs _ ->
          match obs with
          | [] -> Synth UU
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
   Degeneracies
   ******************** *)

let degen = make "degeneracy" (Postfix No.plus_omega)

let () =
  set_tree degen (Open_entry (eop (Op "^") (op LBrace (term RBrace (done_open degen)))));
  set_processor degen
    {
      process =
        (fun ctx obs _ ->
          match obs with
          | [ Term tm; Term d ] -> (
              match d with
              | Ident ([ str ], _) -> (
                  match deg_of_string str with
                  | Some (Any s) -> (
                      match process ctx tm with
                      | Synth x -> Synth (Act (str, s, x))
                      | _ -> fatal (Nonsynthesizing "argument of degeneracy"))
                  | None -> fatal Parse_error)
              | _ -> fatal Parse_error)
          | _ -> fatal (Anomaly "invalid notation arguments for degeneracy"));
    };
  set_print degen @@ fun space ppf obs ws ->
  match obs with
  | [ tm; Term (Ident ([ str ], w)) ] ->
      let wscaret, ws = take (Op "^") ws in
      let wslbrace, ws = take LBrace ws in
      let wsrbrace, ws = take RBrace ws in
      taken_last ws;
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
   Anonymous tuples
 ******************** *)

let tuple = make "tuple" Outfix

(* The notation for tuples is "( x ≔ M, y ≔ N, z ≔ P )".  The parentheses don't conflict with ordinary parentheses, since ≔ and , are not term-forming operators all by themselves.  The 0-ary tuple "()" is included, and also doesn't conflict since ordinary parentheses must contain a term. *)

let rec tuple_fields () =
  Inner
    {
      empty_branch with
      ops = TokMap.singleton RParen (Done_closed tuple);
      term =
        Some
          (TokMap.singleton Coloneq
             (terms [ (Op ",", Lazy (lazy (tuple_fields ()))); (RParen, Done_closed tuple) ]));
    }

let () = set_tree tuple (Closed_entry (eop LParen (tuple_fields ())))

(* We define the processor to allow both variables and fields, with eta as a parameter, so that we can re-use it for processing comatches. *)

let rec process_struct :
    type n.
    eta ->
    n check Field.Map.t * Field.Set.t ->
    (string option, n) Bwv.t ->
    observation list ->
    n check =
 fun eta (flds, found) ctx obs ->
  match obs with
  | [] -> Raw.Struct (eta, flds)
  | Term (Ident ([ x ], _)) :: obs | Term (Field (x, _)) :: obs -> (
      match obs with
      | Term tm :: obs ->
          let tm = process ctx tm in
          let fld = Field.intern x in
          if Field.Set.mem fld found then fatal (duplicate_field eta fld)
          else process_struct eta (Field.Map.add fld tm flds, Field.Set.add fld found) ctx obs
      | _ -> fatal (Anomaly "invalid notation arguments for tuple/comatch"))
  | _ :: _ ->
      (* I think it's impossible to get here in the case of a comatch, since in that case we explicitly parsed a Field. *)
      fatal Invalid_field_in_tuple

let () =
  set_processor tuple
    { process = (fun ctx obs _ -> process_struct `Eta (Field.Map.empty, Field.Set.empty) ctx obs) }

(* We define the pretty-printing functions parametrically over symbols so we can re-use them for printing comatches. *)

let rec pp_fld :
    type a.
    formatter ->
    (formatter -> a -> unit) ->
    a ->
    Whitespace.t list ->
    Whitespace.t list ->
    observation ->
    observation list ->
    Whitespace.alist ->
    Whitespace.alist =
 fun ppf pp x w wscoloneq tm obs ws ->
  pp_open_hovbox ppf 2;
  if true then (
    pp ppf x;
    pp_ws `Nobreak ppf w;
    pp_tok ppf Coloneq;
    pp_ws `Break ppf wscoloneq;
    pp_term `None ppf tm);
  pp_close_box ppf ();
  match obs with
  | [] -> ws
  | _ ->
      let wscomma, ws = take (Op ",") ws in
      pp_tok ppf (Op ",");
      pp_ws `Break ppf wscomma;
      ws

and pp_fields : formatter -> observation list -> Whitespace.alist -> Whitespace.alist =
 fun ppf obs ws ->
  match obs with
  | [] -> ws
  | Term (Ident ([ x ], w)) :: obs -> (
      let wscoloneq, ws = take Coloneq ws in
      match obs with
      | tm :: obs ->
          let ws = pp_fld ppf pp_var (Some x) w wscoloneq tm obs ws in
          pp_fields ppf obs ws
      | _ -> fatal (Anomaly "invalid notation arguments for tuple"))
  | _ :: _ -> fatal (Anomaly "invalid notation arguments for tuple")

let pp_tuple space ppf obs ws =
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

let () = set_print tuple pp_tuple

(* ********************
   Comatches
   ******************** *)

(* Comatches are a lot like tuples, but with different symbols and with fields instead of variables.  We parse them differently, but once parsed we can reuse the processor function because we defined it parametrically.  *)

(* The notations for matches and comatches are very similar.  The differences are (1) comatches label each branch by a field, while matches label it by a constructor applied to pattern variables, and (2) matches can begin with a variable to match against (if not, it is a matching lambda).  This means in particular that a comatch and a matching lambda with no branches are both denoted "[]".  This is okay because both are checking, not synthesizing, so the ambiguity is resolved by whether we are checking against a function or a codatatype.  But it means we have to be careful parsing them to avoid collisions.  We define the basic notation trees for both of them to exclude the empty case, and then give a separate notation for the empty one that parses into Empty_co_match that's disambiguated later.  *)

let comatch = make "comatch" Outfix

let rec comatch_fields end_ok =
  Inner
    {
      empty_branch with
      ops =
        (if end_ok then
           TokMap.of_list
             [ (RBracket, Done_closed comatch); (Op "|", Lazy (lazy (comatch_fields true))) ]
         else TokMap.singleton (Op "|") (Lazy (lazy (comatch_fields false))));
      field =
        Some
          (op Mapsto
             (terms
                [ (Op "|", Lazy (lazy (comatch_fields true))); (RBracket, Done_closed comatch) ]));
    }

let () = set_tree comatch (Closed_entry (eop LBracket (comatch_fields false)))

let () =
  set_processor comatch
    {
      process = (fun ctx obs _ -> process_struct `Noeta (Field.Map.empty, Field.Set.empty) ctx obs);
    }

(* Comatches will be printed using the same functions that print matches (not tuples), since their "|" is treated the same as there rather than like the "," of a tuple. *)

let empty_co_match = make "empty_co_match" Outfix

let () =
  set_tree empty_co_match
    (Closed_entry
       (eop LBracket
          (ops
             [
               (RBracket, Done_closed empty_co_match);
               (Op "|", op RBracket (Done_closed empty_co_match));
             ])));
  set_processor empty_co_match { process = (fun _ _ _ -> Empty_co_match) }

(* ********************
   Matches
 ******************** *)

let mtch = make "match" Outfix

let rec mtch_branches end_ok =
  Inner
    {
      empty_branch with
      ops = (if end_ok then TokMap.of_list [ (RBracket, Done_closed mtch) ] else TokMap.empty);
      term =
        Some
          (TokMap.singleton Mapsto
             (terms [ (Op "|", Lazy (lazy (mtch_branches true))); (RBracket, Done_closed mtch) ]));
    }

let () =
  set_tree mtch
    (Closed_entry
       (eop LBracket
          (Inner
             {
               empty_branch with
               ops = TokMap.of_list [ (Op "|", mtch_branches false) ];
               term =
                 Some
                   (TokMap.of_list
                      [
                        (Op "|", mtch_branches true);
                        (RBracket, Done_closed mtch);
                        ( Mapsto,
                          terms
                            [
                              (Op "|", Lazy (lazy (mtch_branches true)));
                              (RBracket, Done_closed mtch);
                            ] );
                      ]);
             })))

let rec get_pattern :
    type n lt1 ls1 rt1 rs1.
    (string option, n) Bwv.t -> (lt1, ls1, rt1, rs1) parse -> Constr.t * n extended_ctx =
 fun ctx pat ->
  match pat with
  | Constr (c, _) -> (Constr.intern c, Extctx (Zero, ctx))
  | App { fn; arg = Ident ([ x ], _); _ } ->
      let c, Extctx (ab, ctx) = get_pattern ctx fn in
      (c, Extctx (Suc ab, Snoc (ctx, Some x)))
  | App { arg = Ident (xs, _); _ } -> fatal (Invalid_variable xs)
  | App { fn; arg = Placeholder _; _ } ->
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
  | _ -> fatal (Anomaly "invalid notation arguments for (co)match")

let () =
  set_processor mtch
    {
      process =
        (fun ctx obs _ ->
          match obs with
          (* If the first thing is a valid local variable or cube variable, then it's the match variable. *)
          | Term (Ident ([ ident ], _)) :: obs -> (
              match Bwv.find (Some ident) ctx with
              | None -> fatal (Unbound_variable ident)
              | Some x -> Match ((x, None), process_branches ctx obs))
          | Term (Ident ([ ident; fld ], _)) :: obs -> (
              match (Bwv.find (Some ident) ctx, Dim.sface_of_string fld) with
              | Some x, Some fa -> Match ((x, Some fa), process_branches ctx obs)
              | None, _ -> fatal (Unbound_variable ident)
              | _ -> fatal Parse_error)
          (* Otherwise, it's a matching lambda. *)
          | _ ->
              let branches = process_branches (Snoc (ctx, None)) obs in
              Lam (None, `Normal, Match ((Top, None), branches)));
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
      | Term (Notn n) when (equal (notn n) mtch || equal (notn n) comatch) && style = `Compact ->
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
  | _ -> fatal (Anomaly "invalid notation arguments for (co)match")

and pp_match box space ppf obs ws =
  let wslbrack, ws = take LBracket ws in
  let style = style () in
  match obs with
  | (Term (Ident _) as x) :: obs ->
      if box then pp_open_vbox ppf 0;
      if true then (
        pp_tok ppf LBracket;
        pp_ws `Nobreak ppf wslbrack;
        pp_term `None ppf x;
        let wsrbrack = pp_branches true ppf obs ws in
        if style = `Noncompact then pp_print_cut ppf ();
        pp_tok ppf RBracket;
        pp_ws space ppf wsrbrack);
      if box then pp_close_box ppf ()
  | _ ->
      let box = box || style = `Noncompact in
      if box then pp_open_vbox ppf 0;
      if true then (
        pp_tok ppf LBracket;
        pp_ws (if box then `None else `Nobreak) ppf wslbrack;
        let ws =
          match take_opt (Op "|") ws with
          | Some _ -> ws
          | None -> (Op "|", []) :: ws in
        let wsrbrack = pp_branches ((not box) || style = `Noncompact) ppf obs ws in
        if style = `Noncompact then pp_print_cut ppf ();
        pp_tok ppf RBracket;
        pp_ws space ppf wsrbrack);
      if box then pp_close_box ppf ()

(* Matches and comatches are only valid in case trees. *)
let () =
  set_print_as_case mtch (pp_match true);
  set_print_as_case comatch (pp_match true);
  set_print_as_case empty_co_match (pp_match true)

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
    |> State.add tuple
    |> State.add comatch
    |> State.add mtch
    |> State.add empty_co_match)

let run : type a. (unit -> a) -> a = fun f -> State.run_on !builtins f
