open Bwd
open Bwd.Infix
open Util
open Dim
open Core
open Reporter
open Parser
open Notation
open Postprocess
open Syntax
open Raw
open Term
open Print
open Format

let sigma = Constant.make ()
let fst = Field.intern "fst"
let snd = Field.intern "snd"

open Monad.Ops (Monad.Maybe)

let prodn = make "prod" (Infixr No.one)

let () =
  set_tree prodn
    (Open_entry (eops [ (Ident [ "×" ], done_open prodn); (Op "><", done_open prodn) ]));
  set_processor prodn
    {
      process =
        (fun ctx obs loc _ ->
          let x, Term a, Term b =
            match obs with
            | [ one; b ] -> (
                match one with
                | Term { value = Notn n; _ } when equal (notn n) Builtins.parens -> (
                    match args n with
                    | [ Term { value = Notn n; _ } ] when equal (notn n) Builtins.asc -> (
                        match args n with
                        | [ Term { value = Ident ([ x ], _); _ }; Term a ] -> (Some x, Term a, b)
                        | [ Term { value = Placeholder _; _ }; Term a ] -> (None, Term a, b)
                        | _ -> (None, one, b))
                    | _ -> (None, one, b))
                | _ -> (None, one, b))
            | _ -> fatal (Anomaly "invalid notation arguments for sigma") in
          let a = process ctx a in
          let b = process (Snoc (ctx, x)) b in
          {
            value =
              Synth
                (App
                   ( { value = App ({ value = Const sigma; loc }, a); loc },
                     { value = Lam (x, `Normal, b); loc } ));
            loc;
          });
    };
  set_print prodn (fun space ppf obs ws ->
      match obs with
      | [ x; y ] ->
          let wsprod, ws = Option.value (take_opt (Ident [ "×" ]) ws) ~default:(take (Op "><") ws) in
          taken_last ws;
          pp_open_hovbox ppf 2;
          if true then (
            pp_term `Break ppf x;
            (* TODO: Can we let the user define unicode/ascii equivalent pairs? *)
            Uuseg_string.pp_utf_8 ppf (Printconfig.alt_char "×" "><");
            pp_ws `Nobreak ppf wsprod;
            pp_term space ppf y);
          pp_close_box ppf ()
      | _ -> fatal (Anomaly "invalid notation arguments for prod"))

let install_notations () =
  (* TODO: How to unparse into a binding notation? *)
  State.Current.add prodn

let install () =
  install_notations ();
  Scope.set [ "Σ" ] sigma;
  Global.add sigma
    (pi None (UU D.zero) (pi None (pi None (Var (Top (id_sface D.zero))) (UU D.zero)) (UU D.zero)))
    (Defined
       (Lam
          ( D.zero,
            `Cube (Some "A"),
            Lam
              ( D.zero,
                `Cube (Some "B"),
                Canonical
                  (Codata
                     ( Eta,
                       D.zero,
                       Emp
                       <: (fst, Var (Pop (Pop (Top (id_sface D.zero)))))
                       <: ( snd,
                            app
                              (Var (Pop (Top (id_sface D.zero))))
                              (Field (Var (Top (id_sface D.zero)), fst)) ) )) ) )))
