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
let pair = Constant.make ()

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
  State.add_bare prodn

let install () =
  install_notations ();
  Scope.set [ "Σ" ] sigma;
  Scope.set [ "pair" ] pair;
  Hashtbl.add Global.types sigma
    (pi None (UU D.zero) (pi None (pi None (Var (Top (id_sface D.zero))) (UU D.zero)) (UU D.zero)));
  Hashtbl.add Global.types pair
    (pi None (UU D.zero)
       (pi None
          (pi None (Var (Top (id_sface D.zero))) (UU D.zero))
          (pi None
             (Var (Pop (Top (id_sface D.zero))))
             (pi None
                (app (Var (Pop (Top (id_sface D.zero)))) (Var (Top (id_sface D.zero))))
                (app
                   (app (Const sigma) (Var (Pop (Pop (Pop (Top (id_sface D.zero)))))))
                   (Var (Pop (Pop (Top (id_sface D.zero))))))))));
  Hashtbl.add Global.constants sigma
    (Record
       {
         eta = `Eta;
         params = Suc (Suc Zero);
         dim = D.zero;
         fields =
           Emp
           <: (fst, Var (Pop (Pop (Top (id_sface D.zero)))))
           <: ( snd,
                app (Var (Pop (Top (id_sface D.zero)))) (Field (Var (Top (id_sface D.zero)), fst))
              );
       });
  Hashtbl.add Global.constants pair
    (Defined
       (ref
          (Case.Lam
             ( D.zero,
               `Normal (CubeOf.singleton (Some "A")),
               ref
                 (Case.Lam
                    ( D.zero,
                      `Normal (CubeOf.singleton (Some "B")),
                      ref
                        (Case.Lam
                           ( D.zero,
                             `Normal (CubeOf.singleton (Some "a")),
                             ref
                               (Case.Lam
                                  ( D.zero,
                                    `Normal (CubeOf.singleton (Some "b")),
                                    ref
                                      (Case.Leaf
                                         (Struct
                                            ( `Eta,
                                              Emp
                                              <: ( fst,
                                                   (Var (Pop (Top (id_sface D.zero))), `Unlabeled)
                                                 )
                                              <: (snd, (Var (Top (id_sface D.zero)), `Unlabeled)) )))
                                  )) )) )) ))))
