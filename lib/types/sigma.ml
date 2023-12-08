open Util
open Dim
open Core
open Reporter
open Parser
open Notation
open Compile
open Raw
open Term

let sigma = Constant.make ()
let fst = Field.intern "fst"
let snd = Field.intern "snd"
let pair = Constant.make ()

open Monad.Ops (Monad.Maybe)

(* TODO: printing these notations *)

let sigman = make "sigma" (Prefixr No.one)

let () =
  set_tree sigman
    (Closed_entry
       (eop LParen
          (ident
             (op Colon
                (term RParen
                   (ops [ (Ident "×", Done_closed sigman); (Op "><", Done_closed sigman) ]))))));
  set_compiler sigman
    {
      compile =
        (fun ctx obs ->
          match obs with
          | [ Term x; Term tm; Term ty ] ->
              let x =
                match x with
                | Ident x -> Some x
                | Placeholder -> None
                | _ -> fatal Parse_error in
              let tm = compile ctx tm in
              let ty = compile (Snoc (ctx, x)) ty in
              Synth (App (App (Const sigma, tm), Lam (`Normal, ty)))
          | _ -> fatal (Anomaly "invalid notation arguments for sigma"));
    }

let prodn = make "prod" (Infixr No.one)

let () =
  set_tree prodn (Open_entry (eops [ (Ident "×", done_open prodn); (Op "><", done_open prodn) ]));
  set_compiler prodn
    {
      compile =
        (fun ctx obs ->
          match obs with
          | [ Term tm; Term ty ] ->
              let tm = compile ctx tm in
              let ty = compile (Snoc (ctx, None)) ty in
              Synth (App (App (Const sigma, tm), Lam (`Normal, ty)))
          | _ -> fatal (Anomaly "invalid notation arguments for sigma"));
    }

let comma = make "comma" (Infixr No.one)

let () =
  set_tree comma (Open_entry (eop (Op ",") (done_open comma)));
  set_compiler comma
    {
      compile =
        (fun ctx obs ->
          match obs with
          | [ Term x; Term y ] ->
              let x = compile ctx x in
              let y = compile ctx y in
              Raw.Struct (Field.Map.of_list [ (fst, [ x ]); (snd, [ y ]) ])
          | _ -> fatal (Anomaly "invalid notation arguments for sigma"));
    }

let installed = ref false

let install_notations () =
  if not !installed then (
    installed := true;
    Builtins.builtins :=
      !Builtins.builtins |> State.add sigman |> State.add prodn |> State.add comma)

let install () =
  install_notations ();
  Scope.set "Σ" sigma;
  Scope.set "pair" pair;
  Hashtbl.add Global.types sigma
    (pi (UU D.zero) (pi (pi (Var (Top (id_sface D.zero))) (UU D.zero)) (UU D.zero)));
  Hashtbl.add Global.types pair
    (pi (UU D.zero)
       (pi
          (pi (Var (Top (id_sface D.zero))) (UU D.zero))
          (pi
             (Var (Pop (Top (id_sface D.zero))))
             (pi
                (app (Var (Pop (Top (id_sface D.zero)))) (Var (Top (id_sface D.zero))))
                (app
                   (app (Const sigma) (Var (Pop (Pop (Pop (Top (id_sface D.zero)))))))
                   (Var (Pop (Pop (Top (id_sface D.zero))))))))));
  Hashtbl.add Global.constants sigma
    (Record
       {
         eta = true;
         params = Suc (Suc Zero);
         dim = D.zero;
         fields =
           [
             (fst, Var (Pop (Pop (Top (id_sface D.zero)))));
             ( snd,
               app (Var (Pop (Top (id_sface D.zero)))) (Field (Var (Top (id_sface D.zero)), fst)) );
           ];
       });
  Hashtbl.add Global.constants pair
    (Defined
       (ref
          (Case.Lam
             ( D.zero,
               ref
                 (Case.Lam
                    ( D.zero,
                      ref
                        (Case.Lam
                           ( D.zero,
                             ref
                               (Case.Lam
                                  ( D.zero,
                                    ref
                                      (Case.Leaf
                                         (Struct
                                            (Field.Map.empty
                                            |> Field.Map.add fst (Var (Pop (Top (id_sface D.zero))))
                                            |> Field.Map.add snd (Var (Top (id_sface D.zero)))))) ))
                           )) )) ))))
