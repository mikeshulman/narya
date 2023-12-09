open Util
open Dim
open Core
open Reporter
open Parser
open Notation
open Postprocess
open Raw
open Term

let sigma = Constant.make ()
let fst = Field.intern "fst"
let snd = Field.intern "snd"
let pair = Constant.make ()

open Monad.Ops (Monad.Maybe)

(* TODO: printing these notations *)

let prodn = make "prod" (Infixr No.one)

let () =
  set_tree prodn (Open_entry (eops [ (Ident "×", done_open prodn); (Op "><", done_open prodn) ]));
  set_processor prodn
    {
      process =
        (fun ctx obs ->
          let x, Term a, Term b =
            match obs with
            | [ one; b ] -> (
                match one with
                | Term (Notn n) when equal (notn n) Builtins.parens -> (
                    match args n with
                    | [ Term (Notn n) ] when equal (notn n) Builtins.asc -> (
                        match args n with
                        | [ Term (Ident x); Term a ] -> (Some x, Term a, b)
                        | [ Term Placeholder; Term a ] -> (None, Term a, b)
                        | _ -> (None, one, b))
                    | _ -> (None, one, b))
                | _ -> (None, one, b))
            | _ -> fatal (Anomaly "invalid notation arguments for sigma") in
          let a = process ctx a in
          let b = process (Snoc (ctx, x)) b in
          Synth (App (App (Const sigma, a), Lam (x, `Normal, b))));
    }

let comma = make "comma" (Infixr No.one)

let () =
  set_tree comma (Open_entry (eop (Op ",") (done_open comma)));
  set_processor comma
    {
      process =
        (fun ctx obs ->
          match obs with
          | [ Term x; Term y ] ->
              let x = process ctx x in
              let y = process ctx y in
              Raw.Struct (Field.Map.of_list [ (fst, [ x ]); (snd, [ y ]) ])
          | _ -> fatal (Anomaly "invalid notation arguments for sigma"));
    }

let installed = ref false

let install_notations () =
  if not !installed then (
    installed := true;
    Builtins.builtins := !Builtins.builtins |> State.add prodn |> State.add comma)

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
