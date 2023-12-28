open Bwd
open Bwd.Infix
open Util
open Dim
open Core
open Reporter
open Parser
open Notation
open Postprocess
open Term

let nn = Constant.make ()
let zero = Constant.make ()
let suc = Constant.make ()
let plus = Constant.make ()
let times = Constant.make ()
let ind = Constant.make ()
let zero' = Constr.intern "zero"
let suc' = Constr.intern "suc"

open Monad.Ops (Monad.Maybe)

let plusn = make "plus" (Infixl No.zero)

let () =
  set_tree plusn (Open_entry (eop (Op "+") (done_open plusn)));
  set_processor plusn
    {
      process =
        (fun ctx obs ->
          match obs with
          | [ Term x; Term y ] ->
              let x = process ctx x in
              let y = process ctx y in
              Raw.Synth (App (App (Const plus, x), y))
          | _ -> fatal (Anomaly "invalid notation arguments for plus"));
    };
  set_print plusn (fun ppf obs ->
      match obs with
      | [ x; y ] -> Format.fprintf ppf "@[<hov 2>%a@ + %a@]" Print.pp_term x Print.pp_term y
      | _ -> fatal (Anomaly "invalid notation arguments for plus"))

let timesn = make "times" (Infixl No.one)

let () =
  set_tree timesn (Open_entry (eop (Op "*") (done_open timesn)));
  set_processor timesn
    {
      process =
        (fun ctx obs ->
          match obs with
          | [ Term x; Term y ] ->
              let x = process ctx x in
              let y = process ctx y in
              Raw.Synth (App (App (Const times, x), y))
          | _ -> fatal (Anomaly "invalid notation arguments for plus"));
    };
  set_print timesn (fun ppf obs ->
      match obs with
      | [ x; y ] -> Format.fprintf ppf "@[<hov 2>%a@ * %a@]" Print.pp_term x Print.pp_term y
      | _ -> fatal (Anomaly "invalid notation arguments for plus"))

let installed = ref false

let install_notations () =
  State.add_const plusn plus 2;
  State.add_const timesn times 2

let install () =
  install_notations ();
  List.iter2 Scope.set
    [ [ "N" ]; [ "O" ]; [ "S" ]; [ "plus" ]; [ "times" ]; [ "N_ind" ] ]
    [ nn; zero; suc; plus; times; ind ];
  Hashtbl.add Global.types nn (UU D.zero);
  Hashtbl.add Global.constants nn
    (Data
       {
         params = Zero;
         indices = Zero;
         constrs =
           Constr.Map.empty
           |> Constr.Map.add zero' (Global.Constr { args = Emp; indices = Emp })
           |> Constr.Map.add suc'
                (Global.Constr { args = Ext (None, Const nn, Emp); indices = Emp });
       });
  Hashtbl.add Global.types zero (Const nn);
  Hashtbl.add Global.constants zero (Defined (ref (Case.Leaf (Constr (zero', D.zero, Emp)))));
  Hashtbl.add Global.types suc (pi None (Const nn) (Const nn));
  Hashtbl.add Global.constants suc
    (Defined
       (ref
          (Case.Lam
             ( D.zero,
               `Normal (CubeOf.singleton (Some "n")),
               ref
                 (Case.Leaf
                    (Constr (suc', D.zero, Emp <: CubeOf.singleton (Var (Top (id_sface D.zero))))))
             ))));
  Hashtbl.add Global.types plus (pi None (Const nn) (pi None (Const nn) (Const nn)));
  Hashtbl.add Global.types times (pi None (Const nn) (pi None (Const nn) (Const nn)));
  Hashtbl.add Global.constants plus
    (Defined
       (ref
          (Case.Lam
             ( D.zero,
               `Normal (CubeOf.singleton (Some "x")),
               ref
                 (Case.Lam
                    ( D.zero,
                      `Normal (CubeOf.singleton (Some "y")),
                      ref
                        (Case.Branches
                           ( Top (id_sface D.zero),
                             D.zero,
                             Constr.Map.of_list
                               [
                                 ( zero',
                                   Case.Branch
                                     (Zero, ref (Case.Leaf (Var (Pop (Top (id_sface D.zero)))))) );
                                 ( suc',
                                   Branch
                                     ( Suc Zero,
                                       ref
                                         (Case.Leaf
                                            (App
                                               ( Const suc,
                                                 CubeOf.singleton
                                                   (App
                                                      ( App
                                                          ( Const plus,
                                                            CubeOf.singleton
                                                              (Var
                                                                 (Pop (Pop (Top (id_sface D.zero)))))
                                                          ),
                                                        CubeOf.singleton
                                                          (Var (Top (id_sface D.zero))) )) ))) ) );
                               ] )) )) ))));
  Hashtbl.add Global.constants times
    (Defined
       (ref
          (Case.Lam
             ( D.zero,
               `Normal (CubeOf.singleton (Some "x")),
               ref
                 (Case.Lam
                    ( D.zero,
                      `Normal (CubeOf.singleton (Some "y")),
                      ref
                        (Case.Branches
                           ( Top (id_sface D.zero),
                             D.zero,
                             Constr.Map.of_list
                               [
                                 (zero', Case.Branch (Zero, ref (Case.Leaf (Const zero))));
                                 ( suc',
                                   Branch
                                     ( Suc Zero,
                                       ref
                                         (Case.Leaf
                                            (App
                                               ( App
                                                   ( Const plus,
                                                     CubeOf.singleton
                                                       (App
                                                          ( App
                                                              ( Const times,
                                                                CubeOf.singleton
                                                                  (Var
                                                                     (Pop
                                                                        (Pop (Top (id_sface D.zero)))))
                                                              ),
                                                            CubeOf.singleton
                                                              (Var (Top (id_sface D.zero))) )) ),
                                                 CubeOf.singleton
                                                   (Var (Pop (Pop (Top (id_sface D.zero))))) ))) )
                                 );
                               ] )) )) ))));
  Hashtbl.add Global.types ind
    (pi None
       ((* P : *) pi None (Const nn) (UU D.zero))
       (pi None
          ((* z : *) app (Var (Top (id_sface D.zero))) (Const zero))
          (pi None
             ((* s : *)
              pi None ((* n : *) Const nn)
                (pi None
                   ((* pn : *)
                    app
                      (Var (Pop (Pop (Top (id_sface D.zero)))))
                      (Var (Top (id_sface D.zero))))
                   (app
                      (Var (Pop (Pop (Pop (Top (id_sface D.zero))))))
                      (app (Const suc) (Var (Pop (Top (id_sface D.zero))))))))
             (pi None ((* n : *) Const nn)
                (app (Var (Pop (Pop (Pop (Top (id_sface D.zero)))))) (Var (Top (id_sface D.zero))))))));
  Hashtbl.add Global.constants ind
    (Defined
       (ref
          (Case.Lam
             ( D.zero,
               `Normal (CubeOf.singleton (Some "P")),
               ref
                 (Case.Lam
                    ( D.zero,
                      `Normal (CubeOf.singleton (Some "z")),
                      ref
                        (Case.Lam
                           ( D.zero,
                             `Normal (CubeOf.singleton (Some "s")),
                             ref
                               (Case.Lam
                                  ( D.zero,
                                    `Normal (CubeOf.singleton (Some "pn")),
                                    ref
                                      (Case.Branches
                                         ( Top (id_sface D.zero),
                                           D.zero,
                                           Constr.Map.of_list
                                             [
                                               ( zero',
                                                 Case.Branch
                                                   ( Zero,
                                                     ref
                                                       (Case.Leaf
                                                          (Var (Pop (Pop (Top (id_sface D.zero))))))
                                                   ) );
                                               ( suc',
                                                 Branch
                                                   ( Suc Zero,
                                                     ref
                                                       (Case.Leaf
                                                          (app
                                                             (app
                                                                (Var
                                                                   (Pop
                                                                      (Pop (Top (id_sface D.zero)))))
                                                                (Var (Top (id_sface D.zero))))
                                                             (app
                                                                (app
                                                                   (app
                                                                      (app (Const ind)
                                                                         (Var
                                                                            (Pop
                                                                               (Pop
                                                                                  (Pop
                                                                                     (Pop
                                                                                        (Top
                                                                                           (id_sface
                                                                                              D.zero))))))))
                                                                      (Var
                                                                         (Pop
                                                                            (Pop
                                                                               (Pop
                                                                                  (Top
                                                                                     (id_sface
                                                                                        D.zero)))))))
                                                                   (Var
                                                                      (Pop
                                                                         (Pop
                                                                            (Top (id_sface D.zero))))))
                                                                (Var (Top (id_sface D.zero)))))) )
                                               );
                                             ] )) )) )) )) ))))
