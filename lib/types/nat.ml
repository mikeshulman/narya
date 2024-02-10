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
open Term
open Print
open Format

let nn = Constant.make ()
let nnn = Constant.make ()
let zero = Constr.intern "zero"
let suc = Constr.intern "suc"
let plus = Constant.make ()
let times = Constant.make ()
let ind = Constant.make ()
let zero' = Constant.make ()
let suc' = Constant.make ()

open Monad.Ops (Monad.Maybe)

let install () =
  Scope.set [ "ℕ" ] nn;
  Scope.set [ "Nat" ] nnn;
  Hashtbl.add Global.types nn (UU D.zero);
  Hashtbl.add Global.constants nn
    (Data
       {
         params = Zero;
         indices = Zero;
         constrs =
           Constr.Map.empty
           |> Constr.Map.add zero (Global.Constr { args = Emp; indices = Emp })
           |> Constr.Map.add suc (Global.Constr { args = Ext (None, Const nn, Emp); indices = Emp });
       });
  Hashtbl.add Global.types nnn (UU D.zero);
  Hashtbl.add Global.constants nnn (Defined (ref (Case.Leaf (Const nn))));
  ()

let plusn = make "plus" (Infixl No.zero)

let () =
  set_tree plusn (Open_entry (eop (Op "+") (done_open plusn)));
  set_processor plusn
    {
      process =
        (fun ctx obs loc _ ->
          match obs with
          | [ Term x; Term y ] ->
              let x = process ctx x in
              let y = process ctx y in
              {
                value = Raw.Synth (App ({ value = App ({ value = Const plus; loc }, x); loc }, y));
                loc;
              }
          | _ -> fatal (Anomaly "invalid notation arguments for plus"));
    };
  set_print plusn (fun space ppf obs ws ->
      match obs with
      | [ x; y ] ->
          let wsplus, ws = take (Op "+") ws in
          taken_last ws;
          pp_open_hovbox ppf 2;
          if true then (
            pp_term `Break ppf x;
            pp_tok ppf (Op "+");
            pp_ws `Nobreak ppf wsplus;
            pp_term `None ppf y);
          pp_close_box ppf ();
          pp_space ppf space
      | _ -> fatal (Anomaly "invalid notation arguments for plus"))

let timesn = make "times" (Infixl No.one)

let () =
  set_tree timesn (Open_entry (eop (Op "*") (done_open timesn)));
  set_processor timesn
    {
      process =
        (fun ctx obs loc _ ->
          match obs with
          | [ Term x; Term y ] ->
              let x = process ctx x in
              let y = process ctx y in
              {
                value = Raw.Synth (App ({ value = App ({ value = Const times; loc }, x); loc }, y));
                loc;
              }
          | _ -> fatal (Anomaly "invalid notation arguments for plus"));
    };
  set_print timesn (fun space ppf obs ws ->
      match obs with
      | [ x; y ] ->
          let wstimes, ws = take (Op "*") ws in
          taken_last ws;
          pp_open_hovbox ppf 2;
          if true then (
            pp_term `Break ppf x;
            pp_tok ppf (Op "*");
            pp_ws `Nobreak ppf wstimes;
            pp_term `None ppf y);
          pp_close_box ppf ();
          pp_space ppf space
      | _ -> fatal (Anomaly "invalid notation arguments for times"))

let install_ops () =
  List.iter2 Scope.set
    [ [ "O" ]; [ "S" ]; [ "plus" ]; [ "times" ]; [ "ℕ_ind" ] ]
    [ zero'; suc'; plus; times; ind ];
  State.S.modify
    (State.add_with_print (`Constant plus)
       { notn = Wrap plusn; pats = [ "x"; "y" ]; vals = [ "x"; "y" ] });
  State.S.modify
    (State.add_with_print (`Constant times)
       { notn = Wrap timesn; pats = [ "x"; "y" ]; vals = [ "x"; "y" ] });
  Hashtbl.add Global.types zero' (Const nn);
  Hashtbl.add Global.constants zero' (Defined (ref (Case.Leaf (Constr (zero, D.zero, Emp)))));
  Hashtbl.add Global.types suc' (pi None (Const nn) (Const nn));
  Hashtbl.add Global.constants suc'
    (Defined
       (ref
          (Case.Lam
             ( D.zero,
               `Normal (CubeOf.singleton (Some "n")),
               ref
                 (Case.Leaf
                    (Constr (suc, D.zero, Emp <: CubeOf.singleton (Var (Top (id_sface D.zero))))))
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
                                 ( zero,
                                   Case.Branch
                                     (Zero, ref (Case.Leaf (Var (Pop (Top (id_sface D.zero)))))) );
                                 ( suc,
                                   Branch
                                     ( Suc Zero,
                                       ref
                                         (Case.Leaf
                                            (Constr
                                               ( suc,
                                                 D.zero,
                                                 Snoc
                                                   ( Emp,
                                                     CubeOf.singleton
                                                       (App
                                                          ( App
                                                              ( Const plus,
                                                                CubeOf.singleton
                                                                  (Var
                                                                     (Pop
                                                                        (Pop (Top (id_sface D.zero)))))
                                                              ),
                                                            CubeOf.singleton
                                                              (Var (Top (id_sface D.zero))) )) ) )))
                                     ) );
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
                                 ( zero,
                                   Case.Branch (Zero, ref (Case.Leaf (Constr (zero, D.zero, Emp))))
                                 );
                                 ( suc,
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
          ((* z : *) app (Var (Top (id_sface D.zero))) (Constr (zero, D.zero, Emp)))
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
                      (Constr
                         ( suc,
                           D.zero,
                           Snoc (Emp, CubeOf.singleton (Var (Pop (Top (id_sface D.zero))))) )))))
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
                                               ( zero,
                                                 Case.Branch
                                                   ( Zero,
                                                     ref
                                                       (Case.Leaf
                                                          (Var (Pop (Pop (Top (id_sface D.zero))))))
                                                   ) );
                                               ( suc,
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
