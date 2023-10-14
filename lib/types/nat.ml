open Bwd
open Bwd.Infix
open Util
open Dim
open Core
open Parser
open Notations
open Compile
open Term

let nn = Constant.make ()
let zero = Constant.make ()
let suc = Constant.make ()
let plus = Constant.make ()
let times = Constant.make ()
let ind = Constant.make ()
let zero' = Constr.intern "0"
let suc' = Constr.intern "1"

open Monad.Ops (Monad.Maybe)

let plusn =
  make ~name:"+" ~tightness:0. ~left:Open ~right:Open ~assoc:Left ~tree:(fun n ->
      eop (Op "+") (Done n))

let () =
  add_compiler plusn
    {
      compile =
        (fun ctx obs ->
          let x, obs = get_term obs in
          let y, obs = get_term obs in
          let () = get_done obs in
          let* x = compile ctx x in
          let* y = compile ctx y in
          return (Raw.Synth (App (App (Const plus, x), y))));
    }

let timesn =
  make ~name:"*" ~tightness:1. ~left:Open ~right:Open ~assoc:Left ~tree:(fun n ->
      eop (Op "*") (Done n))

let () =
  add_compiler timesn
    {
      compile =
        (fun ctx obs ->
          let x, obs = get_term obs in
          let y, obs = get_term obs in
          let () = get_done obs in
          let* x = compile ctx x in
          let* y = compile ctx y in
          return (Raw.Synth (App (App (Const times, x), y))));
    }

let install_notations () =
  Builtins.builtins := !Builtins.builtins |> State.add plusn |> State.add timesn

let install () =
  install_notations ();
  List.iter2 Scope.set
    [ "N"; "O"; "S"; "plus"; "times"; "N_ind" ]
    [ nn; zero; suc; plus; times; ind ];
  Hashtbl.add Global.types nn (UU D.zero);
  Hashtbl.add Global.constants nn
    (Data
       {
         params = N.zero;
         indices = Zero;
         constrs =
           Constr.Map.empty
           |> Constr.Map.add zero' (Global.Constr { args = Emp; indices = Emp })
           |> Constr.Map.add suc' (Global.Constr { args = Ext (Const nn, Emp); indices = Emp });
       });
  Hashtbl.add Global.types zero (Const nn);
  Hashtbl.add Global.constants zero (Defined (ref (Case.Leaf (Constr (zero', D.zero, Emp)))));
  Hashtbl.add Global.types suc (pi (Const nn) (Const nn));
  Hashtbl.add Global.constants suc
    (Defined
       (ref (Case.Lam (ref (Case.Leaf (Constr (suc', D.zero, Emp <: CubeOf.singleton (Var Top))))))));
  Hashtbl.add Global.types plus (pi (Const nn) (pi (Const nn) (Const nn)));
  Hashtbl.add Global.types times (pi (Const nn) (pi (Const nn) (Const nn)));
  Hashtbl.add Global.constants plus
    (Defined
       (ref
          (Case.Lam
             (ref
                (Case.Lam
                   (ref
                      (Case.Branches
                         ( Top,
                           Constr.Map.of_list
                             [
                               (zero', Case.Branch (Zero, ref (Case.Leaf (Var (Pop Top)))));
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
                                                          CubeOf.singleton (Var (Pop (Pop Top))) ),
                                                      CubeOf.singleton (Var Top) )) ))) ) );
                             ] ))))))));
  Hashtbl.add Global.constants times
    (Defined
       (ref
          (Case.Lam
             (ref
                (Case.Lam
                   (ref
                      (Case.Branches
                         ( Top,
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
                                                              CubeOf.singleton (Var (Pop (Pop Top)))
                                                            ),
                                                          CubeOf.singleton (Var Top) )) ),
                                               CubeOf.singleton (Var (Pop (Pop Top))) ))) ) );
                             ] ))))))));
  Hashtbl.add Global.types ind
    (pi
       ((* P : *) pi (Const nn) (UU D.zero))
       (pi
          ((* z : *) app (Var Top) (Const zero))
          (pi
             ((* s : *)
              pi ((* n : *) Const nn)
                (pi
                   ((* pn : *)
                    app (Var (Pop (Pop Top))) (Var Top))
                   (app (Var (Pop (Pop (Pop Top)))) (app (Const suc) (Var (Pop Top))))))
             (pi ((* n : *) Const nn) (app (Var (Pop (Pop (Pop Top)))) (Var Top))))));
  Hashtbl.add Global.constants ind
    (Defined
       (ref
          (Case.Lam
             (ref
                (Case.Lam
                   (ref
                      (Case.Lam
                         (ref
                            (Case.Lam
                               (ref
                                  (Case.Branches
                                     ( Top,
                                       Constr.Map.of_list
                                         [
                                           ( zero',
                                             Case.Branch
                                               (Zero, ref (Case.Leaf (Var (Pop (Pop Top))))) );
                                           ( suc',
                                             Branch
                                               ( Suc Zero,
                                                 ref
                                                   (Case.Leaf
                                                      (app
                                                         (app (Var (Pop (Pop Top))) (Var Top))
                                                         (app
                                                            (app
                                                               (app
                                                                  (app (Const ind)
                                                                     (Var
                                                                        (Pop (Pop (Pop (Pop Top))))))
                                                                  (Var (Pop (Pop (Pop Top)))))
                                                               (Var (Pop (Pop Top))))
                                                            (Var Top)))) ) );
                                         ] ))))))))))))
