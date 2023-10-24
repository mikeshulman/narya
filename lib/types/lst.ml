open Bwd
open Bwd.Infix
open Dim
open Core
open Util
open Term

let nil = Constr.intern "nil"
let cons = Constr.intern "cons"

let install () =
  let list = Scope.define "List" in
  let ind = Scope.define "List_ind" in
  Hashtbl.add Global.types list (pi (UU D.zero) (UU D.zero));
  Hashtbl.add Global.constants list
    (Data
       {
         params = N.one;
         indices = Zero;
         constrs =
           Constr.Map.empty
           |> Constr.Map.add nil (Global.Constr { args = Emp; indices = Emp })
           |> Constr.Map.add cons
                (Global.Constr
                   {
                     args = Ext (Var Top, Ext (app (Const list) (Term.Var (Pop Top)), Emp));
                     indices = Emp;
                   });
       });
  Hashtbl.add Global.types ind
    (pi (UU D.zero)
       (pi
          (pi (app (Const list) (Var Top)) (UU D.zero))
          (pi
             (app (Var Top) (constr nil Emp))
             (pi
                (pi (Var (Pop (Pop Top)))
                   (pi
                      (app (Const list) (Var (Pop (Pop (Pop Top)))))
                      (pi
                         (app (Var (Pop (Pop (Pop Top)))) (Var Top))
                         (app (Var (Pop (Pop (Pop (Pop Top)))))
                            (constr cons (Emp <: Var (Pop (Pop Top)) <: Var (Pop Top)))))))
                (pi
                   (app (Const list) (Var (Pop (Pop (Pop Top)))))
                   (app (Var (Pop (Pop (Pop Top)))) (Var Top)))))));
  Hashtbl.add Global.constants ind
    (Defined
       (ref
          (Case.Lam
             ( faces_zero,
               Suc Zero,
               ref
                 (Case.Lam
                    ( faces_zero,
                      Suc Zero,
                      ref
                        (Case.Lam
                           ( faces_zero,
                             Suc Zero,
                             ref
                               (Case.Lam
                                  ( faces_zero,
                                    Suc Zero,
                                    ref
                                      (Case.Lam
                                         ( faces_zero,
                                           Suc Zero,
                                           ref
                                             (Case.Branches
                                                ( Top,
                                                  Constr.Map.of_list
                                                    [
                                                      ( nil,
                                                        Case.Branch
                                                          ( Zero,
                                                            ref (Case.Leaf (Var (Pop (Pop Top)))) )
                                                      );
                                                      ( cons,
                                                        Branch
                                                          ( Suc (Suc Zero),
                                                            ref
                                                              (Case.Leaf
                                                                 (apps (Var (Pop (Pop (Pop Top))))
                                                                    [
                                                                      Var (Pop Top);
                                                                      Var Top;
                                                                      apps (Const ind)
                                                                        [
                                                                          Var
                                                                            (Pop
                                                                               (Pop
                                                                                  (Pop
                                                                                     (Pop
                                                                                        (Pop
                                                                                           (Pop Top))))));
                                                                          Var
                                                                            (Pop
                                                                               (Pop
                                                                                  (Pop
                                                                                     (Pop (Pop Top)))));
                                                                          Var
                                                                            (Pop
                                                                               (Pop (Pop (Pop Top))));
                                                                          Var (Pop (Pop (Pop Top)));
                                                                          Var Top;
                                                                        ];
                                                                    ])) ) );
                                                    ] )) )) )) )) )) ))))
