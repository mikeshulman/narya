open Bwd
open Bwd.Infix
open Dim
open Core
open Term

let nil = Constr.intern "nil"
let cons = Constr.intern "cons"

let install () =
  let list = Scope.define [ "List" ] in
  let ind = Scope.define [ "List_ind" ] in
  Hashtbl.add Global.types list (pi None (UU D.zero) (UU D.zero));
  Hashtbl.add Global.constants list
    (Data
       {
         params = Suc Zero;
         indices = Zero;
         constrs =
           Constr.Map.empty
           |> Constr.Map.add nil (Global.Constr { args = Emp; indices = Emp })
           |> Constr.Map.add cons
                (Global.Constr
                   {
                     args =
                       Ext
                         ( None,
                           Var (Top (id_sface D.zero)),
                           Ext (None, app (Const list) (Term.Var (Pop (Top (id_sface D.zero)))), Emp)
                         );
                     indices = Emp;
                   });
       });
  Hashtbl.add Global.types ind
    (pi None (UU D.zero)
       (pi None
          (pi None (app (Const list) (Var (Top (id_sface D.zero)))) (UU D.zero))
          (pi None
             (app (Var (Top (id_sface D.zero))) (constr nil Emp))
             (pi None
                (pi None
                   (Var (Pop (Pop (Top (id_sface D.zero)))))
                   (pi None
                      (app (Const list) (Var (Pop (Pop (Pop (Top (id_sface D.zero)))))))
                      (pi None
                         (app
                            (Var (Pop (Pop (Pop (Top (id_sface D.zero))))))
                            (Var (Top (id_sface D.zero))))
                         (app
                            (Var (Pop (Pop (Pop (Pop (Top (id_sface D.zero)))))))
                            (constr cons
                               (Emp
                               <: Var (Pop (Pop (Top (id_sface D.zero))))
                               <: Var (Pop (Top (id_sface D.zero)))))))))
                (pi None
                   (app (Const list) (Var (Pop (Pop (Pop (Top (id_sface D.zero)))))))
                   (app
                      (Var (Pop (Pop (Pop (Top (id_sface D.zero))))))
                      (Var (Top (id_sface D.zero)))))))));
  Hashtbl.add Global.constants ind
    (Defined
       (ref
          (Case.Lam
             ( D.zero,
               `Normal (CubeOf.singleton (Some "A")),
               ref
                 (Case.Lam
                    ( D.zero,
                      `Normal (CubeOf.singleton (Some "P")),
                      ref
                        (Case.Lam
                           ( D.zero,
                             `Normal (CubeOf.singleton (Some "n")),
                             ref
                               (Case.Lam
                                  ( D.zero,
                                    `Normal (CubeOf.singleton (Some "c")),
                                    ref
                                      (Case.Lam
                                         ( D.zero,
                                           `Normal (CubeOf.singleton (Some "l")),
                                           ref
                                             (Case.Branches
                                                ( Top (id_sface D.zero),
                                                  D.zero,
                                                  Constr.Map.of_list
                                                    [
                                                      ( nil,
                                                        Case.Branch
                                                          ( Zero,
                                                            ref
                                                              (Case.Leaf
                                                                 (Var
                                                                    (Pop
                                                                       (Pop (Top (id_sface D.zero))))))
                                                          ) );
                                                      ( cons,
                                                        Branch
                                                          ( Suc (Suc Zero),
                                                            ref
                                                              (Case.Leaf
                                                                 (apps
                                                                    (Var
                                                                       (Pop
                                                                          (Pop
                                                                             (Pop
                                                                                (Top
                                                                                   (id_sface D.zero))))))
                                                                    [
                                                                      Var
                                                                        (Pop (Top (id_sface D.zero)));
                                                                      Var (Top (id_sface D.zero));
                                                                      apps (Const ind)
                                                                        [
                                                                          Var
                                                                            (Pop
                                                                               (Pop
                                                                                  (Pop
                                                                                     (Pop
                                                                                        (Pop
                                                                                           (Pop
                                                                                              (Top
                                                                                                 (id_sface
                                                                                                    D
                                                                                                    .zero))))))));
                                                                          Var
                                                                            (Pop
                                                                               (Pop
                                                                                  (Pop
                                                                                     (Pop
                                                                                        (Pop
                                                                                           (Top
                                                                                              (id_sface
                                                                                                 D
                                                                                                 .zero)))))));
                                                                          Var
                                                                            (Pop
                                                                               (Pop
                                                                                  (Pop
                                                                                     (Pop
                                                                                        (Top
                                                                                           (id_sface
                                                                                              D.zero))))));
                                                                          Var
                                                                            (Pop
                                                                               (Pop
                                                                                  (Pop
                                                                                     (Top
                                                                                        (id_sface
                                                                                           D.zero)))));
                                                                          Var
                                                                            (Top (id_sface D.zero));
                                                                        ];
                                                                    ])) ) );
                                                    ] )) )) )) )) )) ))))
