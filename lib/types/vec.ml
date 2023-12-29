open Bwd
open Bwd.Infix
open Dim
open Core
open Syntax
open Term
open Nat

let nil = Constr.intern "nil"
let cons = Constr.intern "cons"

let install () =
  Nat.install ();
  let vec = Scope.define [ "Vec" ] in
  let concat = Scope.define [ "concat" ] in
  let ind = Scope.define [ "Vec_ind" ] in
  Hashtbl.add Global.types vec (pi None (UU D.zero) (pi None (Const nn) (UU D.zero)));
  Hashtbl.add Global.constants vec
    (Data
       {
         params = Suc Zero;
         indices = Suc Zero;
         constrs =
           Constr.Map.empty
           |> Constr.Map.add nil
                (Global.Constr { args = Emp; indices = Snoc (Emp, Constr (zero', D.zero, Emp)) })
           |> Constr.Map.add cons
                (Global.Constr
                   {
                     args =
                       Ext
                         ( None,
                           Const nn,
                           Ext
                             ( None,
                               Var (Pop (Top (id_sface D.zero))),
                               Ext
                                 ( None,
                                   App
                                     ( App
                                         ( Const vec,
                                           CubeOf.singleton
                                             (Term.Var (Pop (Pop (Top (id_sface D.zero))))) ),
                                       CubeOf.singleton (Term.Var (Pop (Top (id_sface D.zero)))) ),
                                   Emp ) ) );
                     indices =
                       Snoc
                         ( Emp,
                           Constr
                             ( suc',
                               D.zero,
                               Emp
                               <: CubeOf.singleton (Term.Var (Pop (Pop (Top (id_sface D.zero))))) )
                         );
                   });
       });
  Hashtbl.add Global.types concat
    (pi None (UU D.zero)
       (pi None (Const nn)
          (pi None (Const nn)
             (pi None
                (apps (Const vec)
                   [ Var (Pop (Pop (Top (id_sface D.zero)))); Var (Pop (Top (id_sface D.zero))) ])
                (pi None
                   (apps (Const vec)
                      [
                        Var (Pop (Pop (Pop (Top (id_sface D.zero)))));
                        Var (Pop (Top (id_sface D.zero)));
                      ])
                   (apps (Const vec)
                      [
                        Var (Pop (Pop (Pop (Pop (Top (id_sface D.zero))))));
                        apps (Const plus)
                          [
                            Var (Pop (Pop (Pop (Top (id_sface D.zero)))));
                            Var (Pop (Pop (Top (id_sface D.zero))));
                          ];
                      ]))))));
  Hashtbl.add Global.types ind
    (pi None (UU D.zero)
       (pi None
          (pi None (Const nn)
             (pi None
                (apps (Const vec)
                   [ Var (Pop (Top (id_sface D.zero))); Var (Top (id_sface D.zero)) ])
                (UU D.zero)))
          (pi None
             (apps (Var (Top (id_sface D.zero))) [ constr zero' Emp; constr nil Emp ])
             (pi None
                (pi None (Const nn)
                   (pi None
                      (Var (Pop (Pop (Pop (Top (id_sface D.zero))))))
                      (pi None
                         (apps (Const vec)
                            [
                              Var (Pop (Pop (Pop (Pop (Top (id_sface D.zero))))));
                              Var (Pop (Top (id_sface D.zero)));
                            ])
                         (pi None
                            (apps
                               (Var (Pop (Pop (Pop (Pop (Top (id_sface D.zero)))))))
                               [
                                 Var (Pop (Pop (Top (id_sface D.zero))));
                                 Var (Top (id_sface D.zero));
                               ])
                            (apps
                               (Var (Pop (Pop (Pop (Pop (Pop (Top (id_sface D.zero))))))))
                               [
                                 constr suc' (Emp <: Var (Pop (Pop (Pop (Top (id_sface D.zero))))));
                                 constr cons
                                   (Emp
                                   <: Var (Pop (Pop (Pop (Top (id_sface D.zero)))))
                                   <: Var (Pop (Pop (Top (id_sface D.zero))))
                                   <: Var (Pop (Top (id_sface D.zero))));
                               ])))))
                (pi None (Const nn)
                   (pi None
                      (apps (Const vec)
                         [
                           Var (Pop (Pop (Pop (Pop (Top (id_sface D.zero))))));
                           Var (Top (id_sface D.zero));
                         ])
                      (apps
                         (Var (Pop (Pop (Pop (Pop (Top (id_sface D.zero)))))))
                         [ Var (Pop (Top (id_sface D.zero))); Var (Top (id_sface D.zero)) ])))))));
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
                                           `Normal (CubeOf.singleton (Some "k")),
                                           ref
                                             (Case.Lam
                                                ( D.zero,
                                                  `Normal (CubeOf.singleton (Some "v")),
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
                                                                              (Pop
                                                                                 (Pop
                                                                                    (Top
                                                                                       (id_sface
                                                                                          D.zero)))))))
                                                                 ) );
                                                             ( cons,
                                                               Branch
                                                                 ( Suc (Suc (Suc Zero)),
                                                                   ref
                                                                     (Case.Leaf
                                                                        (apps
                                                                           (Var
                                                                              (Pop
                                                                                 (Pop
                                                                                    (Pop
                                                                                       (Pop
                                                                                          (Pop
                                                                                             (Top
                                                                                                (id_sface
                                                                                                   D
                                                                                                   .zero))))))))
                                                                           [
                                                                             Var
                                                                               (Pop
                                                                                  (Pop
                                                                                     (Top
                                                                                        (id_sface
                                                                                           D.zero))));
                                                                             Var
                                                                               (Pop
                                                                                  (Top
                                                                                     (id_sface
                                                                                        D.zero)));
                                                                             Var
                                                                               (Top
                                                                                  (id_sface D.zero));
                                                                             apps (Const ind)
                                                                               [
                                                                                 Var
                                                                                   (Pop
                                                                                      (Pop
                                                                                         (Pop
                                                                                            (Pop
                                                                                               (Pop
                                                                                                  (Pop
                                                                                                    (
                                                                                                    Pop
                                                                                                    (
                                                                                                    Pop
                                                                                                    (
                                                                                                    Top
                                                                                                    (
                                                                                                    id_sface
                                                                                                    D
                                                                                                    .zero))))))))));
                                                                                 Var
                                                                                   (Pop
                                                                                      (Pop
                                                                                         (Pop
                                                                                            (Pop
                                                                                               (Pop
                                                                                                  (Pop
                                                                                                    (
                                                                                                    Pop
                                                                                                    (
                                                                                                    Top
                                                                                                    (
                                                                                                    id_sface
                                                                                                    D
                                                                                                    .zero)))))))));
                                                                                 Var
                                                                                   (Pop
                                                                                      (Pop
                                                                                         (Pop
                                                                                            (Pop
                                                                                               (Pop
                                                                                                  (Pop
                                                                                                    (
                                                                                                    Top
                                                                                                    (
                                                                                                    id_sface
                                                                                                    D
                                                                                                    .zero))))))));
                                                                                 Var
                                                                                   (Pop
                                                                                      (Pop
                                                                                         (Pop
                                                                                            (Pop
                                                                                               (Pop
                                                                                                  (Top
                                                                                                    (
                                                                                                    id_sface
                                                                                                    D
                                                                                                    .zero)))))));
                                                                                 Var
                                                                                   (Pop
                                                                                      (Pop
                                                                                         (Top
                                                                                            (id_sface
                                                                                               D
                                                                                               .zero))));
                                                                                 Var
                                                                                   (Top
                                                                                      (id_sface
                                                                                         D.zero));
                                                                               ];
                                                                           ])) ) );
                                                           ] )) )) )) )) )) )) ))))
