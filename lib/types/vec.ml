open Bwd
open Bwd.Infix
open Dim
open Core
open Util
open Term
open Nat

let nil = Constr.intern "nil"
let cons = Constr.intern "cons"

let install () =
  Nat.install ();
  let vec = Scope.define "Vec" in
  let concat = Scope.define "concat" in
  let ind = Scope.define "Vec_ind" in
  Hashtbl.add Global.types vec (pi (UU D.zero) (pi (Const nn) (UU D.zero)));
  Hashtbl.add Global.constants vec
    (Data
       {
         params = N.one;
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
                         ( Const nn,
                           Ext
                             ( Var (Pop Top),
                               Ext
                                 ( App
                                     ( App (Const vec, CubeOf.singleton (Term.Var (Pop (Pop Top)))),
                                       CubeOf.singleton (Term.Var (Pop Top)) ),
                                   Emp ) ) );
                     indices =
                       Snoc
                         ( Emp,
                           Constr (suc', D.zero, Emp <: CubeOf.singleton (Term.Var (Pop (Pop Top))))
                         );
                   });
       });
  Hashtbl.add Global.types concat
    (pi (UU D.zero)
       (pi (Const nn)
          (pi (Const nn)
             (pi
                (apps (Const vec) [ Var (Pop (Pop Top)); Var (Pop Top) ])
                (pi
                   (apps (Const vec) [ Var (Pop (Pop (Pop Top))); Var (Pop Top) ])
                   (apps (Const vec)
                      [
                        Var (Pop (Pop (Pop (Pop Top))));
                        apps (Const plus) [ Var (Pop (Pop (Pop Top))); Var (Pop (Pop Top)) ];
                      ]))))));
  Hashtbl.add Global.types ind
    (pi (UU D.zero)
       (pi
          (pi (Const nn) (pi (apps (Const vec) [ Var (Pop Top); Var Top ]) (UU D.zero)))
          (pi
             (apps (Var Top) [ constr zero' Emp; constr nil Emp ])
             (pi
                (pi (Const nn)
                   (pi (Var (Pop (Pop (Pop Top))))
                      (pi
                         (apps (Const vec) [ Var (Pop (Pop (Pop (Pop Top)))); Var (Pop Top) ])
                         (pi
                            (apps (Var (Pop (Pop (Pop (Pop Top))))) [ Var (Pop (Pop Top)); Var Top ])
                            (apps (Var (Pop (Pop (Pop (Pop (Pop Top))))))
                               [
                                 constr suc' (Emp <: Var (Pop (Pop (Pop Top))));
                                 constr cons
                                   (Emp
                                   <: Var (Pop (Pop (Pop Top)))
                                   <: Var (Pop (Pop Top))
                                   <: Var (Pop Top));
                               ])))))
                (pi (Const nn)
                   (pi
                      (apps (Const vec) [ Var (Pop (Pop (Pop (Pop Top)))); Var Top ])
                      (apps (Var (Pop (Pop (Pop (Pop Top))))) [ Var (Pop Top); Var Top ])))))));
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
                                  (Case.Lam
                                     (ref
                                        (Case.Lam
                                           (ref
                                              (Case.Branches
                                                 ( Top,
                                                   Constr.Map.of_list
                                                     [
                                                       ( nil,
                                                         Case.Branch
                                                           ( Zero,
                                                             ref
                                                               (Case.Leaf
                                                                  (Var (Pop (Pop (Pop Top))))) ) );
                                                       ( cons,
                                                         Branch
                                                           ( Suc (Suc (Suc Zero)),
                                                             ref
                                                               (Case.Leaf
                                                                  (apps
                                                                     (Var
                                                                        (Pop
                                                                           (Pop
                                                                              (Pop (Pop (Pop Top))))))
                                                                     [
                                                                       Var (Pop (Pop Top));
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
                                                                                            (Pop
                                                                                               (Pop
                                                                                                  (Pop
                                                                                                    Top))))))));
                                                                           Var
                                                                             (Pop
                                                                                (Pop
                                                                                   (Pop
                                                                                      (Pop
                                                                                         (Pop
                                                                                            (Pop
                                                                                               (Pop
                                                                                                  Top)))))));
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
                                                                           Var (Pop (Pop Top));
                                                                           Var Top;
                                                                         ];
                                                                     ])) ) );
                                                     ] ))))))))))))))))
