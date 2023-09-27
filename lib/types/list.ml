open Bwd
open Bwd.Infix
open Dim
open Core
open Util
open Term

let ([ list; ind ] : (Constant.t, N.two) Vec.t) = Vec.map Constant.intern [ "List"; "List_ind" ]
let ([ nil; cons ] : (Constr.t, N.two) Vec.t) = Vec.map Constr.intern [ "nil"; "cons" ]

let install () =
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
       (Lam
          (Lam
             (Lam
                (Lam
                   (Lam
                      (Branches
                         ( Top,
                           [
                             Branch (nil, Zero, Leaf (Var (Pop (Pop Top))));
                             Branch
                               ( cons,
                                 Suc (Suc Zero),
                                 Leaf
                                   (apps (Var (Pop (Pop (Pop Top))))
                                      [
                                        Var (Pop Top);
                                        Var Top;
                                        apps (Const ind)
                                          [
                                            Var (Pop (Pop (Pop (Pop (Pop (Pop Top))))));
                                            Var (Pop (Pop (Pop (Pop (Pop Top)))));
                                            Var (Pop (Pop (Pop (Pop Top))));
                                            Var (Pop (Pop (Pop Top)));
                                            Var Top;
                                          ];
                                      ]) );
                           ] ))))))))
