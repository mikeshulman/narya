open Dim
open Term

let ([ nn; zero; suc; plus ] : (Constant.t, N.four) Vec.t) =
  Vec.map Constant.intern [ "N"; "0"; "S"; "+" ]

let install () =
  Hashtbl.add Global.types nn UU;
  Hashtbl.add Global.types zero (Const nn);
  Hashtbl.add Global.types suc (Pi (Const nn, Const nn));
  Hashtbl.add Global.types plus (Pi (Const nn, Pi (Const nn, Const nn)));
  Hashtbl.add Global.trees plus
    (Lam
       ( Suc (Suc Zero),
         Branch
           ( Top,
             [
               Branch (zero, Zero, Zero, Leaf (Var (Pop Top)));
               Branch
                 ( suc,
                   Take Zero,
                   Suc Zero,
                   Leaf
                     (App
                        ( Const suc,
                          CubeOf.singleton
                            (App
                               ( App (Const plus, CubeOf.singleton (Var (Pop (Pop Top)))),
                                 CubeOf.singleton (Var Top) )) )) );
             ] ) ))
