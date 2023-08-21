open Term

let install () =
  Hashtbl.add Global.types "N" UU;
  Hashtbl.add Global.types "0" (Const "N");
  Hashtbl.add Global.types "S" (Pi (Const "N", Const "N"));
  Hashtbl.add Global.types "+" (Pi (Const "N", Pi (Const "N", Const "N")));
  Hashtbl.add Global.trees "+"
    (Lam
       ( Suc (Suc Zero),
         Branch
           ( Top,
             [
               Branch ("0", Zero, Zero, Leaf (Var (Pop Top)));
               Branch
                 ( "S",
                   Take Zero,
                   Suc Zero,
                   Leaf
                     (App
                        ( Const "S",
                          TermCube.singleton
                            (App
                               ( App (Const "+", TermCube.singleton (Var (Pop (Pop Top)))),
                                 TermCube.singleton (Var Top) )) )) );
             ] ) ))
