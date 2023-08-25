open Dim
open Term

let ([ sigma; pair ] : (Constant.t, N.two) Vec.t) = Vec.map Constant.intern [ "Sig"; "pair" ]
let ([ fst; snd ] : (Field.t, N.two) Vec.t) = Vec.map Field.intern [ "fst"; "snd" ]

let install () =
  Hashtbl.add Global.types sigma (Pi (UU, Pi (Pi (Var Top, UU), UU)));
  Hashtbl.add Global.types pair
    (Pi
       ( UU,
         Pi
           ( Pi (Var Top, UU),
             Pi
               ( Var (Pop Top),
                 Pi
                   ( App (Var (Pop Top), CubeOf.singleton (Var Top)),
                     App
                       ( App (Const sigma, CubeOf.singleton (Var (Pop (Pop (Pop Top))))),
                         CubeOf.singleton (Var (Pop (Pop Top))) ) ) ) ) ));
  Hashtbl.add Global.records sigma
    (Record
       {
         eta = true;
         params = N.two;
         dim = D.zero;
         dim_faces = faces_zero;
         params_plus = Suc Zero;
         fields =
           [
             (fst, Var (Pop (Pop Top)));
             (snd, App (Var (Pop Top), CubeOf.singleton (Field (Var Top, fst))));
           ];
       });
  Hashtbl.add Global.trees pair
    (Lam
       (Suc (Suc (Suc (Suc Zero))), Cobranch [ (fst, Leaf (Var (Pop Top))); (snd, Leaf (Var Top)) ]))
