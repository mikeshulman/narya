open Util
open Dim
open Core
open Term

let ([ stream; corec ] : (Constant.t, N.two) Vec.t) = Vec.map Constant.intern [ "Stream"; "corec" ]
let ([ head; tail ] : (Field.t, N.two) Vec.t) = Vec.map Field.intern [ "head"; "tail" ]

let install () =
  Hashtbl.add Global.types stream (pi (UU D.zero) (UU D.zero));
  Hashtbl.add Global.constants stream
    (Record
       {
         eta = false;
         params = N.one;
         dim = D.zero;
         dim_faces = faces_zero;
         params_plus = Suc Zero;
         fields =
           [ (head, Var (Pop Top)); (tail, App (Const stream, CubeOf.singleton (Var (Pop Top)))) ];
       });
  Hashtbl.add Global.types corec
    (pi ((* A : *) UU D.zero)
       (pi ((* K : *) UU D.zero)
          (pi
             ((* h : *) pi ((* k : K *) Var Top) ((*A*) Var (Pop (Pop Top))))
             (pi
                ((* t : *) pi ((* k : K *) Var (Pop Top)) ((*K*) Var (Pop (Pop Top))))
                (pi ((* k : K *) Var (Pop (Pop Top)))
                   (app (Const stream) ((*A*) Var (Pop (Pop (Pop (Pop Top)))))))))));
  Hashtbl.add Global.constants corec
    (Defined
       (Lam
          ( Suc (Suc (Suc (Suc (Suc Zero)))),
            Cobranches
              [
                (head, Leaf (app (Var (Pop (Pop Top))) (Var Top)));
                ( tail,
                  Leaf
                    (app
                       (app
                          (app
                             (app
                                (app (Const corec) (Var (Pop (Pop (Pop (Pop Top))))))
                                (Var (Pop (Pop (Pop Top)))))
                             (Var (Pop (Pop Top))))
                          (Var (Pop Top)))
                       (app (Var (Pop Top)) (Var Top))) );
              ] )))

(*
  Hashtbl.add Global.types bisim
    (Pi
       ( (* A : *) (UU D.zero),
         Pi
           ( (* K : *) (UU D.zero),
             Pi
               ( (* l : *)
                 Pi
                   ( (* k : K *) Var Top,
                     (* Stream A *) App (Const stream, CubeOf.singleton (Var (Pop (Pop Top)))) ),
                 Pi
                   ( (* r : *)
                     Pi
                       ( (* k : K *) Var (Pop Top),
                         (* Stream A *)
                         App (Const stream, CubeOf.singleton (Var (Pop (Pop (Pop Top))))) ),
                     Pi
                       ( (* h : *)
                         Pi
                           ( (* k : K *) Var (Pop (Pop Top)),
                             (* Id A (l k .head) (r k .head) *)
                             Inst
                               ( (* Id A *) Refl ((* A *) Var (Pop (Pop (Pop (Pop Top))))),
                                 TubeOf.pair
                                   (Field
                                      ( App
                                          ( (* l *) Var (Pop (Pop Top)),
                                            CubeOf.singleton ((* k *) Var Top) ),
                                        head ))
                                   (Field
                                      ( App
                                          ((* r *) Var (Pop Top), CubeOf.singleton ((* k *) Var Top)),
                                        head )) ) ),
                         Pi
                           (* TODO: Is this possible to state in general? *)
                           ( (* t : *) Sorry.e (),
                             Pi
                               ( (* k : K *) Var (Pop (Pop (Pop (Pop Top)))),
                                 (* Id (Stream A) (l k) (r k) *)
                                 Inst
                                   ( Refl
                                       ((* Stream A *)
                                          App
                                          ( Const stream,
                                            CubeOf.singleton
                                              ((* A *) Var (Pop (Pop (Pop (Pop (Pop (Pop Top)))))))
                                          )),
                                     TubeOf.pair
                                       (App
                                          ( (* l *) Var (Pop (Pop (Pop (Pop Top)))),
                                            CubeOf.singleton ((* k *) Var Top) ))
                                       (App
                                          ( (* r *) Var (Pop (Pop (Pop Top))),
                                            CubeOf.singleton ((* k *) Var Top) )) ) ) ) ) ) ) ) ))
*)
