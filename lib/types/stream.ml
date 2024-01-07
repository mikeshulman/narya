open Dim
open Core
open Syntax
open Term
open Parser

let head = Field.intern "head"
let tail = Field.intern "tail"

let install () =
  let stream = Scope.define [ "Stream" ] in
  let corec = Scope.define [ "corec" ] in
  Hashtbl.add Global.types stream (pi None (UU D.zero) (UU D.zero));
  Hashtbl.add Global.constants stream
    (Record
       {
         eta = false;
         params = Suc Zero;
         dim = D.zero;
         fields =
           [
             (head, Var (Pop (Top (id_sface D.zero))));
             (tail, App (Const stream, CubeOf.singleton (Var (Pop (Top (id_sface D.zero))))));
           ];
       });
  Hashtbl.add Global.types corec
    (pi None ((* A : *) UU D.zero)
       (pi None ((* K : *) UU D.zero)
          (pi None
             ((* h : *) pi None
                ((* k : K *) Var (Top (id_sface D.zero)))
                ((*A*) Var (Pop (Pop (Top (id_sface D.zero))))))
             (pi None
                ((* t : *) pi None
                   ((* k : K *) Var (Pop (Top (id_sface D.zero))))
                   ((*K*) Var (Pop (Pop (Top (id_sface D.zero))))))
                (pi None
                   ((* k : K *) Var (Pop (Pop (Top (id_sface D.zero)))))
                   (app (Const stream) ((*A*) Var (Pop (Pop (Pop (Pop (Top (id_sface D.zero)))))))))))));
  Hashtbl.add Global.constants corec
    (Defined
       (ref
          (Case.Lam
             ( D.zero,
               `Normal (CubeOf.singleton (Some "A")),
               ref
                 (Case.Lam
                    ( D.zero,
                      `Normal (CubeOf.singleton (Some "K")),
                      ref
                        (Case.Lam
                           ( D.zero,
                             `Normal (CubeOf.singleton (Some "h")),
                             ref
                               (Case.Lam
                                  ( D.zero,
                                    `Normal (CubeOf.singleton (Some "t")),
                                    ref
                                      (Case.Lam
                                         ( D.zero,
                                           `Normal (CubeOf.singleton (Some "k")),
                                           ref
                                             (Case.Cobranches
                                                (Field.Map.of_list
                                                   [
                                                     ( head,
                                                       ref
                                                         (Case.Leaf
                                                            (app
                                                               (Var
                                                                  (Pop (Pop (Top (id_sface D.zero)))))
                                                               (Var (Top (id_sface D.zero))))) );
                                                     ( tail,
                                                       ref
                                                         (Case.Leaf
                                                            (app
                                                               (app
                                                                  (app
                                                                     (app
                                                                        (app (Const corec)
                                                                           (Var
                                                                              (Pop
                                                                                 (Pop
                                                                                    (Pop
                                                                                       (Pop
                                                                                          (Top
                                                                                             (id_sface
                                                                                                D
                                                                                                .zero))))))))
                                                                        (Var
                                                                           (Pop
                                                                              (Pop
                                                                                 (Pop
                                                                                    (Top
                                                                                       (id_sface
                                                                                          D.zero)))))))
                                                                     (Var
                                                                        (Pop
                                                                           (Pop
                                                                              (Top (id_sface D.zero))))))
                                                                  (Var (Pop (Top (id_sface D.zero)))))
                                                               (app
                                                                  (Var (Pop (Top (id_sface D.zero))))
                                                                  (Var (Top (id_sface D.zero))))))
                                                     );
                                                   ])) )) )) )) )) ))))
