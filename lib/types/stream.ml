open Dim
open Core
open Term

let head = Field.intern "head"
let tail = Field.intern "tail"

let install () =
  let stream = Scope.define "Stream" in
  let corec = Scope.define "corec" in
  Hashtbl.add Global.types stream (pi (UU D.zero) (UU D.zero));
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
    (pi ((* A : *) UU D.zero)
       (pi ((* K : *) UU D.zero)
          (pi
             ((* h : *) pi
                ((* k : K *) Var (Top (id_sface D.zero)))
                ((*A*) Var (Pop (Pop (Top (id_sface D.zero))))))
             (pi
                ((* t : *) pi
                   ((* k : K *) Var (Pop (Top (id_sface D.zero))))
                   ((*K*) Var (Pop (Pop (Top (id_sface D.zero))))))
                (pi
                   ((* k : K *) Var (Pop (Pop (Top (id_sface D.zero)))))
                   (app (Const stream) ((*A*) Var (Pop (Pop (Pop (Pop (Top (id_sface D.zero)))))))))))));
  Hashtbl.add Global.constants corec
    (Defined
       (ref
          (Case.Lam
             ( D.zero,
               ref
                 (Case.Lam
                    ( D.zero,
                      ref
                        (Case.Lam
                           ( D.zero,
                             ref
                               (Case.Lam
                                  ( D.zero,
                                    ref
                                      (Case.Lam
                                         ( D.zero,
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
