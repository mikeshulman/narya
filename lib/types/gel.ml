open Dim
open Core
open Syntax
open Term
open Parser

let ungel = Field.intern "ungel"
let gel = Constant.make ()

let install () =
  Scope.set [ "Gel" ] gel;
  Hashtbl.add Global.types gel
    (pi None (UU D.zero)
       (pi None (UU D.zero)
          (pi None
             (pi None
                (Var (Pop (Top (id_sface D.zero))))
                (pi None (Var (Pop (Top (id_sface D.zero)))) (UU D.zero)))
             (Inst
                ( Act (UU D.zero, refl),
                  TubeOf.pair
                    (Var (Pop (Pop (Top (id_sface D.zero)))))
                    (Var (Pop (Top (id_sface D.zero)))) )))));
  Hashtbl.add Global.constants gel
    (Record
       {
         eta = true;
         params = Suc (Suc (Suc Zero));
         dim = one;
         fields =
           [
             ( ungel,
               app
                 (app (Var (Pop (Top (id_sface D.zero)))) (Var (Top zero_sface_one)))
                 (Var (Top one_sface_one)) );
           ];
       })
