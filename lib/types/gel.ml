open Dim
open Core
open Term

(* Gel-types, via some hardcoded basic constants.  Their types are computed by (1) writing them out comprehensibly in the Poor Man's Parser, (2) typechecking and printing the resulting Terms in the toplevel with Dim made transparent (i.e. with dim.mli temporarily moved or renamed), and (3) copy and pasting them here, removing unnecessary module qualifiers, and replacing explicit calls to Leaf and Branch with Cube.singleton and Tube.pair. *)

(* Note that the function "install" has to be called explicitly to make Gel-types available. *)

let ungel = Field.intern "ungel"
let gel = Constant.make ()

let install () =
  Scope.set "Gel" gel;
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
