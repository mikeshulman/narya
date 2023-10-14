open Util
open Dim
open Core
open Term

(* Gel-types, via some hardcoded basic constants.  Their types are computed by (1) writing them out comprehensibly in the Poor Man's Parser, (2) typechecking and printing the resulting Terms in the toplevel with Dim made transparent (i.e. with dim.mli temporarily moved or renamed), and (3) copy and pasting them here, removing unnecessary module qualifiers, and replacing explicit calls to Leaf and Branch with Cube.singleton and Tube.pair. *)

(* Note that the function "install" has to be called explicitly to make Gel-types available. *)

let ungel = Field.intern "ungel"

let install () =
  let gel = Scope.define "Gel" in
  Hashtbl.add Global.types gel
    (pi (UU D.zero)
       (pi (UU D.zero)
          (pi
             (pi (Var (N.Pop N.Top)) (pi (Var (N.Pop N.Top)) (UU D.zero)))
             (Inst
                (Act (UU D.zero, refl), TubeOf.pair (Var (N.Pop (N.Pop N.Top))) (Var (N.Pop N.Top)))))));
  Hashtbl.add Global.constants gel
    (Record
       {
         eta = true;
         params = N.three;
         dim = one;
         dim_faces = faces_one;
         params_plus = Suc (Suc (Suc Zero));
         fields =
           [ (ungel, app (app (Var (Pop (Pop (Pop Top)))) (Var (Pop (Pop Top)))) (Var (Pop Top))) ];
       })
