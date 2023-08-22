open Dim
open Term

(* Gel-types, via some hardcoded basic constants.  Their types are computed by (1) writing them out comprehensibly in the Poor Man's Parser, (2) typechecking and printing the resulting Terms in the toplevel with Dim made transparent (i.e. with dim.mli temporarily moved or renamed), and (3) copy and pasting them here, removing unnecessary module qualifiers, and replacing explicit calls to Leaf and Branch with Cube.singleton and Tube.pair. *)

(* Note that the function "install" has to be called explicitly to make Gel-types available. *)

let install () =
  Hashtbl.add Global.types "GEL"
    (Pi
       ( UU,
         Pi
           ( UU,
             Pi
               ( Pi (Var (N.Pop N.Top), Pi (Var (N.Pop N.Top), UU)),
                 Inst (Refl UU, TubeOf.pair (Var (N.Pop (N.Pop N.Top))) (Var (N.Pop N.Top))) ) ) ));
  Hashtbl.add Global.types "gel"
    (Pi
       ( UU,
         Pi
           ( UU,
             Pi
               ( Pi (Var (N.Pop N.Top), Pi (Var (N.Pop N.Top), UU)),
                 Pi
                   ( Var (N.Pop (N.Pop N.Top)),
                     Pi
                       ( Var (N.Pop (N.Pop N.Top)),
                         Pi
                           ( App
                               ( App
                                   (Var (N.Pop (N.Pop N.Top)), CubeOf.singleton (Var (N.Pop N.Top))),
                                 CubeOf.singleton (Var N.Top) ),
                             Inst
                               ( App
                                   ( App
                                       ( App
                                           ( Const "GEL",
                                             CubeOf.singleton
                                               (Var (N.Pop (N.Pop (N.Pop (N.Pop (N.Pop N.Top))))))
                                           ),
                                         CubeOf.singleton
                                           (Var (N.Pop (N.Pop (N.Pop (N.Pop N.Top))))) ),
                                     CubeOf.singleton (Var (N.Pop (N.Pop (N.Pop N.Top)))) ),
                                 TubeOf.pair (Var (N.Pop (N.Pop N.Top))) (Var (N.Pop N.Top)) ) ) )
                   ) ) ) ));
  Hashtbl.add Global.types "ungel"
    (Pi
       ( UU,
         Pi
           ( UU,
             Pi
               ( Pi (Var (N.Pop N.Top), Pi (Var (N.Pop N.Top), UU)),
                 Pi
                   ( Var (N.Pop (N.Pop N.Top)),
                     Pi
                       ( Var (N.Pop (N.Pop N.Top)),
                         Pi
                           ( Inst
                               ( App
                                   ( App
                                       ( App
                                           ( Const "GEL",
                                             CubeOf.singleton
                                               (Var (N.Pop (N.Pop (N.Pop (N.Pop N.Top))))) ),
                                         CubeOf.singleton (Var (N.Pop (N.Pop (N.Pop N.Top)))) ),
                                     CubeOf.singleton (Var (N.Pop (N.Pop N.Top))) ),
                                 TubeOf.pair (Var (N.Pop N.Top)) (Var N.Top) ),
                             App
                               ( App
                                   ( Var (N.Pop (N.Pop (N.Pop N.Top))),
                                     CubeOf.singleton (Var (N.Pop (N.Pop N.Top))) ),
                                 CubeOf.singleton (Var (N.Pop N.Top)) ) ) ) ) ) ) ));
  Hashtbl.add Global.trees "ungel"
    (Lam
       ( Suc (Suc (Suc (Suc (Suc (Suc Zero))))),
         Branch
           ( Top,
             [
               Branch ("gel", Take (Omit (Omit (Omit (Omit (Omit Zero))))), Suc Zero, Leaf (Var Top));
             ] ) ));
  (* Maybe this would be better implemented as an eta-rule for GEL *)
  Hashtbl.add Global.trees "gel"
    (Lam
       ( Suc (Suc (Suc (Suc (Suc (Suc Zero))))),
         Branch
           ( Top,
             [
               Branch
                 ("ungel", Take (Omit (Omit (Omit (Omit (Omit Zero))))), Suc Zero, Leaf (Var Top));
             ] ) ))
