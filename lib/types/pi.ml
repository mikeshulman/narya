open Dim
open Core
open Syntax
open Term
open Parser

let pisym = Constant.make ()

let install () =
  Scope.set [ "Π" ] pisym;
  Global.add pisym
    (pi None (UU D.zero) (pi None (pi None (Var (Top (id_sface D.zero))) (UU D.zero)) (UU D.zero)))
    (Defined
       (Lam
          ( D.zero,
            `Normal (CubeOf.singleton (Some "A")),
            Lam
              ( D.zero,
                `Normal (CubeOf.singleton (Some "B")),
                Realize
                  (Pi
                     ( (* TODO: Get the variable somehow from the second argument *)
                       Some "x",
                       CubeOf.singleton (Var (Pop (Top (id_sface D.zero)))),
                       CodCube.singleton
                         (App
                            ( Var (Pop (Top (id_sface D.zero))),
                              CubeOf.singleton (Var (Top (id_sface D.zero))) )) )) ) )))
