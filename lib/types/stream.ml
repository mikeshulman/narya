open Bwd
open Bwd.Infix
open Dim
open Core
open Syntax
open Term
open Parser

let head = Field.intern "head"
let tail = Field.intern "tail"

let install () =
  let stream = Scope.define [ "Stream" ] in
  Global.add stream (pi None (UU D.zero) (UU D.zero))
    (Defined
       (Lam
          ( D.zero,
            `Cube (Some "A"),
            Canonical
              (Codata
                 ( Noeta,
                   D.zero,
                   Emp
                   <: (head, Var (Pop (Top (id_sface D.zero))))
                   <: ( tail,
                        App (Const stream, CubeOf.singleton (Var (Pop (Top (id_sface D.zero))))) )
                 )) )))
