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
  Hashtbl.add Global.types stream (pi None (UU D.zero) (UU D.zero));
  Hashtbl.add Global.constants stream
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
