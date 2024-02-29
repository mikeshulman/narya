open Bwd
open Bwd.Infix
open Dim
open Core
open Syntax
open Term
open Nat
open Parser

let car = Field.intern "car"
let cdr = Field.intern "cdr"

let install () =
  Nat.install ();
  let covec = Scope.define [ "Covec" ] in
  Hashtbl.add Global.types covec (pi None (UU D.zero) (pi None (Const nn) (UU D.zero)));
  Hashtbl.add Global.constants covec
    (Defined
       (Lam
          ( D.zero,
            `Cube (Some "A"),
            Lam
              ( D.zero,
                `Cube (Some "n"),
                Match
                  ( Top (id_sface D.zero),
                    D.zero,
                    Constr.Map.empty
                    |> Constr.Map.add zero (Branch (Zero, Canonical (Codata (Eta, D.zero, Emp))))
                    |> Constr.Map.add suc
                         (Branch
                            ( Suc Zero,
                              Canonical
                                (Codata
                                   ( Eta,
                                     D.zero,
                                     let aa = Var (Pop (Pop (Pop (Top (id_sface D.zero))))) in
                                     let nn = Var (Pop (Top (id_sface D.zero))) in
                                     Emp <: (car, aa) <: (cdr, app (app (Const covec) aa) nn) )) ))
                  ) ) )))
