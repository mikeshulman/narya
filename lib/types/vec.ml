open Bwd
open Bwd.Infix
open Dim
open Core
open Syntax
open Term
open Nat
open Parser

let nil = Constr.intern "nil"
let cons = Constr.intern "cons"

let install () =
  Nat.install ();
  let vec = Scope.define [ "Vec" ] in
  Hashtbl.add Global.types vec (pi None (UU D.zero) (pi None (Const nn) (UU D.zero)));
  Hashtbl.add Global.constants vec
    (Data
       {
         params = Suc Zero;
         indices = Suc Zero;
         constrs =
           Constr.Map.empty
           |> Constr.Map.add nil
                (Dataconstr { args = Emp; indices = Snoc (Emp, Constr (zero, D.zero, Emp)) })
           |> Constr.Map.add cons
                (Dataconstr
                   {
                     args =
                       Ext
                         ( None,
                           Const nn,
                           Ext
                             ( None,
                               Var (Pop (Top (id_sface D.zero))),
                               Ext
                                 ( None,
                                   App
                                     ( App
                                         ( Const vec,
                                           CubeOf.singleton
                                             (Term.Var (Pop (Pop (Top (id_sface D.zero))))) ),
                                       CubeOf.singleton (Term.Var (Pop (Top (id_sface D.zero)))) ),
                                   Emp ) ) );
                     indices =
                       Snoc
                         ( Emp,
                           Constr
                             ( suc,
                               D.zero,
                               Emp
                               <: CubeOf.singleton (Term.Var (Pop (Pop (Top (id_sface D.zero))))) )
                         );
                   });
       })
