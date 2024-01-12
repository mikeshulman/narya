open Dim
open Core
open Syntax
open Term
open Parser

let emp = Constr.intern "emp"
let snoc = Constr.intern "snoc"

let install () =
  let bwd = Scope.define [ "Bwd" ] in
  Hashtbl.add Global.types bwd (pi None (UU D.zero) (UU D.zero));
  Hashtbl.add Global.constants bwd
    (Data
       {
         params = Suc Zero;
         indices = Zero;
         constrs =
           Constr.Map.empty
           |> Constr.Map.add emp (Global.Constr { args = Emp; indices = Emp })
           |> Constr.Map.add snoc
                (Global.Constr
                   {
                     args =
                       Ext
                         ( None,
                           app (Const bwd) (Term.Var (Top (id_sface D.zero))),
                           Ext (None, Var (Pop (Top (id_sface D.zero))), Emp) );
                     indices = Emp;
                   });
       })
