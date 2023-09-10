open Bwd
open Bwd.Infix
open Util
open Dim
open Core
open Parser
open Parsing
open Term

let ([ nn; zero; suc; plus; times; ind ] : (Constant.t, N.six) Util.Vec.t) =
  Util.Vec.map Constant.intern [ "N"; "O"; "S"; "plus"; "times"; "N_ind" ]

let ([ zero'; suc' ] : (Constr.t, N.two) Util.Vec.t) = Util.Vec.map Constr.intern [ "O"; "S" ]

module Nodes = struct
  let plus = Node.make "nat_plus"
  let times = Node.make "nat_times"
end

let num = Token.compile "^(0|[1-9][0-9]*)$"

let rec numeral_of_int = function
  | 0 -> Raw.Synth (Const zero)
  | n when n > 0 -> Synth (App (Const suc, numeral_of_int (n - 1)))
  | _ -> raise (Failure "Negative numeral")

class numeral =
  object
    inherit [Fixity.non] Notation.t
    method fixity = `Outfix
    val finis = false
    method finished = finis
    val n = 0

    method consume =
      let open ParseOps in
      let* str = consume_ident in
      let* () = guard (Pcre.pmatch ~rex:num str) in
      return {<finis = true; n = int_of_string str>}

    method compile args =
      let open ChoiceOps in
      let [] = Util.Vec.of_bwd N.zero args "numeral" in
      return (numeral_of_int n)
  end

let install () =
  Hashtbl.add Global.types nn (UU D.zero);
  Hashtbl.add Global.constants nn
    (Data
       {
         params = N.zero;
         indices = Zero;
         constrs =
           Constr.Map.empty
           |> Constr.Map.add zero' (Global.Constr { args = Emp; indices = Emp })
           |> Constr.Map.add suc' (Global.Constr { args = Ext (Const nn, Emp); indices = Emp });
       });
  Hashtbl.add Global.types zero (Const nn);
  Hashtbl.add Global.constants zero (Defined (Leaf (Constr (zero', D.zero, Emp))));
  Hashtbl.add Global.types suc (pi (Const nn) (Const nn));
  Hashtbl.add Global.constants suc
    (Defined (Lam (Suc Zero, Leaf (Constr (suc', D.zero, Emp <: CubeOf.singleton (Var Top))))));
  Hashtbl.add Global.types plus (pi (Const nn) (pi (Const nn) (Const nn)));
  Hashtbl.add Global.types times (pi (Const nn) (pi (Const nn) (Const nn)));
  Hashtbl.add Global.constants plus
    (Defined
       (Lam
          ( Suc (Suc Zero),
            Branches
              ( Top,
                [
                  Branch (zero', Zero, Leaf (Var (Pop Top)));
                  Branch
                    ( suc',
                      Suc Zero,
                      Leaf
                        (App
                           ( Const suc,
                             CubeOf.singleton
                               (App
                                  ( App (Const plus, CubeOf.singleton (Var (Pop (Pop Top)))),
                                    CubeOf.singleton (Var Top) )) )) );
                ] ) )));
  Hashtbl.add Global.constants times
    (Defined
       (Lam
          ( Suc (Suc Zero),
            Branches
              ( Top,
                [
                  Branch (zero', Zero, Leaf (Const zero));
                  Branch
                    ( suc',
                      Suc Zero,
                      Leaf
                        (App
                           ( App
                               ( Const plus,
                                 CubeOf.singleton
                                   (App
                                      ( App (Const times, CubeOf.singleton (Var (Pop (Pop Top)))),
                                        CubeOf.singleton (Var Top) )) ),
                             CubeOf.singleton (Var (Pop (Pop Top))) )) );
                ] ) )));
  Hashtbl.add Global.types ind
    (pi
       ((* P : *) pi (Const nn) (UU D.zero))
       (pi
          ((* z : *) app (Var Top) (Const zero))
          (pi
             ((* s : *)
              pi ((* n : *) Const nn)
                (pi
                   ((* pn : *)
                    app (Var (Pop (Pop Top))) (Var Top))
                   (app (Var (Pop (Pop (Pop Top)))) (app (Const suc) (Var (Pop Top))))))
             (pi ((* n : *) Const nn) (app (Var (Pop (Pop (Pop Top)))) (Var Top))))));
  Hashtbl.add Global.constants ind
    (Defined
       (Lam
          ( Suc (Suc (Suc (Suc Zero))),
            Branches
              ( Top,
                [
                  Branch (zero', Zero, Leaf (Var (Pop (Pop Top))));
                  Branch
                    ( suc',
                      Suc Zero,
                      Leaf
                        (app
                           (app (Var (Pop (Pop Top))) (Var Top))
                           (app
                              (app
                                 (app
                                    (app (Const ind) (Var (Pop (Pop (Pop (Pop Top))))))
                                    (Var (Pop (Pop (Pop Top)))))
                                 (Var (Pop (Pop Top))))
                              (Var Top))) );
                ] ) )));
  Parse.rightassoc_notations :=
    !Parse.rightassoc_notations
    |> Node.Map.add Nodes.plus (new Notation.simple `Infix plus [ "+" ])
    |> Node.Map.add Nodes.times (new Notation.simple `Infix times [ "*" ]);
  Option.get (Node.add_prec Nodes.plus Nodes.times);
  Parse.nonassoc_notations := !Parse.nonassoc_notations |> Node.Map.add Node.max (new numeral)
