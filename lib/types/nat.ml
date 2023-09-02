open Util
open Dim
open Core
open Parser
open Parsing
open Term

let ([ nn; zero; suc; plus; times; ind ] : (Constant.t, N.six) Vec.t) =
  Vec.map Constant.intern [ "N"; "O"; "S"; "plus"; "times"; "ind" ]

let plus_node = Node.make "nat_plus"
let times_node = Node.make "nat_times"
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
      let [] = Vec.of_bwd N.zero args "numeral" in
      return (numeral_of_int n)
  end

let install () =
  Hashtbl.add Global.types nn UU;
  Hashtbl.add Global.types zero (Const nn);
  Hashtbl.add Global.types suc (Pi (Const nn, Const nn));
  Hashtbl.add Global.types plus (Pi (Const nn, Pi (Const nn, Const nn)));
  Hashtbl.add Global.types times (Pi (Const nn, Pi (Const nn, Const nn)));
  Hashtbl.add Global.trees plus
    (Lam
       ( Suc (Suc Zero),
         Branch
           ( Top,
             [
               Branch (zero, Zero, Zero, Leaf (Var (Pop Top)));
               Branch
                 ( suc,
                   Take Zero,
                   Suc Zero,
                   Leaf
                     (App
                        ( Const suc,
                          CubeOf.singleton
                            (App
                               ( App (Const plus, CubeOf.singleton (Var (Pop (Pop Top)))),
                                 CubeOf.singleton (Var Top) )) )) );
             ] ) ));
  Hashtbl.add Global.trees times
    (Lam
       ( Suc (Suc Zero),
         Branch
           ( Top,
             [
               Branch (zero, Zero, Zero, Leaf (Const zero));
               Branch
                 ( suc,
                   Take Zero,
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
             ] ) ));
  Hashtbl.add Global.types ind
    (Pi
       ( (* P : *) Pi (Const nn, UU),
         Pi
           ( (* z : *) App (Var Top, CubeOf.singleton (Const zero)),
             Pi
               ( (* s : *)
                 Pi
                   ( (* n : *) Const nn,
                     Pi
                       ( (* pn : *)
                         App (Var (Pop (Pop Top)), CubeOf.singleton (Var Top)),
                         App
                           ( Var (Pop (Pop (Pop Top))),
                             CubeOf.singleton (App (Const suc, CubeOf.singleton (Var (Pop Top)))) )
                       ) ),
                 Pi ((* n : *) Const nn, App (Var (Pop (Pop (Pop Top))), CubeOf.singleton (Var Top)))
               ) ) ));
  Hashtbl.add Global.trees ind
    (Lam
       ( Suc (Suc (Suc (Suc Zero))),
         Branch
           ( Top,
             [
               Branch (zero, Zero, Zero, Leaf (Var (Pop (Pop Top))));
               Branch
                 ( suc,
                   Take Zero,
                   Suc Zero,
                   Leaf
                     (App
                        ( App (Var (Pop (Pop Top)), CubeOf.singleton (Var Top)),
                          CubeOf.singleton
                            (App
                               ( App
                                   ( App
                                       ( App
                                           ( Const ind,
                                             CubeOf.singleton (Var (Pop (Pop (Pop (Pop Top))))) ),
                                         CubeOf.singleton (Var (Pop (Pop (Pop Top)))) ),
                                     CubeOf.singleton (Var (Pop (Pop Top))) ),
                                 CubeOf.singleton (Var Top) )) )) );
             ] ) ));
  Parse.rightassoc_notations :=
    !Parse.rightassoc_notations
    |> Node.Map.add plus_node (new Notation.simple `Infix plus [ "+" ])
    |> Node.Map.add times_node (new Notation.simple `Infix times [ "*" ]);
  Option.get (Node.add_prec plus_node times_node);
  Node.open_node plus_node;
  Node.open_node times_node;
  Parse.nonassoc_notations := !Parse.nonassoc_notations |> Node.Map.add Node.max (new numeral)
