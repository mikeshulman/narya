open Util
open Dim
open Core
open Parser
open Parsing
open Term

let ([ sigma; pair ] : (Constant.t, N.two) Vec.t) = Vec.map Constant.intern [ "Sig"; "pair" ]
let ([ fst; snd ] : (Field.t, N.two) Vec.t) = Vec.map Field.intern [ "fst"; "snd" ]

module Notation = struct
  class sigma =
    object
      inherit [Fixity.right] Notation.t
      val name : string option = None
      method fixity = `Prefix
      val state : [ `Start | `Middle | `End ] = `Start
      method finished = state = `End

      method consume =
        let open ParseOps in
        match state with
        | `Start ->
            let* () = consume "(" in
            let* x = consume_var in
            let* () = consume ":" in
            return {<state = `Middle; name = x>}
        | `Middle ->
            let* () = consume ")" in
            let* () = consume "×" in
            return {<state = `End>}
        | `End -> raise (Failure "Empty notation")

      method compile args =
        let open ChoiceOps in
        let [ left; right ] = Vec.of_bwd N.two args "sigma" in
        let* lc = left.compile Emp Zero in
        let* rc = right.compile (Snoc (Emp, name)) (Suc Zero) in
        return (Raw.Synth (App (App (Const sigma, lc), Lam rc)))
    end

  class prod =
    object
      inherit [Fixity.right] Notation.t
      method fixity = `Infix
      val finis = false
      method finished = finis

      method consume =
        let open ParseOps in
        let* () = consume "×" in
        return {<finis = true>}

      method compile args =
        let open ChoiceOps in
        let [ left; right ] = Vec.of_bwd N.two args "sigma" in
        let* lc = left.compile Emp Zero in
        match lc with
        | Synth (Asc _) -> fail (* See arrow notation *)
        | _ ->
            let* rc = right.compile (Snoc (Emp, None)) (Suc Zero) in
            return (Raw.Synth (App (App (Const sigma, lc), Lam rc)))
    end

  class comma =
    object
      inherit [Fixity.right] Notation.t
      method fixity = `Infix
      val finis = false
      method finished = finis

      method consume =
        let open ParseOps in
        let* () = consume "," in
        return {<finis = true>}

      method compile args =
        let open ChoiceOps in
        let [ x; y ] = Vec.of_bwd N.two args "comma" in
        let* x = x.compile Emp Zero in
        let* y = y.compile Emp Zero in
        return (Raw.Struct (Field.Map.empty |> Field.Map.add fst x |> Field.Map.add snd y))
    end
end

let prod_scope = Scope.make "prod"
let comma_scope = Scope.make "comma"

let install () =
  Hashtbl.add Global.types sigma (Pi (UU, Pi (Pi (Var Top, UU), UU)));
  Hashtbl.add Global.types pair
    (Pi
       ( UU,
         Pi
           ( Pi (Var Top, UU),
             Pi
               ( Var (Pop Top),
                 Pi
                   ( App (Var (Pop Top), CubeOf.singleton (Var Top)),
                     App
                       ( App (Const sigma, CubeOf.singleton (Var (Pop (Pop (Pop Top))))),
                         CubeOf.singleton (Var (Pop (Pop Top))) ) ) ) ) ));
  Hashtbl.add Global.records sigma
    (Record
       {
         eta = true;
         params = N.two;
         dim = D.zero;
         dim_faces = faces_zero;
         params_plus = Suc Zero;
         fields =
           [
             (fst, Var (Pop (Pop Top)));
             (snd, App (Var (Pop Top), CubeOf.singleton (Field (Var Top, fst))));
           ];
       });
  Hashtbl.add Global.trees pair
    (Lam
       (Suc (Suc (Suc (Suc Zero))), Cobranch [ (fst, Leaf (Var (Pop Top))); (snd, Leaf (Var Top)) ]));
  Parse.rightassoc_notations :=
    !Parse.rightassoc_notations
    |> Scope.Map.add prod_scope (new Notation.sigma)
    |> Scope.Map.add prod_scope (new Notation.prod)
    |> Scope.Map.add comma_scope (new Notation.comma);
  Scope.open_scope prod_scope;
  Scope.open_scope comma_scope;
  Option.get (Scope.add_prec Scope.arrow prod_scope)
