open Util
open Dim
open Core
open Parser
open Parsing
open Term

let ([ sigma; pair ] : (Constant.t, N.two) Vec.t) = Vec.map Constant.intern [ "Σ"; "pair" ]
let ([ fst; snd ] : (Field.t, N.two) Vec.t) = Vec.map Field.intern [ "fst"; "snd" ]

module Nodes = struct
  let prod = Node.make "prod"
  let comma = Node.make "comma"
end

module Notations = struct
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

let install () =
  Hashtbl.add Global.types sigma (pi (UU D.zero) (pi (pi (Var Top) (UU D.zero)) (UU D.zero)));
  Hashtbl.add Global.types pair
    (pi (UU D.zero)
       (pi (pi (Var Top) (UU D.zero))
          (pi (Var (Pop Top))
             (pi (app (Var (Pop Top)) (Var Top))
                (app (app (Const sigma) (Var (Pop (Pop (Pop Top))))) (Var (Pop (Pop Top))))))));
  Hashtbl.add Global.constants sigma
    (Record
       {
         eta = true;
         params = N.two;
         dim = D.zero;
         dim_faces = faces_zero;
         params_plus = Suc Zero;
         fields = [ (fst, Var (Pop (Pop Top))); (snd, app (Var (Pop Top)) (Field (Var Top, fst))) ];
       });
  Hashtbl.add Global.constants pair
    (Defined
       (Lam
          ( N.zero_plus N.four,
            Leaf
              (Struct
                 (Field.Map.empty
                 |> Field.Map.add fst (Var (Pop Top))
                 |> Field.Map.add snd (Var Top))) )));
  Parse.rightassoc_notations :=
    !Parse.rightassoc_notations
    |> Node.Map.add Nodes.prod (new Notations.sigma)
    |> Node.Map.add Nodes.prod (new Notations.prod)
    |> Node.Map.add Nodes.comma (new Notations.comma);
  Option.get (Node.add_prec Node.arrow Nodes.prod)
