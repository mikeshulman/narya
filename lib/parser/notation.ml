(* This module should not be opened, but used qualified. *)

open Util
open Core
open Parsing
open ParseOps
open Bwd
open Raw

(* ********************
   Notations
   *********************)

(* The parse subtrees of a notation object are passed as callbacks, to which it can supply a list of further variables to bind therein. *)
type 'm subterm = {
  compile : 'n 'mn. (string option, 'n) Bwv.t -> ('m, 'n, 'mn) N.plus -> 'mn check Choice.t;
}

(* A notation is an immutable object whose state stores what it has parsed so far and remains to parse.  The "initial" version stored in the configuration is totally unparsed. *)
class virtual ['fixity] t =
  object (_ : 'notn)
    method virtual fixity : 'fixity
    method virtual finished : bool

    (* Consume some number of tokens, if they are the next notation parts of this notation, returning an updated notation state. *)
    method virtual consume : 'notn Parsing.t

    (* Once all the inputs of this notation are parsed (into callbacks), assemble them into a term. *)
    method virtual compile : 'n. 'n subterm Bwd.t -> 'n check Choice.t
  end

(* A simple notation denotes the application of a single constant to a fixed number of arguments, in order and delimited by single tokens, without repeats or variable binding. *)
class ['fixity] simple (fix : 'fixity) (c : Constant.t) (parts : string list) =
  object
    inherit ['fixity] t
    val parts = parts
    method fixity = fix
    method finished = parts = []

    method consume =
      match parts with
      | [] -> raise (Failure "Empty notation")
      | next :: rest ->
          let* _ = consume next in
          return {<parts = rest>}

    method compile : type n. n subterm Bwd.t -> n check Choice.t =
      fun args ->
        let open ChoiceOps in
        let* (), res =
          let open
            Mbwd.Monadic
              (Monad.StateT
                 (Choice)
                 (struct
                   type t = n synth
                 end)) in
          miterM
            (fun [ x ] f ->
              let* xc = x.compile Emp Zero in
              return ((), App (f, xc)))
            [ args ] (Const c) in
        return (Synth res)
  end

(* TODO: Better error-handling.  When a notation gets started parsing but fails to complete, it could generate an error message that gets stored in the parsing monad.  Then if parsing fails completely, we can give the user at least some information about what failed. *)

type non = Fixity.non t
type left = Fixity.left t
type right = Fixity.right t
type any = Any : 'fixity t -> any

(* Once we have a parse tree, we can compile it into a term, in the presence of a namespace resolving strings to variables. *)
let rec compile : type n. (string option, n) Bwv.t -> any Tree.t -> n check Choice.t =
 fun ctx tr ->
  let open ChoiceOps in
  match tr with
  | Leaf name -> (
      match Bwv.index (Some name) ctx with
      (* If a string is a variable in the context, we return that. *)
      | Some x -> return (Synth (Var x))
      | None ->
          (* If it is a constant with a global definition, we return that.  Otherwise, parsing fails. *)
          let c = Constant.intern name in
          if Hashtbl.mem Global.types c then return (Synth (Const (Constant.intern name))) else fail
      )
  | Node (Any notn, children) ->
      notn#compile
        (Bwd.map (fun t -> { compile = (fun vs p -> compile (Bwv.append p ctx vs) t) }) children)

(* ********************
   Builtin notations
   ******************** *)

(* A general class for paired delimeters such as "(" and ")". *)
class parens opn cls =
  object
    inherit [Fixity.non] t
    method fixity = `Outfix
    val parts = [ opn; cls ]
    method finished = parts = []

    method consume =
      match parts with
      | [] -> raise (Failure "Empty notation")
      | next :: rest ->
          let* _ = consume next in
          return {<parts = rest>}

    method compile args =
      let [ arg ] = Vec.of_bwd N.one args "parens" in
      arg.compile Emp Zero
  end

(*
class default =
  object
    inherit [Fixity.non] t
    method fixity = `Outfix
    val finis = false
    method finished = finis

    method consume =
      let* _ = consume "{" in
      let* _ = consume "}" in
      return {<finis = true>}

  end
*)

(*
class uvar =
  object
    inherit [Fixity.non] t
    method fixity = `Outfix
    val finis = false
    method finished = finis

    method consume =
      let* _ = consume "_" in
      return {<finis = true>}

  end
*)

class field =
  object
    inherit [Fixity.left] t
    method fixity = `Postfix
    val name = ""
    val finis = false
    method finished = finis

    method consume =
      let* name = consume_field in
      return {<finis = true; name>}

    method compile args =
      let open ChoiceOps in
      let [ arg ] = Vec.of_bwd N.one args "field" in
      let* ac = arg.compile Emp Zero in
      match ac with
      | Synth acs -> return (Synth (Field (acs, Field.intern name)))
      | _ -> fail
  end

class arrow =
  object
    inherit [Fixity.right] t
    method fixity = `Infix
    val finis = false
    method finished = finis

    method consume =
      let* () = consume "→" <|> consume "->" in
      return {<finis = true>}

    method compile args =
      let open ChoiceOps in
      let [ dom; cod ] = Vec.of_bwd N.two args "arrow" in
      let* dc = dom.compile Emp Zero in
      match dc with
      (* Ascriptions are not allowed in the domain of an arrow.  No one should ever need to do this, and forbidding it prevents an ambiguity in parsing "(A : Type) → B" when there is already a variable in the context named A. *)
      | Synth (Asc _) -> fail
      | _ ->
          let* cc = cod.compile (Snoc (Emp, None)) (Suc Zero) in
          return (Synth (Pi (dc, cc)))
  end

class lambda =
  object (_ : 'notn)
    inherit [Fixity.right] t
    val names : string option Bwd.t = Emp
    method fixity = `Prefix
    val finis = false
    method finished = finis

    method consume =
      let rec consume_vars : string option Bwd.t -> 'notn Parsing.t =
       fun vars ->
        (let* x = consume_var in
         consume_vars (Snoc (vars, x)))
        <|> let* _ = consume "↦" <|> consume "|->" in
            let* _ = guard (vars <> Emp) in
            return {<names = vars; finis = true>} in
      consume_vars Emp

    method compile args =
      let open ChoiceOps in
      let [ body ] = Vec.of_bwd N.one args "lambda" in
      let (Wrap names) = Bwv.of_bwd names in
      let (Plus p) = Bwv.plus_length names in
      let* bc = body.compile names p in
      return (raw_lam p bc)
  end

class application =
  object
    inherit [Fixity.left] t
    method fixity = `Infix
    val finis = false
    method finished = finis
    method consume = return {<finis = true>}

    method compile args =
      let open ChoiceOps in
      let [ fn; arg ] = Vec.of_bwd N.two args "application" in
      let* fc = fn.compile Emp Zero in
      let* ac = arg.compile Emp Zero in
      match fc with
      | Synth (Symbol (syn, (Suc _ as n), xs)) ->
          return (Synth (Symbol (syn, N.suc_plus'' n, Snoc (xs, ac))))
      | Synth sfn -> return (Synth (App (sfn, ac)))
      | _ -> fail
  end

class ascription =
  object
    inherit [Fixity.non] t
    method fixity = `Infix
    val finis = false
    method finished = finis

    method consume =
      let* () = consume ":" in
      return {<finis = true>}

    method compile args =
      let open ChoiceOps in
      let [ tm; asc ] = Vec.of_bwd N.two args "ascription" in
      let* tc = tm.compile Emp Zero in
      let* ac = asc.compile Emp Zero in
      return (Synth (Asc (tc, ac)))
  end

class pi =
  object (self)
    inherit [Fixity.right] t
    val state : [ `Start | `Explicit | `Implicit | `Default | `End ] = `Start

    val names : ([ `Explicit | `Implicit | `Default ] * [ `New | `Repeat ] * string option) Bwd.t =
      Emp

    method fixity = `Prefix
    method finished = state = `End

    method consume_vars label rep =
      (let* x = consume_var in
       {<names = Snoc (names, (label, rep, x))>}#consume_vars label `Repeat)
      <|> let* () = consume ":" in
          let* () = guard (rep = `Repeat) in
          return self

    method consume_start =
      (let* () = consume "(" in
       {<state = `Explicit>}#consume_vars `Explicit `New)
      <|> let* () = consume "{" in
          {<state = `Implicit>}#consume_vars `Implicit `New

    method consume =
      match state with
      | `Start -> self#consume_start
      | `Explicit ->
          let* () = consume ")" in
          self#consume_start
          <|> let* () = consume "→" <|> consume "->" in
              return {<state = `End>}
      | `Implicit -> (
          (let* () = consume "}" in
           self#consume_start
           <|> let* () = consume "→" <|> consume "->" in
               return {<state = `End>})
          <|> let* () = consume "≔" <|> consume ":=" in
              match names with
              | Snoc (rest, (`Implicit, `New, x)) ->
                  return {<state = `Default; names = Snoc (rest, (`Default, `New, x))>}
              | Snoc (_, _) -> fail
              | _ -> raise (Failure "missing variables in pi"))
      | `Default ->
          let* () = consume "}" in
          self#consume_start
          <|> let* () = consume "→" <|> consume "->" in
              return {<state = `End>}
      | `End -> raise (Failure "Empty notation")

    method compile args =
      let open ChoiceOps in
      let rec compile_doms :
          type a b ab.
          ([ `Explicit | `Implicit | `Default ] * [ `New | `Repeat ] * string option, b) Bwv.t ->
          (a, b, ab) N.plus ->
          a subterm Bwd.t ->
          ab check ->
          a check Choice.t =
       fun names ab doms cod ->
        match (names, ab, doms) with
        | Emp, Zero, Emp -> return cod
        | Snoc (_, (`Implicit, _, _)), _, _ | Snoc (_, (`Default, _, _)), _, _ ->
            fail (* Not yet implemented *)
        | Snoc (names, (`Explicit, rep, _)), Suc ab, Snoc (doms', dom) ->
            let newctx = Bwv.map (fun (_, _, x) -> x) names in
            let* dom = dom.compile newctx ab in
            compile_doms names ab
              (match rep with
              | `New -> doms'
              | `Repeat -> doms)
              (Synth (Pi (dom, cod)))
        | _ -> raise (Failure "Mismatch in Pi") in
      let (Wrap names) = Bwv.of_bwd names in
      let (Plus ab) = Bwv.plus_length names in
      let newctx = Bwv.map (fun (_, _, x) -> x) names in
      match args with
      | Emp -> raise (Failure "No codomain in Pi")
      | Snoc (doms, cod) ->
          let* cod = cod.compile newctx ab in
          compile_doms names ab doms cod
  end

class symbol name n syn =
  object
    inherit [Fixity.non] t
    method fixity = `Outfix
    val finis = false
    method finished = finis

    method consume =
      let* () = consume name in
      return {<finis = true>}

    method compile args =
      let open ChoiceOps in
      let [] = Vec.of_bwd N.zero args "symbol" in
      return (Synth (Symbol (syn, N.zero_plus n, Emp)))
  end

class struc =
  object
    inherit [Fixity.non] t
    method fixity = `Outfix
    val state : [ `Start | `Middle | `End ] = `Start
    val fields : Field.t Bwd.t = Emp
    method finished = state = `End

    method consume =
      match state with
      | `Start ->
          let* () = consume "{" in
          (let* fld = consume_fieldname in
           let* () = consume "≔" <|> consume ":=" in
           return {<state = `Middle; fields = Snoc (Emp, Field.intern fld)>})
          <|> let* () = consume "}" in
              return {<state = `End>}
      | `Middle ->
          (let* () = consume ";" in
           let* fld = consume_fieldname in
           let* () = consume "≔" <|> consume ":=" in
           return {<state = `Middle; fields = Snoc (fields, Field.intern fld)>})
          <|> let* () = consume "}" in
              return {<state = `End>}
      | `End -> raise (Failure "Empty notation")

    method compile : type n. n subterm Bwd.t -> n check Choice.t =
      fun args ->
        let module M =
          Monad.StateT
            (Choice)
            (struct
              type t = n check Field.Map.t
            end)
        in
        let open Mbwd.Monadic (M) in
        let open ChoiceOps in
        let* (), flds =
          miterM
            (fun [ fld; arg ] ->
              let open Monad.Ops (M) in
              let* map = M.get in
              let* arg = M.stateless (arg.compile Emp Zero) in
              let* () = M.put (Field.Map.add fld arg map) in
              return ())
            [ fields; args ] Field.Map.empty in
        return (Struct flds)
  end

class letin =
  object
    inherit [Fixity.right] t
    method fixity = `Prefix
    val state : [ `Start | `Type | `Value | `End ] = `Start
    val typed = false
    val name : string option = None
    method finished = state = `End

    method consume =
      match state with
      | `Start ->
          let* () = consume "let" in
          let* name = consume_var in
          (let* () = consume "≔" <|> consume ":=" in
           return {<state = `Value; name>})
          <|>
          let* () = consume ":" in
          return {<state = `Type; name; typed = true>}
      | `Type ->
          let* () = consume "≔" <|> consume ":=" in
          return {<state = `Value>}
      | `Value ->
          let* () = consume "in" in
          return {<state = `End>}
      | `End -> raise (Failure "Empty notation")

    method compile args =
      let open ChoiceOps in
      let* carg, body =
        if typed then
          let [ ty; arg; body ] = Vec.of_bwd N.three args "typed let-in" in
          let* cty = ty.compile Emp Zero in
          let* carg = arg.compile Emp Zero in
          return (Synth (Asc (carg, cty)), body)
        else
          let [ arg; body ] = Vec.of_bwd N.two args "let-in" in
          let* carg = arg.compile Emp Zero in
          return (carg, body) in
      let* cbody = body.compile (Snoc (Emp, name)) (Suc Zero) in
      match (carg, cbody) with
      | Synth sarg, Synth sbody -> return (Synth (Let (sarg, sbody)))
      | _ -> fail
  end
