open Util
open Bwd
open Notations
open Compile
open Fmlib_parse

let msg (_ : string) = ()
(* let msg s = Printf.printf "%s" s *)

module Res = struct
  type t = res
end

module Parse_term = struct
  module Basic = Token_parser.Make (State) (Token) (Res) (Unit)
  open Basic

  let name : res t =
    step "name" (fun state _ tok ->
        match tok with
        | Name x ->
            msg (Printf.sprintf "Found name %s in name\n" x);
            Some (Name x, state)
        | _ -> None)

  let constr : res t =
    step "constr" (fun state _ tok ->
        match tok with
        | Constr x -> if Token.variableable x then Some (Constr x, state) else None
        | _ -> None)

  let field : res t =
    step "field" (fun state _ tok ->
        match tok with
        | Field x -> if Token.variableable x then Some (Field x, state) else None
        | _ -> None)

  let numeral : res t =
    step "numeral" (fun state _ tok ->
        match tok with
        | Numeral n -> (
            match Float.of_string_opt n with
            | Some n -> Some (Numeral n, state)
            | None -> None)
        | _ -> None)

  let rec tree_op (ops : tree TokMap.t) (obs : observation Bwd.t) :
      (observation Bwd.t * Notation.t) t =
    let* optree =
      msg (Printf.sprintf "Looking for op in tree\n");
      step "operator" (fun state _ tok ->
          let open Monad.Ops (Monad.Maybe) in
          let* br = TokMap.find_opt tok ops in
          msg (Printf.sprintf "Found op %s in tree\n" (Token.to_string tok));
          return (br, state)) in
    tree optree obs

  and tree_name (name : tree option) (obs : observation Bwd.t) : (observation Bwd.t * Notation.t) t
      =
    let* nametree, x =
      msg (Printf.sprintf "Looking for name in tree\n");
      step "name" (fun state _ tok ->
          match (name, tok) with
          | Some br, Name x ->
              msg (Printf.sprintf "Found name %s in tree\n" x);
              if Token.variableable x then Some ((br, Some x), state) else None
          | Some br, Underscore ->
              msg (Printf.sprintf "Found name _ in tree\n");
              Some ((br, None), state)
          | _ -> None) in
    tree nametree (Snoc (obs, Name x))

  and tree_term (term : tree TokMap.t option) (fail : string list) (obs : observation Bwd.t) :
      (observation Bwd.t * Notation.t) t =
    match term with
    | Some e ->
        msg (Printf.sprintf "Looking for term\n");
        (* This is an *interior* term, so it has no tightness restrictions on what notations can occur inside, and is ended by the specified ending tokens. *)
        let* subterm = lclosed Interval.entire e in
        tree_op e (Snoc (obs, Term subterm))
    | None -> unexpected ("failure " ^ String.concat ", " fail)

  and tree (t : tree) (obs : observation Bwd.t) : (observation Bwd.t * Notation.t) t =
    msg (Printf.sprintf "tree\n");
    match t with
    | Inner { ops; name; term; fail } ->
        backtrack (tree_op ops obs) "operator"
        </> backtrack (tree_name name obs) "name"
        </> tree_term term fail obs
    | Done n -> return (obs, n)
    | Flag (f, t) -> tree t (Snoc (obs, Flag f))
    | Lazy (lazy t) -> tree t obs

  and entry (e : entry) : (observation Bwd.t * Notation.t) t = tree_op e Emp

  (* "lclosed" is passed an upper tightness interval and an additional set of ending ops (stored as a map, since that's how they occur naturally, but here we ignore the values and look only at the keys).  It parses an arbitrary left-closed tree (pre-merged).  The interior terms are calls to "lclosed" with the next ops passed as the ending ones. *)
  and lclosed (tight : Interval.t) (stop : tree TokMap.t) : res t =
    msg (Printf.sprintf "lclosed\n");
    let* state = get in
    let* res, res_tight =
      (msg (Printf.sprintf "Looking in left_closeds\n");
       let* obs, n = entry state.left_closeds in
       let d = get_data n in
       msg (Printf.sprintf "Finished op %s\n" d.name);
       (* If the parse ended right-open, we call "lclosed" again, with the upper tightness interval starting at the tightness of the just-parsed notation, closed if that notation is right-associative and open otherwise, to pick up the open argument. *)
       match d.right with
       | Closed -> return (Notn (n, Bwd.to_list obs), None)
       | Open ->
           let i = Interval.right_assoc d.tightness d.assoc in
           (* Note that the tightness here is that of the notation n, not the "tight" from the surrounding one that called lclosed.  Thus, if while parsing a right-open argument of some operator X we see a left-closed, right-open notation Z of *lower* tightness than X, we allow it, and it does not end if we encounter the start of a left-open notation Y of tightness in between X and Z, only if we see something of lower tightness than Z, or a stop-token from an *enclosing* notation (otherwise we wouldn't be able to delimit right-open operators by parentheses). *)
           let* last_arg = lclosed i stop in
           return (Notn (n, Bwd.to_list (Snoc (obs, Term last_arg))), Some d.tightness))
      (* If parsing a left-closed notation fails, we can instead parse an abstraction, a single variable name, a numeral, or a constructor.  Field projections are not allowed since this would be the head of a spine. *)
      </> backtrack (abstraction stop Emp) "abstraction"
      </> let* res = name </> numeral </> constr in
          return (res, None) in
    (* Then "lclosed" ends by calling "lopen" with its interval and ending ops, and also its own result (with extra argument added if necessary).  Note that we don't incorporate d.tightness here; it is only used to find the delimiter of the right-hand argument if the notation we parsed was right-open.  In particular, therefore, a right-closed notation can be followed by anything, even a left-open notation that binds tighter than it does; the only restriction is if we're inside the right-hand argument of some containing right-open notation, so we inherit a "tight" from there.  *)
    let* r = lopen tight stop res res_tight in
    msg (Printf.sprintf "end of lclosed\n");
    return r

  (* If we see a variable name or an underscore, there's a chance that it's actually the beginning of an abstraction.  Thus, we pick up as many variable names as possible and look for a mapsto afterwards. *)
  and abstraction (stop : tree TokMap.t) (names : string option Bwd.t) : (res * float option) t =
    let* x =
      step "name" (fun state _ tok ->
          match tok with
          | Name x -> if Token.variableable x then Some (`Name x, state) else None
          | Underscore -> Some (`Underscore, state)
          | Mapsto -> Some (`Mapsto, state)
          | _ -> None) in
    match x with
    | `Name x ->
        msg (Printf.sprintf "Found name %s in abstraction\n" x);
        abstraction stop (Snoc (names, Some x))
    | `Underscore -> abstraction stop (Snoc (names, None))
    | `Mapsto -> (
        match names with
        | Emp -> unexpected "\"↦\""
        | Snoc _ ->
            (* An abstraction should be thought of as having −∞ tightness, so we allow almost anything at all to its right.  Except, of course, for the stop-tokens currently in effect, since we we need to be able to delimit an abstraction by parentheses or other right-closed notations.  Moreover, we make it *not* "right-associative", i.e. the tightness interval is open, so that operators of actual tightness −∞ (such as type ascription ":") can *not* appear undelimited inside it.  This is intentional: I feel that "x ↦ M : A" is inherently ambiguous and should be required to be parenthesized one way or the other.  (The other possible parsing of the unparenthesized version is disallowed because : is not left-associative, so it can't contain an abstraction to its left.) *)
            let* res = lclosed (Open Float.neg_infinity) stop in
            return (Abs (Bwd.to_list names, res), Some Float.neg_infinity))

  (* "lopen" is passed an upper tightness interval and a set of ending ops, plus a parsed result for the left open argument and the tightness of the outermost notation in that argument if it is right-open. *)
  and lopen (tight : Interval.t) (stop : tree TokMap.t) (first_arg : res)
      (first_tight : float option) : res t =
    msg (Printf.sprintf "lopen\n");
    (* We start by looking ahead one token.  If we see one of the specified ending ops, or the initial op of a left-open tree with looser tightness than the lower endpoint of the current interval (with strictness determined by the tree in question), we return the result argument without parsing any more.  Note that the order matters, in case the next token could have more than one role.  Ending ops are tested first, which means that if a certain operator could end an "inner term" in an outer containing notation, it always does, even if it could also be interpreted as some infix notation inside that inner term. *)
    followed_by
      (step "stopping token (1)" (fun state _ tok ->
           if TokMap.mem tok stop then Some (first_arg, state) else None))
      "stopping token (2)"
    (* Next we test for initial ops of looser left-opens.  If a certain token could be the initial op of more than one left-open, we stop here if *any* of those is looser; we don't backtrack and try other possibilities.  So the rule is that if multiple notations start with the same token, the looser one is used preferentially in cases when it matters.  (In cases where it doesn't matter, i.e. they would both be allowed at the same grouping relative to other notations, we can proceed to parse a merged tree containing both of them and decide later which one it is.)  *)
    </> followed_by
          (step "looser left-open (1)" (fun state _ tok ->
               let open Monad.Ops (Monad.Maybe) in
               let* ivls = TokMap.find_opt tok state.left_opens in
               if List.exists (fun ivl -> Interval.contains ivl (Interval.endpoint tight)) ivls then
                 return (first_arg, state)
               else None))
          "looser left-open (2)"
    </> (* Otherwise, we parse either an arbitrary left-closed tree (applying the given result to it as a function) or an arbitrary left-open tree with tightness in the given interval (passing the given result as the starting open argument).  Interior terms are treated as in "lclosed".  *)
    (let* state = get in
     let* res, res_tight =
       (msg (Printf.sprintf "looking at tighters\n");
        let* obs, n = entry (TIMap.find tight state.tighters) in
        let d = get_data n in
        (* We enforce that the notation parsed previously, if right-open, is allowed to appear inside the left argument of this one. *)
        let* () =
          match first_tight with
          | None -> return ()
          | Some t ->
              if d.left = Closed || Interval.contains (Interval.left d) t then return ()
              else unexpected d.name in
        msg (Printf.sprintf "Found left-open %s\n" d.name);
        match d.right with
        | Closed -> (
            match d.left with
            | Open -> return (Notn (n, Term first_arg :: Bwd.to_list obs), None)
            | Closed -> return (App (first_arg, Notn (n, Bwd.to_list obs)), None))
        | Open -> (
            let i =
              match d.assoc with
              | Right -> Interval.Closed d.tightness
              | Left | Non -> Open d.tightness in
            msg (Printf.sprintf "Getting the rest of right-open %s\n" d.name);
            let* last_arg = lclosed i stop in
            msg (Printf.sprintf "Got the rest of right-open %s\n" d.name);
            match d.left with
            | Open ->
                return
                  ( Notn (n, Term first_arg :: Bwd.to_list (Snoc (obs, Term last_arg))),
                    Some d.tightness )
            | Closed ->
                return
                  ( App (first_arg, Notn (n, Bwd.to_list (Snoc (obs, Term last_arg)))),
                    Some d.tightness )))
       (* If this fails, we can parse a single variable name or a field projection and apply the first term to it.  Abstractions are not allowed as undelimited arguments.  Constructors *are* allowed, because they might have no arguments. *)
       </> let* arg = name </> numeral </> field </> constr in
           return (App (first_arg, arg), None) in
     msg (Printf.sprintf "Going on\n");
     (* Same comment here about carrying over "tight" as in lclosed. *)
     lopen tight stop res res_tight)
    (* If that also fails, another possibility is that we're at the end of the term with no more operators to parse, so we can just return the supplied "first argument". *)
    </> succeed first_arg

  let term () = lclosed Interval.entire TokMap.empty

  module Parser = struct
    include Basic.Parser

    let parse (state : State.t) : t = make state (term ())
  end
end

module Lex_and_parse =
  Parse_with_lexer.Make (State) (Token) (Res) (Unit) (Lexer.Parser) (Parse_term.Parser)

open Lex_and_parse

let start (state : State.t) : Lex_and_parse.t =
  make Lexer.Parser.init (Parse_term.Parser.parse state)

let parse (state : State.t) (str : string) : (Res.t, expect list) result =
  let p = run_on_string str (start state) in
  if has_succeeded p then Ok (final p)
  else if has_failed_syntax p then Error (failed_expectations p)
  else raise (Failure "what.")
