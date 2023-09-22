open Bwd
open Notations
open Compile
open Fmlib_parse

exception Tokens of Token.t list

let msg (_ : string) = ()
(* let msg s = Printf.printf "%s" s *)

module Result = struct
  type t = result
end

module Parse_term = struct
  module Basic = Token_parser.Make (State) (Token) (Result) (Unit)
  open Basic

  let rec tree (t : tree) (obs : observation Bwd.t) : (observation Bwd.t * Notation.t) t =
    msg (Printf.sprintf "tree\n");
    match t with
    | Inner { ops; name; term; fail } -> (
        backtrack
          (let* optree =
             msg (Printf.sprintf "Looking for op in tree\n");
             step "operator" (fun state _ tok ->
                 Option.map
                   (fun br ->
                     msg (Printf.sprintf "Found op %s in tree\n" (Token.to_string tok));
                     (br, state))
                   (TokMap.find_opt tok ops)) in
           tree optree obs)
          "operator"
        </> backtrack
              (let* nametree, x =
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
               tree nametree (Snoc (obs, Name x)))
              "name"
        </>
        match term with
        | Some e ->
            msg (Printf.sprintf "Looking for term\n");
            let* subterm = lclosed Interval.entire e in
            tree (of_entry e) (Snoc (obs, Term subterm))
        | None -> unexpected ("failure " ^ String.concat ", " fail))
    | Done n -> return (obs, n)
    | Flag (f, t) -> tree t (Snoc (obs, Flag f))
    | Lazy (lazy t) -> tree t obs

  and entry (e : entry) : (observation Bwd.t * Notation.t) t = tree (of_entry e) Emp

  (* "lclosed" is passed an upper precedence interval and an additional set of ending ops.  It parses an arbitrary left-closed tree (pre-merged).  The interior terms are calls to "lclosed" with the next ops passed as the ending ones. *)
  and lclosed (tight : Interval.t) (stop : tree TokMap.t) : result t =
    msg (Printf.sprintf "lclosed\n");
    let* state = get in
    let* res =
      (msg (Printf.sprintf "Looking in left_closeds\n");
       let* obs, n = entry state.left_closeds in
       let d = get_data n in
       msg (Printf.sprintf "Finished op %s\n" d.name);
       (* If the parse ended right-open, we call "lclosed" again, with the upper precedence interval starting at the precedence of the just-parsed notation, closed if that notation is right-associative and open otherwise, to pick up the open argument. *)
       match d.right with
       | Closed -> return (Notn (n, Bwd.to_list obs))
       | Open ->
           let i =
             match d.assoc with
             | Right -> Interval.Closed d.tightness
             | Left | Non -> Open d.tightness in
           (* Note that the tightness here is that of the notation n, not the "tight" from the surrounding one that called lclosed.  Thus, if while parsing a right-open argument of some operator X we see a left-closed, right-open notation Z of *lower* precedence than X, we allow it, and it does not end if we encounter the start of a left-open notation Y of precedence in between X and Z, only if we see something of lower precedence than Z, or a stop-token from an *enclosing* notation (otherwise we wouldn't be able to delimit right-open operators by parentheses). *)
           let* last_arg = lclosed i stop in
           return (Notn (n, Bwd.to_list (Snoc (obs, Term last_arg)))))
      (* If parsing a left-closed notation fails, we can instead parse an abstraction, a single variable name, or a constructor.  Field projections are not allowed since this would be the head of a spine. *)
      </> backtrack (abstraction stop Emp) "abstraction"
      </> name
      </> numeral
      </> constr in
    (* Then "lclosed" ends by calling "lopen" with its interval and ending ops, and also its own result (with extra argument added if necessary).  Note that we don't incorporate d.tightness here; it is only used to find the delimiter of the right-hand argument if the notation we parsed was right-open.  In particular, therefore, a right-closed notation can be followed by anything, even a left-open notation that binds tighter than it does; the only restriction is if we're inside the right-hand argument of some containing right-open notation, so we inherit a "tight" from there.  *)
    let* r = lopen tight stop res in
    msg (Printf.sprintf "end of lclosed\n");
    return r

  (* If we see a variable name or an underscore, there's a chance that it's actually the beginning of an abstraction.  Thus, we pick up as many variable names as possible and look for a mapsto afterwards. *)
  and abstraction (stop : tree TokMap.t) (names : string option Bwd.t) : result t =
    let* x =
      step "name" (fun state _ tok ->
          match tok with
          | Name x -> if Token.variableable x then Some (`Name x, state) else None
          | Underscore -> Some (`Underscore, state)
          | Mapsto -> Some (`Mapsto, state)
          | _ -> None) in
    match x with
    | `Name x -> abstraction stop (Snoc (names, Some x))
    | `Underscore -> abstraction stop (Snoc (names, None))
    | `Mapsto -> (
        match names with
        | Emp -> unexpected "\"↦\""
        | Snoc _ ->
            (* An abstraction should be thought of as having −∞ tightness, so we allow almost anything at all to its right.  Except, of course, for the stop-tokens currently in effect, since we we need to be able to delimit an abstraction by parentheses or other right-closed notations.  Moreover, we make it *not* "right-associative", i.e. the precedence interval is open, so that operators of actual precedence −∞ (such as type ascription ":") can *not* appear undelimited inside it.  This is intentional: I feel that "x ↦ M : A" is inherently ambiguous and should be required to be parenthesized one way or the other.  (The other possible parsing of the unparenthesized version is disallowed because : is not left-associative, so it can't contain an abstraction to its left.) *)
            let* res = lclosed (Open Float.neg_infinity) stop in
            return (Abs (Bwd.to_list names, res)))

  and name : result t =
    step "name" (fun state _ tok ->
        match tok with
        | Name x ->
            msg (Printf.sprintf "Found name %s in name\n" x);
            Some (Name x, state)
        | _ -> None)

  and constr : result t =
    step "constr" (fun state _ tok ->
        match tok with
        | Constr x -> if Token.variableable x then Some (Constr x, state) else None
        | _ -> None)

  and proj : result t =
    step "proj" (fun state _ tok ->
        match tok with
        | Proj x -> if Token.variableable x then Some (Proj x, state) else None
        | _ -> None)

  and numeral : result t =
    step "numeral" (fun state _ tok ->
        match tok with
        | Numeral n -> (
            match Float.of_string_opt n with
            | Some n -> Some (Numeral n, state)
            | None -> None)
        | _ -> None)

  (* "lopen" is passed an upper precedence and a set of ending ops, plus a parsed result for the left open argument.  It starts by looking ahead one token: if it sees Eof, or the initial op of a left-open tree with looser precedence than the lower endpoint of the current interval (with strictness determined by the tree in question), or one of the specified ending ops, then it returns its result argument without parsing any more. *)
  and lopen (tight : Interval.t) (stop : tree TokMap.t) (first_arg : result) : result t =
    msg (Printf.sprintf "lopen\n");
    (let* () =
       followed_by
         (step "ending tok" (fun state _ tok ->
              if
                TokSet.mem tok (FMap.find (Interval.endpoint tight) state.loosers)
                || TokMap.mem tok stop
              then Some ((), state)
              else None))
         "ending token" in
     return first_arg)
    </> (* Otherwise, it parses either an arbitrary left-closed tree (applying the given result to it as a function) or an arbitrary left-open tree with precedence in the given interval (passing the given result as the starting open argument).  Interior terms are treated as in "lclosed".  *)
    (let* state = get in
     let* res =
       (msg (Printf.sprintf "looking at tighters\n");
        let* obs, n = entry (TIMap.find tight state.tighters) in
        let d = get_data n in
        msg (Printf.sprintf "Found left-open %s\n" d.name);
        match d.right with
        | Closed -> (
            match d.left with
            | Open -> return (Notn (n, Term first_arg :: Bwd.to_list obs))
            | Closed -> return (App (first_arg, Notn (n, Bwd.to_list obs))))
        | Open -> (
            let i =
              match d.assoc with
              | Right -> Interval.Closed d.tightness
              | Left | Non -> Open d.tightness in
            msg (Printf.sprintf "Getting the rest of right-open %s\n" d.name);
            let* last_arg = lclosed i stop in
            msg (Printf.sprintf "Got the rest of right-open %s\n" d.name);
            match d.left with
            | Open -> return (Notn (n, Term first_arg :: Bwd.to_list (Snoc (obs, Term last_arg))))
            | Closed -> return (App (first_arg, Notn (n, Bwd.to_list (Snoc (obs, Term last_arg)))))))
       (* If this fails, we can parse a single variable name or a field projection and apply the first term to it.  Abstractions are not allowed as undelimited arguments.  Constructors *are* allowed, because they might have no arguments. *)
       </> let* arg = name </> numeral </> proj </> constr in
           return (App (first_arg, arg)) in
     msg (Printf.sprintf "Going on\n");
     (* Same comment here about carrying over "tight" as in lclosed. *)
     lopen tight stop res)
    </> succeed first_arg

  let term () = lclosed Interval.entire TokMap.empty

  module Parser = struct
    include Basic.Parser

    let parse (state : State.t) : t = make state (term ())
  end
end

module Lex_and_parse =
  Parse_with_lexer.Make (State) (Token) (Result) (Unit) (Lexer.Parser) (Parse_term.Parser)

open Lex_and_parse

let start (state : State.t) : Lex_and_parse.t =
  make Lexer.Parser.init (Parse_term.Parser.parse state)

let parse (state : State.t) (str : string) : (Result.t, expect list) Either.t =
  let p = run_on_string str (start state) in
  if has_succeeded p then Left (final p)
  else if has_failed_syntax p then Right (failed_expectations p)
  else raise (Failure "what.")
