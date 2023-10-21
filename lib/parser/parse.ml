open Util
open Bwd
open Notations
open Compile
open Core
open Reporter
open Fmlib_parse

(* Sometimes we want to parse only a single term, other times we want to parse and execute a sequence of commands.  Since these two processes return different results, they have to be based on different instances of Token_parser.Make.  But they share all the code of the combinators for parsing terms, so we make those instances of a functor as well. *)

(* Parsing a term outputs a parse tree (which is then compiled in a context of local variables). *)
module ParseTree = struct
  type t = parse_tree
end

(* We misuse Fmlib's "semantic" errors for a couple of special classes of errors that are really syntactic, but which we don't detect until after the relevant tokens have already been "successfully" parsed, and for which we want to report more structured error information than just an "expected" string. *)
module SemanticError = struct
  type t =
    | Invalid_variable of Position.range * string
    (* These strings are the names of notations.  Arguably we should display their *namespaced* names, which would mean calling out to Yuujinchou.  It would also mean some special-casing, because abstractions are implemented specially in the parser and not as an actual Notation. *)
    | No_relative_precedence of Position.range * string * string
end

(* The functor that defines all the term-parsing combinators. *)
module Combinators (Final : Fmlib_std.Interfaces.ANY) = struct
  module Basic = Token_parser.Make (State) (Token) (Final) (SemanticError)
  open Basic

  (* We aren't using Fmlib's error reporting, so there's no point in supplying it nonempty "expect" strings. *)
  let step f = step "" f
  let followed_by f = followed_by f ""
  let backtrack f = backtrack f ""

  let rec tree (t : tree) (obs : observation Bwd.t) : (observation Bwd.t * Notation.t) t =
    match t with
    | Inner { ops; constr; field; name; term } -> (
        match term with
        | Some e ->
            (* If a term is allowed, we first try parsing something else, and if that fails we backtrack and parse a term.  Note that this means the "semantic" errors of invalid variable names from inside the backtrack are lost.  But that makes sense, because invalid variable names are valid as constant names, and if a term is allowed they can be parsed as constants (and then generate a name resolution error later if there is no such constant). *)
            backtrack (inner_nonterm ops constr field name obs)
            </>
            (* This is an *interior* term, so it has no tightness restrictions on what notations can occur inside, and is ended by the specified ending tokens. *)
            let* subterm = lclosed Interval.entire e in
            tree_op e (Snoc (obs, Term subterm))
        | None ->
            (* If a term is not allowed, we simply parse something else, with no backtracking needed. *)
            inner_nonterm ops constr field name obs)
    | Done n -> return (obs, n)
    | Flag (f, t) -> tree t (Snoc (obs, Flag f))
    | Lazy (lazy t) -> tree t obs

  (* Parse an inner branch of a tree except for the possibility of a term. *)
  and inner_nonterm ops constr field name obs =
    let* rng, ok =
      located
        (step (fun state _ tok ->
             match TokMap.find_opt tok ops with
             | Some br -> Some (Ok (br, ([] : observation list)), state)
             | None -> (
                 match (constr, tok) with
                 | Some br, Constr x -> Some (Ok (br, [ Constr x ]), state)
                 | _ -> (
                     match (field, tok) with
                     | Some br, Field x -> Some (Ok (br, [ Field x ]), state)
                     | _ -> (
                         match (name, tok) with
                         | Some br, Name x ->
                             if Token.variableable x then Some (Ok (br, [ Name (Some x) ]), state)
                               (* We'd like to report "invalid local variable name" here, but we can't raise it directly through Asai because there could be backtracking.  We also want to mark it as a "semantic error" so we can control exactly what data is attached to it, but we can't do that by failing a 'step' with None.  So instead we "succeed" the 'step' but return an error value that encodes the invalid variable name.  *)
                             else Some (Error x, state)
                         | Some br, Underscore -> Some (Ok (br, [ Name None ]), state)
                         | _ -> None))))) in
    (* Now outside the 'step', we test whether there was an error value, and if so we raise the appropriate semantic error.  *)
    match ok with
    | Ok (br, x) -> tree br (Bwd.append obs x)
    | Error name ->
        (* The 'position' of the parser at this point is *past* the offending variable name, since the 'step' call succeeded.  But we want to mark the error as occurring on the offending variable name, and we can get its range from the 'located' wrapper around the 'step' call, and store it in the semantic error message. *)
        fail (Invalid_variable (rng, name))

  and tree_op (ops : tree TokMap.t) (obs : observation Bwd.t) : (observation Bwd.t * Notation.t) t =
    let* optree =
      step (fun state _ tok ->
          match TokMap.find_opt tok ops with
          | Some br -> Some (br, state)
          | None -> None) in
    tree optree obs

  and entry (e : entry) : (observation Bwd.t * Notation.t) t = tree_op e Emp

  (* "lclosed" is passed an upper tightness interval and an additional set of ending ops (stored as a map, since that's how they occur naturally, but here we ignore the values and look only at the keys).  It parses an arbitrary left-closed tree (pre-merged).  The interior terms are calls to "lclosed" with the next ops passed as the ending ones. *)
  and lclosed (tight : Interval.t) (stop : tree TokMap.t) : parse_tree t =
    let* state = get in
    let* res, res_tight =
      (let* obs, n = entry state.left_closeds in
       let d = get_data n in
       (* If the parse ended right-open, we call "lclosed" again, with the upper tightness interval starting at the tightness of the just-parsed notation, closed if that notation is right-associative and open otherwise, to pick up the open argument. *)
       match d.right with
       | Closed -> return (Notn (n, Bwd.to_list obs), None)
       | Open ->
           let i = Interval.right_assoc d.tightness d.assoc in
           (* Note that the tightness here is that of the notation n, not the "tight" from the surrounding one that called lclosed.  Thus, if while parsing a right-open argument of some operator X we see a left-closed, right-open notation Z of *lower* tightness than X, we allow it, and it does not end if we encounter the start of a left-open notation Y of tightness in between X and Z, only if we see something of lower tightness than Z, or a stop-token from an *enclosing* notation (otherwise we wouldn't be able to delimit right-open operators by parentheses). *)
           let* last_arg = lclosed i stop in
           return (Notn (n, Bwd.to_list (Snoc (obs, Term last_arg))), Some (d.tightness, d.name)))
      (* If parsing a left-closed notation fails, we can instead parse an abstraction, a single variable name, a numeral, or a constructor.  (Field projections are not allowed since this would be the head of a spine.)  First we look forward past possible variable names to find a Mapsto, to see whether we're looking at an abstraction, and if so we insist on actually parsing that abstraction (and checking that the variable names are valid).  It seems that we must do this with backtracking, since if there *isn't* a Mapsto out there, a list of names might not just be something simple like an application spine but might include infix parts of notations.  The "followed_by" combination is to allow the abstraction to fail permanently on an invalid variable name (having consumed at least one name), while failing without consuming anything if there isn't a Mapsto. *)
      </> (let* _ = followed_by (abstraction stop Emp false) in
           abstraction stop Emp true)
      (* Otherwise, we parse a single name, numeral, or constructor. *)
      </> let* res =
            step (fun state _ tok ->
                match tok with
                | Name x -> Some (Name x, state)
                | Numeral n -> Some (Numeral n, state)
                | Constr x -> if Token.variableable x then Some (Constr x, state) else None
                | _ -> None) in
          return (res, None) in
    (* Then "lclosed" ends by calling "lopen" with its interval and ending ops, and also its own result (with extra argument added if necessary).  Note that we don't incorporate d.tightness here; it is only used to find the delimiter of the right-hand argument if the notation we parsed was right-open.  In particular, therefore, a right-closed notation can be followed by anything, even a left-open notation that binds tighter than it does; the only restriction is if we're inside the right-hand argument of some containing right-open notation, so we inherit a "tight" from there.  *)
    lopen tight stop res res_tight

  (* If we see a variable name or an underscore, there's a chance that it's actually the beginning of an abstraction.  Thus, we pick up as many variable names as possible and look for a mapsto afterwards.  The parameter for_real says whether to insist the variable names are valid and actually parse the body of the abstraction. *)
  and abstraction (stop : tree TokMap.t) (names : string option Bwd.t) (for_real : bool) :
      (parse_tree * (float * string) option) t =
    let* rng, x =
      located
        (step (fun state _ tok ->
             match tok with
             | Name x -> Some (`Name x, state)
             | Underscore -> Some (`Underscore, state)
             | Mapsto -> (
                 match names with
                 | Emp -> None
                 | Snoc _ -> Some (`Mapsto, state))
             | _ -> None)) in
    match x with
    | `Name x ->
        if (not for_real) || Token.variableable x then
          abstraction stop (Snoc (names, Some x)) for_real
        else fail (Invalid_variable (rng, x))
    | `Underscore -> abstraction stop (Snoc (names, None)) for_real
    | `Mapsto ->
        if for_real then
          (* An abstraction should be thought of as having −∞ tightness, so we allow almost anything at all to its right.  Except, of course, for the stop-tokens currently in effect, since we we need to be able to delimit an abstraction by parentheses or other right-closed notations.  Moreover, we make it *not* "right-associative", i.e. the tightness interval is open, so that operators of actual tightness −∞ (such as type ascription ":") can *not* appear undelimited inside it.  This is intentional: I feel that "x ↦ M : A" is inherently ambiguous and should be required to be parenthesized one way or the other.  (The other possible parsing of the unparenthesized version is disallowed because : is not left-associative, so it can't contain an abstraction to its left.) *)
          let* res = lclosed (Open Float.neg_infinity) stop in
          return (Abs (Bwd.to_list names, res), Some (Float.neg_infinity, "↦"))
        else return (Name "", None)

  (* "lopen" is passed an upper tightness interval and a set of ending ops, plus a parsed result for the left open argument and the tightness of the outermost notation in that argument if it is right-open. *)
  and lopen (tight : Interval.t) (stop : tree TokMap.t) (first_arg : parse_tree)
      (first_tight : (float * string) option) : parse_tree t =
    (* We start by looking ahead one token.  If we see one of the specified ending ops, or the initial op of a left-open tree with looser tightness than the lower endpoint of the current interval (with strictness determined by the tree in question), we return the result argument without parsing any more.  Note that the order matters, in case the next token could have more than one role.  Ending ops are tested first, which means that if a certain operator could end an "inner term" in an outer containing notation, it always does, even if it could also be interpreted as some infix notation inside that inner term.  If a certain token could be the initial op of more than one left-open, we stop here if *any* of those is looser; we don't backtrack and try other possibilities.  So the rule is that if multiple notations start with the same token, the looser one is used preferentially in cases when it matters.  (In cases where it doesn't matter, i.e. they would both be allowed at the same grouping relative to other notations, we can proceed to parse a merged tree containing both of them and decide later which one it is.)  *)
    followed_by
      (step (fun state _ tok ->
           if TokMap.mem tok stop then Some (first_arg, state)
           else
             let open Monad.Ops (Monad.Maybe) in
             let* ivls = TokMap.find_opt tok state.left_opens in
             if List.exists (fun ivl -> Interval.contains ivl (Interval.endpoint tight)) ivls then
               return (first_arg, state)
             else None))
    (* Otherwise, we parse either an arbitrary left-closed tree (applying the given result to it as a function) or an arbitrary left-open tree with tightness in the given interval (passing the given result as the starting open argument).  Interior terms are treated as in "lclosed".  (Actually, if the given interval is (Open ∞), i.e. completely empty, we don't allow left-closed trees either, since function application has tightness +∞.)  *)
    </> (let* state = get in
         let* res, res_tight =
           (let* rng, (obs, n) = located (entry (TIMap.find tight state.tighters)) in
            let d = get_data n in
            (* We enforce that the notation parsed previously, if right-open, is allowed to appear inside the left argument of this one.  One could make a case that notations d that fail this test should already have been excluded from the 'entry' that we parsed above.  But for one thing, that would require indexing those pre-merged trees by *two* tightness values, so that we'd have to maintain n² such trees where n is the number of tightness values in use, and that makes me worry a bit about efficiency.  Furthermore, doing it this way makes it easier to trap it and issue a more informative error message, which I think is a good thing because this includes examples like "let x ≔ M in N : A" and "x ↦ M : A" where the need for parentheses in Narya may be surprising to a new user.  *)
            let* () =
              match first_tight with
              | None -> return ()
              | Some (t, tname) ->
                  if d.left = Closed || Interval.contains (Interval.left d) t then return ()
                  else fail (No_relative_precedence (rng, tname, d.name)) in
            match d.right with
            | Closed -> (
                match d.left with
                | Open -> return (Notn (n, Term first_arg :: Bwd.to_list obs), None)
                | Closed ->
                    return
                      ( App (first_arg, Notn (n, Bwd.to_list obs)),
                        Some (Float.infinity, "application") ))
            | Open -> (
                let i =
                  match d.assoc with
                  | Right -> Interval.Closed d.tightness
                  | Left | Non -> Open d.tightness in
                let* last_arg = lclosed i stop in
                match d.left with
                | Open ->
                    return
                      ( Notn (n, Term first_arg :: Bwd.to_list (Snoc (obs, Term last_arg))),
                        Some (d.tightness, d.name) )
                | Closed ->
                    return
                      ( App (first_arg, Notn (n, Bwd.to_list (Snoc (obs, Term last_arg)))),
                        (* TODO: Is this right?  In this case it's really the *application* that is "inside" whatever comes next. *)
                        (* Some (d.tightness, d.name) *)
                        Some (Float.infinity, "application") )))
           (* If this fails, and if the given tightness interval includes +∞, we can parse a single variable name, numeral, constr, or field projection and apply the first term to it.  Abstractions are not allowed as undelimited arguments.  Constructors *are* allowed, because they might have no arguments. *)
           </> let* arg =
                 step (fun state _ tok ->
                     if tight = Open Float.infinity then None
                     else
                       match tok with
                       | Name x -> Some (Name x, state)
                       | Numeral n -> Some (Numeral n, state)
                       | Constr x -> if Token.variableable x then Some (Constr x, state) else None
                       | Field x -> if Token.variableable x then Some (Field x, state) else None
                       | _ -> None) in
               return (App (first_arg, arg), Some (Float.infinity, "application")) in
         (* Same comment here about carrying over "tight" as in lclosed. *)
         lopen tight stop res res_tight)
    (* If that also fails, another possibility is that we're at the end of the term with no more operators to parse, so we can just return the supplied "first argument". *)
    </> succeed first_arg

  (* The master term-parsing combinator parses an lclosed of arbitrary tightness, with no ending tokens (so it must take up the entire input string). *)
  let term () = lclosed Interval.entire TokMap.empty
end

(* To parse single terms, we instantiate this to output a parse tree. *)
module TermCombinators = Combinators (ParseTree)

module Parse_term = struct
  include TermCombinators.Basic.Parser

  let term (state : State.t) : t = TermCombinators.Basic.make state (TermCombinators.term ())
end

(* Then we connect it up with the lexer. *)
module Lex_and_parse_term =
  Parse_with_lexer.Make (State) (Token) (ParseTree) (SemanticError) (Lexer.Parser) (Parse_term)

open Lex_and_parse_term

let term (state : State.t) (str : string) : parse_tree =
  Range.run ~env:str @@ fun () ->
  let p = run_on_string str (make Lexer.Parser.init (Parse_term.term state)) in
  if has_succeeded p then final p
    (* Fmlib_parse has its own built-in error reporting with locations.  However, we instead use Asai's error reporting, so that we have a common "look" for parse errors and typechecking errors. *)
  else if has_failed_syntax p then
    (* It should be possible to report more detailed error information from the parser than just the location.  Fmlib supplies "failed_expectations", but I haven't been able to figure out how to make that useful with this parsing algorithm. *)
    fatal ~loc:(Range.convert (range p)) Parse_error
  else
    match failed_semantic p with
    | Invalid_variable (rng, name) -> fatal ~loc:(Range.convert rng) (Invalid_variable name)
    | No_relative_precedence (rng, n1, n2) ->
        fatal ~loc:(Range.convert rng) (No_relative_precedence (n1, n2))
