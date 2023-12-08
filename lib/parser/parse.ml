open Util
open Bwd
open Core
open Reporter
open Fmlib_parse
open Notation
module TokMap = Map.Make (Token)
module TIMap = Map.Make (Interval)

(* Sometimes we want to parse only a single term, other times we want to parse and execute a sequence of commands.  Since these two processes return different results, they have to be based on different instances of Token_parser.Make.  But they share all the code of the combinators for parsing terms, so we make those instances of a functor as well. *)

(* Parsing a term outputs a parse tree (which is then compiled in a context of local variables). *)
module ParseTree = struct
  type t = wrapped_parse
end

(* We misuse Fmlib's "semantic" errors for a couple of special classes of errors that are really syntactic, but which we don't detect until after the relevant tokens have already been "successfully" parsed, and for which we want to report more structured error information than just an "expected" string. *)
module SemanticError = struct
  type t =
    | Invalid_variable of Position.range * string
    (* These strings are the names of notations.  Arguably we should display their *namespaced* names, which would mean calling out to Yuujinchou.  It would also mean some special-casing, because applications are implemented specially in the parser and not as an actual Notation. *)
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

  let rec tree :
      type tight strict.
      (tight, strict) tree ->
      observation Bwd.t ->
      (observation Bwd.t * (tight, strict) notation_in_interval) t =
   fun t obs ->
    match t with
    | Inner ({ term; _ } as br) -> (
        match term with
        | Some e -> (
            (* If a term is allowed, we first try parsing something else, and if that fails we backtrack and parse a term.  Some backtracking seems unavoidable here, because if we see for instance "(x : A) (y : B)" we have no way of knowing at first whether it is the beginning of an iterated Π-type or whether it means the existing variable x ascribed to the type A, applied as a function to the existing variable y ascribed to the type B.  It is also possible for there to be ambiguity, e.g. "(x : A) → B" looks like a Π-type, but could also be a *non* dependent function-type with its domain ascribed.  We resolve the ambiguity in favor of non-terms first, so that this example parses as a Π-type (the other reading is very unlikely to be what was meant).  Note that this also means the "semantic" errors of invalid variable names from inside the backtrack are lost if it fails and we go on to a term.  But that makes sense, because invalid variable names are valid as constant names, and if a term is allowed they can be parsed as constants (and then generate a name resolution error later if there is no such constant). *)
            backtrack (inner_nonterm br obs)
            </>
            (* This is an *interior* term, so it has no tightness restrictions on what notations can occur inside, and is ended by the specified ending tokens. *)
            let* subterm = lclosed Interval.entire e in
            match subterm.get Interval.entire with
            | Ok tm -> tree_op e (Snoc (obs, Term tm))
            | Error _ -> fatal (Anomaly "Interior term failed"))
        | None ->
            (* If a term is not allowed, we simply parse something else, with no backtracking needed. *)
            inner_nonterm br obs)
    | Done_open (lt, n) -> return (obs, Open_in_interval (lt, n))
    | Done_closed n -> return (obs, Closed_in_interval n)
    | Lazy (lazy t) -> tree t obs

  (* Parse an inner branch of a tree except for the possibility of a term. *)
  and inner_nonterm :
      type tight strict.
      (tight, strict) branch ->
      observation Bwd.t ->
      (observation Bwd.t * (tight, strict) notation_in_interval) t =
   fun { ops; constr; field; ident; term = _ } obs ->
    let* rng, ok =
      located
        (step (fun state _ tok ->
             match TokMap.find_opt tok ops with
             | Some br -> Some (Ok (br, ([] : observation list)), state)
             | None -> (
                 (* Constructor and field names have already been validated by the lexer. *)
                 match (constr, tok) with
                 | Some br, Constr x -> Some (Ok (br, [ Constr x ]), state)
                 | _ -> (
                     match (field, tok) with
                     | Some br, Field x -> Some (Ok (br, [ Field x ]), state)
                     | _ -> (
                         (* A "ident" in a notation tree must be a valid *local* variable name. *)
                         match (ident, tok) with
                         | Some br, Ident x ->
                             if Token.variableable x then Some (Ok (br, [ Ident (Some x) ]), state)
                               (* We'd like to report "invalid local variable name" here, but we can't raise it directly through Asai because there could be backtracking.  We also want to mark it as a "semantic error" so we can control exactly what data is attached to it, but we can't do that by failing a 'step' with None.  So instead we "succeed" the 'step' but return an error value that encodes the invalid variable name.  *)
                             else Some (Error x, state)
                         | Some br, Underscore -> Some (Ok (br, [ Ident None ]), state)
                         | _ -> None))))) in
    (* Now outside the 'step', we test whether there was an error value, and if so we raise the appropriate semantic error.  *)
    match ok with
    | Ok (br, x) -> tree br (Bwd.append obs x)
    | Error ident ->
        (* The 'position' of the parser at this point is *past* the offending variable name, since the 'step' call succeeded.  But we want to mark the error as occurring on the offending variable name, and we can get its range from the 'located' wrapper around the 'step' call, and store it in the semantic error message. *)
        fail (Invalid_variable (rng, ident))

  and tree_op :
      type tight strict.
      (tight, strict) tree TokMap.t ->
      observation Bwd.t ->
      (observation Bwd.t * (tight, strict) notation_in_interval) t =
   fun ops obs ->
    let* optree =
      step (fun state _ tok ->
          match TokMap.find_opt tok ops with
          | Some br -> Some (br, state)
          | None -> None) in
    tree optree obs

  and entry :
      type tight strict.
      (tight, strict) tree TokMap.t -> (observation Bwd.t * (tight, strict) notation_in_interval) t
      =
   fun e -> tree_op e Emp

  (* "lclosed" is passed an upper tightness interval and an additional set of ending ops (stored as a map, since that's how they occur naturally, but here we ignore the values and look only at the keys).  It parses an arbitrary left-closed tree (pre-merged).  The interior terms are calls to "lclosed" with the next ops passed as the ending ones. *)
  and lclosed :
      type lt ls rt rs.
      (lt, ls) Interval.tt -> (rt, rs) tree TokMap.t -> (lt, ls) right_wrapped_parse t =
   fun tight stop ->
    let* state = get in
    let* res =
      (let* inner, notn = entry (State.left_closeds state) in
       match notn with
       | Open_in_interval (lt, _) -> No.plusomega_nlt lt
       | Closed_in_interval notn -> (
           match right notn with
           | Closed -> return { get = (fun _ -> Ok (outfix ~notn ~inner)) }
           | Open _ ->
               (* If the parse ended right-open, we call "lclosed" again, with the right-side upper tightness interval of the just-parsed notation, to pick up the open argument.  Since the tightness here is that of the notation n, not the "tight" from the surrounding one that called lclosed, if while parsing a right-open argument of some operator X we see a left-closed, right-open notation Z of *lower* tightness than X, we allow it, and it does not end if we encounter the start of a left-open notation Y of tightness in between X and Z, only if we see something of lower tightness than Z, or a stop-token from an *enclosing* notation (otherwise we wouldn't be able to delimit right-open operators by parentheses). *)
               let* last_arg = lclosed (interval_right notn) stop in
               return
                 {
                   get =
                     (* Both the notation and anything in its right-open argument must be allowed in a right-tightness interval. *)
                     (fun ivl ->
                       match Interval.contains ivl (tightness notn) with
                       | None -> Error (name notn)
                       | Some right_ok -> (
                           match last_arg.get ivl with
                           | Ok last -> Ok (prefix ~notn ~inner ~last ~right_ok)
                           | Error e -> Error e));
                 }))
      (* Otherwise, we parse a single ident, numeral, or constructor. *)
      </> step (fun state _ tok ->
              match tok with
              | Ident x -> Some ({ get = (fun _ -> Ok (Ident x)) }, state)
              | Numeral n -> Some ({ get = (fun _ -> Ok (Numeral n)) }, state)
              (* Constructor names have already been validated by the lexer. *)
              | Constr x -> Some ({ get = (fun _ -> Ok (Constr x)) }, state)
              | _ -> None) in
    (* Then "lclosed" ends by calling "lopen" with its interval and ending ops, and also its own result (with extra argument added if necessary).  Note that we don't incorporate d.tightness here; it is only used to find the delimiter of the right-hand argument if the notation we parsed was right-open.  In particular, therefore, a right-closed notation can be followed by anything, even a left-open notation that binds tighter than it does; the only restriction is if we're inside the right-hand argument of some containing right-open notation, so we inherit a "tight" from there.  *)
    lopen tight stop res

  (* "lopen" is passed an upper tightness interval and a set of ending ops, plus a parsed result for the left open argument and the tightness of the outermost notation in that argument if it is right-open. *)
  and lopen :
      type lt ls rt rs.
      (lt, ls) Interval.tt ->
      (rt, rs) tree TokMap.t ->
      (lt, ls) right_wrapped_parse ->
      (lt, ls) right_wrapped_parse t =
   fun tight stop first_arg ->
    match Interval.contains tight No.plus_omega with
    (* If the left tightness interval is the empty one (+ω,+ω], we aren't allowed to go on at all.  Otherwise, we need to get a witness of nonemptiness of that interval, for the case when we end up with an application. *)
    | None -> succeed first_arg
    | Some nontrivial ->
        (* Now we start by looking ahead one token.  If we see one of the specified ending ops, or the initial op of a left-open tree with looser tightness than the lower endpoint of the current interval (with strictness determined by the tree in question), we return the result argument without parsing any more.  Note that the order matters, in case the next token could have more than one role.  Ending ops are tested first, which means that if a certain operator could end an "inner term" in an outer containing notation, it always does, even if it could also be interpreted as some infix notation inside that inner term.  If a certain token could be the initial op of more than one left-open, we stop here if *any* of those is looser; we don't backtrack and try other possibilities.  So the rule is that if multiple notations start with the same token, the looser one is used preferentially in cases when it matters.  (In cases where it doesn't matter, i.e. they would both be allowed at the same grouping relative to other notations, we can proceed to parse a merged tree containing both of them and decide later which one it is.)  *)
        followed_by
          (step (fun state _ tok ->
               if TokMap.mem tok stop then Some (first_arg, state)
               else
                 let open Monad.Ops (Monad.Maybe) in
                 let* (Interval ivl) = TokMap.find_opt tok state.left_opens in
                 let (Wrap t) = Interval.endpoint tight in
                 let* _ = Interval.contains ivl t in
                 return (first_arg, state)))
        (* Otherwise, we parse either an arbitrary left-closed tree (applying the given result to it as a function) or an arbitrary left-open tree with tightness in the given interval (passing the given result as the starting open argument).  Interior terms are treated as in "lclosed".  *)
        </> (let* state = get in
             let* res =
               (let* rng, (inner, notn) = located (entry (State.tighters state tight)) in
                match notn with
                | Open_in_interval (left_ok, notn) -> (
                    match first_arg.get (interval_left notn) with
                    | Error e -> fail (No_relative_precedence (rng, e, name notn))
                    | Ok first -> (
                        match right notn with
                        | Closed ->
                            return { get = (fun _ -> Ok (postfix ~notn ~first ~inner ~left_ok)) }
                        | Open _ ->
                            let* last_arg = lclosed (interval_right notn) stop in
                            return
                              {
                                get =
                                  (fun ivl ->
                                    match
                                      (last_arg.get ivl, Interval.contains ivl (tightness notn))
                                    with
                                    | Ok last, Some right_ok ->
                                        Ok (infix ~notn ~first ~inner ~last ~left_ok ~right_ok)
                                    | Error e, _ -> Error e
                                    | _, None -> Error (name notn));
                              }))
                | Closed_in_interval notn -> (
                    match first_arg.get (Nonstrict, No.plus_omega) with
                    | Error e -> fail (No_relative_precedence (rng, e, "application"))
                    | Ok fn -> (
                        match right notn with
                        | Closed ->
                            return
                              {
                                get =
                                  (fun ivl ->
                                    match Interval.contains ivl No.plus_omega with
                                    | None -> Error "application"
                                    | Some right_ok ->
                                        Ok
                                          (App
                                             {
                                               fn;
                                               arg = outfix ~notn ~inner;
                                               left_ok = nontrivial;
                                               right_ok;
                                             }));
                              }
                        | Open _ ->
                            let* last_arg = lclosed (interval_right notn) stop in
                            return
                              {
                                get =
                                  (fun ivl ->
                                    match
                                      ( last_arg.get ivl,
                                        Interval.contains ivl (tightness notn),
                                        Interval.contains ivl No.plus_omega )
                                    with
                                    | Ok last, Some right_ok, Some right_app ->
                                        Ok
                                          (App
                                             {
                                               fn;
                                               arg = prefix ~notn ~inner ~last ~right_ok;
                                               left_ok = nontrivial;
                                               right_ok = right_app;
                                             })
                                    | Error e, _, _ -> Error e
                                    | _, None, _ -> Error (name notn)
                                    | _, _, None -> Error "application");
                              })))
               (* If this fails, we can parse a single variable name, numeral, constr, or field projection and apply the first term to it.  Abstractions are not allowed as undelimited arguments.  Constructors *are* allowed, because they might have no arguments. *)
               </> let* rng, arg =
                     located
                       (step (fun state _ tok ->
                            match tok with
                            | Ident x -> Some ({ get = (fun _ -> Ok (Ident x)) }, state)
                            | Numeral n -> Some ({ get = (fun _ -> Ok (Numeral n)) }, state)
                            (* Constructor and field names have already been validated by the lexer. *)
                            | Constr x -> Some ({ get = (fun _ -> Ok (Constr x)) }, state)
                            | Field x -> Some ({ get = (fun _ -> Ok (Field x)) }, state)
                            | _ -> None)) in
                   match first_arg.get (Nonstrict, No.plus_omega) with
                   | Error e -> fail (No_relative_precedence (rng, e, "application"))
                   | Ok fn ->
                       return
                         {
                           get =
                             (fun ivl ->
                               match (arg.get ivl, Interval.contains ivl No.plus_omega) with
                               | Ok arg, Some right_ok ->
                                   Ok (App { fn; arg; left_ok = nontrivial; right_ok })
                               | Error e, _ -> Error e
                               | _, None -> Error "application");
                         } in
             (* Same comment here about carrying over "tight" as in lclosed. *)
             lopen tight stop res)
        (* If that also fails, another possibility is that we're at the end of the term with no more operators to parse, so we can just return the supplied "first argument". *)
        </> succeed first_arg

  (* The master term-parsing combinator parses an lclosed of arbitrary tightness, with no ending tokens (so it must take up the entire input string). *)
  let term () =
    let* tm = lclosed Interval.entire TokMap.empty in
    match tm.get Interval.entire with
    | Ok tm -> return (Wrap tm)
    | Error _ -> fatal (Anomaly "Outer term failed")
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

let term (state : State.t) (str : string) : wrapped_parse =
  Range.run ~env:str @@ fun () ->
  let p = run_on_string str (make Lexer.Parser.init (Parse_term.term state)) in
  if has_succeeded p then final p
    (* Fmlib_parse has its own built-in error reporting with locations.  However, we instead use Asai's error reporting, so that we have a common "look" for parse errors and typechecking errors. *)
  else if has_failed_syntax p then
    (* It should be possible to report more detailed error information from the parser than just the location.  Fmlib supplies "failed_expectations", but I haven't been able to figure out how to make that useful with this parsing algorithm. *)
    fatal ~loc:(Range.convert (range p)) Parse_error
  else
    match failed_semantic p with
    | Invalid_variable (rng, ident) -> fatal ~loc:(Range.convert rng) (Invalid_variable ident)
    | No_relative_precedence (rng, n1, n2) ->
        fatal ~loc:(Range.convert rng) (No_relative_precedence (n1, n2))
