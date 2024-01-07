open Util
open Bwd
open Core.Reporter
open Fmlib_parse
open Notation
module TokMap = Map.Make (Token)

(* Sometimes we want to parse only a single term, other times we want to parse and execute a sequence of commands.  Since these two processes return different results, they have to be based on different instances of Token_parser.Make.  But they share all the code of the combinators for parsing terms, so we make those instances of a functor as well. *)

(* Parsing a term outputs a parse tree (which is then postprocessed in a context of local variables). *)
module ParseTree = struct
  type t = observation
end

(* We misuse Fmlib's "semantic" errors for a special class of errors that are really syntactic, but which we don't detect until after the relevant tokens have already been "successfully" parsed, and for which we want to report more structured error information than just an "expected" string. *)
module SemanticError = struct
  type t =
    (* These strings are the names of notations.  Arguably we should display their *namespaced* names, which would mean calling out to Yuujinchou.  It would also mean some special-casing, because applications are implemented specially in the parser and not as an actual Notation. *)
    | No_relative_precedence of Position.range * string * string
end

(* The functor that defines all the term-parsing combinators. *)
module Combinators (Final : Fmlib_std.Interfaces.ANY) = struct
  module Basic = Token_parser.Make (Unit) (Token) (Final) (SemanticError)
  open Basic

  (* We aren't using Fmlib's error reporting, so there's no point in supplying it nonempty "expect" strings. *)
  let step f = step "" f
  let followed_by f = followed_by f ""

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
            inner_nonterm br obs
            </>
            (* This is an *interior* term, so it has no tightness restrictions on what notations can occur inside, and is ended by the specified ending tokens. *)
            let* subterm = lclosed Interval.entire e in
            match subterm.get Interval.entire with
            | Ok tm -> tree_op e (Snoc (obs, Term tm))
            | Error n -> fatal (Anomaly (Printf.sprintf "Interior term failed on notation %s" n)))
        | None -> inner_nonterm br obs)
    | Done_open (lt, n) -> return (obs, Open_in_interval (lt, n))
    | Done_closed n -> return (obs, Closed_in_interval n)
    | Lazy (lazy t) -> tree t obs

  (* Parse an inner branch of a tree except for the possibility of a term. *)
  and inner_nonterm :
      type tight strict.
      (tight, strict) branch ->
      observation Bwd.t ->
      (observation Bwd.t * (tight, strict) notation_in_interval) t =
   fun { ops; field; term = _ } obs ->
    let* br, x =
      step (fun state _ tok ->
          match TokMap.find_opt tok ops with
          | Some br -> Some ((br, ([] : observation list)), state)
          | None -> (
              (* Field names have already been validated by the lexer. *)
              match (field, tok) with
              | Some br, Field x -> Some ((br, [ Term (Field x) ]), state)
              | _ -> None)) in
    tree br (Bwd.append obs x)

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
    let* res =
      (let* inner, notn = entry (State.left_closeds ()) in
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
      (* Otherwise, we parse a single ident or constructor. *)
      </> step (fun state _ tok ->
              match tok with
              | Ident x -> Some ({ get = (fun _ -> Ok (Ident x)) }, state)
              (* Constructor names have already been validated by the lexer. *)
              | Constr x -> Some ({ get = (fun _ -> Ok (Constr x)) }, state)
              | Underscore -> Some ({ get = (fun _ -> Ok Placeholder) }, state)
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
                 let* (Interval ivl) = State.left_opens tok in
                 let t = tight.endpoint in
                 let* _ = Interval.contains ivl t in
                 return (first_arg, state)))
        (* Otherwise, we parse either an arbitrary left-closed tree (applying the given result to it as a function) or an arbitrary left-open tree with tightness in the given interval (passing the given result as the starting open argument).  Interior terms are treated as in "lclosed".  *)
        </> (let* res =
               (let* rng, (inner, notn) = located (entry (State.tighters tight)) in
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
                    match first_arg.get Interval.plus_omega_only with
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
               (* If this fails, we can parse a single variable name, constr, or field projection and apply the first term to it.  Constructors are allowed here because they might have no arguments. *)
               </> let* rng, arg =
                     located
                       (step (fun state _ tok ->
                            match tok with
                            | Ident x -> Some ({ get = (fun _ -> Ok (Ident x)) }, state)
                            (* Constructor and field names have already been validated by the lexer. *)
                            | Constr x -> Some ({ get = (fun _ -> Ok (Constr x)) }, state)
                            | Underscore -> Some ({ get = (fun _ -> Ok Placeholder) }, state)
                            | Field x -> Some ({ get = (fun _ -> Ok (Field x)) }, state)
                            | _ -> None)) in
                   match first_arg.get Interval.plus_omega_only with
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
    | Ok tm -> return (Term tm)
    | Error _ -> fatal (Anomaly "Outer term failed")
end

(* Sometimes we want to parse just one term, other times a sequence of commands.  But the parsing functor has to be instantiated differently depending on the goal type, and the error-wrapping around it is the same in both cases, so we make it into another functor. *)

module type Goal = sig
  module Final : Fmlib_std.Interfaces.ANY
  module C : module type of Combinators (Final)

  val final : unit -> Final.t C.Basic.t
end

module Parse_goal (Final : Fmlib_std.Interfaces.ANY) (G : Goal with module Final = Final) = struct
  include G.C.Basic.Parser

  module Lex_and_parse =
    Parse_with_lexer.Make (Unit) (Token) (Final) (SemanticError) (Lexer.Parser) (G.C.Basic.Parser)

  open Lex_and_parse

  type new_source = [ `String of string | `File of string ]
  type open_source = Range.Data.t * [ `String of int * string | `File of In_channel.t ]

  (* Parse the given 'source', raising appropriate Asai errors as 'fatal'.  If this returns normally, then the parse succeeded, and the functions below can be used to extract the result.  The first argument says whether EOF is expected at the end, whether it can be restarted, or whether it is itself a restart of another parser. *)
  let parse
      (action :
        [ `New of [ `Full | `Partial ] * new_source | `Restart of Lex_and_parse.t * open_source ]) :
      Lex_and_parse.t * open_source =
    let env, run =
      match action with
      | `New (partial, `String content) -> (
          let (env : Range.Data.t) =
            {
              source = `String { content; title = Some "user-supplied term" };
              length = Int64.of_int (String.length content);
            } in
          match partial with
          | `Full -> (env, fun p -> (`String (0, content), run_on_string content p))
          | `Partial ->
              ( env,
                fun p ->
                  let n, p = run_on_string_at 0 content p in
                  (`String (n, content), p) ))
      | `New (_, `File name) ->
          let ic = In_channel.open_text name in
          ( { source = `File name; length = In_channel.length ic },
            fun p -> (`File ic, run_on_channel ic p) )
      | `Restart (_, (env, `String (n, content))) ->
          ( env,
            fun p ->
              let n, p = run_on_string_at n content p in
              (`String (n, content), p) )
      | `Restart (_, (env, `File ic)) -> (env, fun p -> (`File ic, run_on_channel ic p)) in
    let final =
      match action with
      | `New (`Full, _) -> G.final ()
      | `New (`Partial, _) | `Restart _ ->
          G.C.Basic.(
            let* x = G.final () in
            expect_end x </> return x) in
    let lex =
      match action with
      | `New _ -> Lexer.Parser.start
      | `Restart (p, _) -> Lex_and_parse.lex p in
    let token_make =
      match action with
      | `New (`Full, _) -> G.C.Basic.make ()
      | `New (`Partial, _) -> G.C.Basic.make_partial ()
      | `Restart (p, _) ->
          fun c ->
            G.C.Basic.make_partial () c
            |> G.C.Basic.Parser.transfer_lookahead (Lex_and_parse.parse p) in
    Range.run ~env @@ fun () ->
    let p = Lex_and_parse.make lex (token_make final) in
    let ic, p = run p in
    (* Fmlib_parse has its own built-in error reporting with locations.  However, we instead use Asai's error reporting, so that we have a common "look" for parse errors and typechecking errors. *)
    if has_failed_syntax p then
      (* It should be possible to report more detailed error information from the parser than just the location.  Fmlib supplies "failed_expectations", but I haven't been able to figure out how to make that useful with this parsing algorithm. *)
      fatal ~loc:(Range.convert (range p)) Parse_error
    else if has_failed_semantic p then
      match failed_semantic p with
      | No_relative_precedence (rng, n1, n2) ->
          fatal ~loc:(Range.convert rng) (No_relative_precedence (n1, n2))
    else if has_succeeded p then (p, (env, ic))
    else if needs_more p then fatal (Anomaly "parser needs more")
    else fatal (Anomaly "what")

  let final (p : Lex_and_parse.t) : Final.t = final p
  let has_consumed_end (p : Lex_and_parse.t) : bool = has_consumed_end p
end

(* To parse single terms, we instantiate this to output a parse tree. *)
module Term_goal = struct
  module Final = ParseTree
  module C = Combinators (Final)

  let final : unit -> observation C.Basic.t = C.term
end

module Term = Parse_goal (ParseTree) (Term_goal)

module Command_goal = struct
  module Final = Command
  module C = Combinators (Final)
  open C.Basic

  let token x = step "" (fun state _ tok -> if tok = x then Some ((), state) else None)

  let ident =
    step "" (fun state _ tok ->
        match tok with
        | Ident name -> Some (name, state)
        | _ -> None)

  let axiom =
    let* () = token Axiom in
    let* name = ident in
    let* () = token Colon in
    let* ty = C.term () in
    return (Command.Axiom (name, ty))

  let def =
    let* () = token Def in
    let* name = ident in
    let* () = token Colon in
    let* ty = C.term () in
    let* () = token Coloneq in
    let* tm = C.term () in
    return (Command.Def (name, ty, tm))

  let final : unit -> Command.t C.Basic.t = fun () -> axiom </> def
end

module Command = Parse_goal (Command) (Command_goal)
