open Util

(* ********************
   Parsing monad
   ******************** *)

(* During parsing we use a monad for nondeterministic choice, such as the List monad or the Seq/Stream (delayed list) monads. A List parser computes all possible parses.  This enables us to be maximally informative when rejecting ambiguous input, as suggested by DN. By contrast, a delayed list parser can bail out as soon as one parse is found, thereby possibly improving performance on correct input (although not necessarily, since laziness has an overhead).  We thereby lose the ability to reject ambiguous input, and strictly reduce performance on input that has no parses (since we incur the overhead of laziness while still having to do all the same work).  But since we expect most input to parse correctly, this *could* be a win. *)

(* In theory, a delayed list parser could also proceed until it finds either a second parse or that there isn't one.  This could potentially be faster than a List parser at rejecting ambiguous input, although it would not give complete information about the possible parses.  But it would be strictly slower not just on unparsable input but also on correct input, since in both cases it incurs the overhead of laziness while still doing all the same work.  Since we expect ambiguous input to be rare, this is unlikely to ever be a win. *)

(* Currently we stick with a List parser. *)

module Choice = Monad.List
module ChoiceOps = Monad.PlusOps (Choice)

(* We also augment the specified choice monad with a State monad to keep track of the tokens consumed so far on the input stream.  As compared with other ways of maintaining state, such as mutable references and shallow effects, the monadic approach allows different Choices to have different states.  And since we already have to use a monad for Choice (OCaml's effect continuations are single-shot, preventing an effectful implementation of backtracking), using a monad for state doesn't incur extra monadic overhead. *)

module Toklist = struct
  type t = Token.t list
end

module Parsing = Monad.StateTPlus (Choice) (Toklist)
module ParseOps = Monad.PlusOps (Parsing)
open ParseOps

(* We separate the domain and codomain of the parsing monad type so that we can expose its definition in terms of them (to enable memoization) without exposing their structure. *)
type parse_in = Token.t list
type 'b parse_out = ('b * Token.t list) Choice.t

(* Get the next token, removing it from the input stream.  Currently just skips over indentation information. *)
let rec next : unit -> string Parsing.t =
 fun () ->
  let* toks = Parsing.get in
  match toks with
  | Tok first :: rest ->
      let* () = Parsing.put rest in
      return first
  | Indent _ :: rest ->
      let* () = Parsing.put rest in
      next ()
  | [] -> fail

(* Consume a specified notation-part token, failing if it is not the next token.  *)
let consume (tok : string) : unit Parsing.t =
  let* first = next () in
  guard (first = tok)

(* Consume a specified list of notation parts. *)
let consume_list (toks : string list) : unit Parsing.t =
  let open Mlist.Monadic (Parsing) in
  miterM (fun [ x ] -> consume x) [ toks ]

(* Consume an arbitrary identifier, returning it.  Fails if the next token is not a valid identifier. *)
let consume_ident : string Parsing.t =
  let* first = next () in
  let* () = guard (Token.is_ident first) in
  return first

(* Consume either an identifier or an underscore.  Return Some of the name, or None if an underscore. *)
let consume_var : string option Parsing.t =
  (let* name = consume_ident in
   return (Some name))
  <|> let* _ = consume "_" in
      return None

(* Consume an arbitrary field projection, returning it without the dot. *)
let consume_field : string Parsing.t =
  let* first = next () in
  match Token.is_field first with
  | Some fld -> return fld
  | None -> fail

let consume_fieldname : string Parsing.t =
  let* first = next () in
  let* () = guard (Token.is_fieldname first) in
  return first

(* Supply a token stream and run a parsing computation in the monad. *)
let execute (f : 'a Parsing.t) (toks : Token.t list) : 'a Choice.t =
  let open ChoiceOps in
  let* cx = f toks in
  match cx with
  | x, [] -> return x
  | _ -> fail
