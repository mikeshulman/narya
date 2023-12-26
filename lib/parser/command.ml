open Core
open Notation
open Postprocess
open Format
open Uuseg_string
open Print

type t =
  | Axiom of Scope.Trie.path * observation
  | Def of Scope.Trie.path * observation * observation

let execute : t -> unit = function
  | Axiom (name, Term ty) -> Core.Command.execute (Axiom (name, process Emp ty))
  | Def (name, Term ty, Term tm) ->
      Core.Command.execute (Def (name, process Emp ty, process Emp tm))

let pp_command : formatter -> t -> unit =
 fun ppf cmd ->
  match cmd with
  | Axiom (name, ty) ->
      fprintf ppf "@[<hv 2>%a %a@ %a %a@]" pp_tok Axiom pp_utf_8 (String.concat "." name) pp_tok
        Colon pp_term ty
  | Def (name, ty, tm) ->
      fprintf ppf "@[<hv 2>%a %a@ %a %a@ %a %a@]" pp_tok Def pp_utf_8 (String.concat "." name)
        pp_tok Colon pp_term ty pp_tok Coloneq pp_term tm
