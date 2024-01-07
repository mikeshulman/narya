open Dim
open Core
open Notation
open Postprocess
open Unparse
open Format
open Uuseg_string
open Print
open Reporter

type t =
  | Axiom of Scope.Trie.path * observation
  | Def of Scope.Trie.path * observation * observation
  | Echo of observation

let execute : t -> unit = function
  | Axiom (name, Term ty) -> Core.Command.execute (Axiom (name, process Emp ty))
  | Def (name, Term ty, Term tm) ->
      Core.Command.execute (Def (name, process Emp ty, process Emp tm))
  | Echo (Term tm) -> (
      let rtm = process Emp tm in
      match rtm with
      | Synth rtm ->
          let ctm, ety = Check.synth Ctx.empty rtm in
          let etm = Norm.eval (Emp D.zero) ctm in
          let btm = Readback.readback_at Ctx.empty etm ety in
          let utm = unparse Names.empty btm Interval.entire Interval.entire in
          pp_term Format.std_formatter (Term utm);
          Format.pp_print_newline Format.std_formatter ()
      | _ -> fatal (Nonsynthesizing "argument of echo"))

let pp_command : formatter -> t -> unit =
 fun ppf cmd ->
  match cmd with
  | Axiom (name, ty) ->
      fprintf ppf "@[<hv 2>%a %a@ %a %a@]" pp_tok Axiom pp_utf_8 (String.concat "." name) pp_tok
        Colon pp_term ty
  | Def (name, ty, tm) ->
      fprintf ppf "@[<hv 2>%a %a@ %a %a@ %a %a@]" pp_tok Def pp_utf_8 (String.concat "." name)
        pp_tok Colon pp_term ty pp_tok Coloneq pp_term tm
  | Echo tm -> fprintf ppf "@[<hv 2>%a %a@]" pp_tok Echo pp_term tm
