open Core
open Format
open Uuseg_string
open Reporter

(* We have two styles of output, compact and noncompact.  The caller can specify which to use with a reader effect.  We also have two different printing states, for case trees and terms. *)

type style = Compact | Noncompact
type context = Term | Case

module Reader = Algaeff.Reader.Make (struct
  type env = style * context
end)

let style () = fst (Reader.read ())
let compactly f = Reader.scope (fun (_, context) -> (Compact, context)) f
let noncompactly f = Reader.scope (fun (_, context) -> (Noncompact, context)) f
let state () = snd (Reader.read ())
let as_term f = Reader.scope (fun (style, _) -> (style, Term)) f
let as_case f = Reader.scope (fun (style, _) -> (style, Case)) f

(* Print a token, with arguments swapped so that it takes the token as an argument. *)
let pp_tok (ppf : formatter) (tok : Token.t) : unit = Token.pp tok ppf ()

(* Print a variable, with underscore for unnamed variables. *)
let pp_var : formatter -> string option -> unit =
  pp_print_option ~none:(Token.pp Underscore) pp_utf_8

(* Print constructors and fields *)
let pp_constr (ppf : formatter) (c : string) : unit = fprintf ppf "%a." pp_utf_8 c
let pp_field (ppf : formatter) (c : string) : unit = fprintf ppf ".%a" pp_utf_8 c

(* Print a parse tree. *)
let rec pp_term (ppf : formatter) (tr : Notation.parse) : unit =
  match state () with
  | Case -> (
      match tr with
      | Notn (n, obs) -> (
          match Notation.print_as_case n with
          | Some pp -> pp ppf obs
          | None -> as_term @@ fun () -> pp_term ppf tr)
      | Abs (cube, vars, body) ->
          fprintf ppf "@[<b 0>@[<hov 2>%a %a@]@ %a@]"
            (pp_print_list ~pp_sep:pp_print_space pp_var)
            vars pp_tok
            (match cube with
            | `Normal -> Mapsto
            | `Cube -> DblMapsto)
            (* TODO: Test that passing through a lambda doesn't drop into term parsing *)
            pp_term body
      | _ -> as_term @@ fun () -> pp_term ppf tr)
  | Term -> (
      match tr with
      | Notn (n, obs) -> (
          match Notation.print n with
          | Some pp -> pp ppf obs
          | None -> fatal (Anomaly "Unprintable term"))
      | App _ -> fprintf ppf "@[<hov 2>%a@]" pp_spine tr
      | Name x -> pp_utf_8 ppf x
      | Constr c -> pp_constr ppf c
      | Field f -> pp_field ppf f
      | Numeral n -> Q.pp_print ppf n
      | Abs (cube, vars, body) ->
          fprintf ppf "@[<b 0>@[<hov 2>%a %a@]@ %a@]"
            (pp_print_list ~pp_sep:pp_print_space pp_var)
            vars pp_tok
            (match cube with
            | `Normal -> Mapsto
            | `Cube -> DblMapsto)
            pp_term body)

and pp_spine (ppf : formatter) (tr : Notation.parse) : unit =
  match tr with
  | App (head, arg) -> fprintf ppf "%a@ %a" pp_spine head pp_term arg
  | _ -> pp_term ppf tr

let pp_as_term style f = Reader.run ~env:(style, Term) f
let pp_as_case style f = Reader.run ~env:(style, Case) f
