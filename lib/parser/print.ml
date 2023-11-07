open Core
open Compile
open Format
open Uuseg_string
open Reporter

(* We have two styles of output, compact and noncompact.  The caller can specify which to use with a reader effect. *)

module Compact = Algaeff.Reader.Make (struct
  type env = bool
end)

let compact = Compact.read
let compactly f = Compact.run ~env:true f
let noncompactly f = Compact.run ~env:false f

(* We save tables of pretty-printing functions indexed by notations, one for case trees and one for ordinary terms.  These functions should always put a box of some kind around their output. *)

let pp_terms : (Notation.t, formatter -> observation list -> unit) Hashtbl.t = Hashtbl.create 16

let add_term_pp (n : Notation.t) (pp : formatter -> observation list -> unit) =
  Hashtbl.add pp_terms n pp

let pp_cases : (Notation.t, formatter -> observation list -> unit) Hashtbl.t = Hashtbl.create 16

let add_case_pp (n : Notation.t) (pp : formatter -> observation list -> unit) =
  Hashtbl.add pp_cases n pp

(* Print a token, with arguments swapped so that it takes the token as an argument. *)
let pp_tok (ppf : formatter) (tok : Token.t) : unit = Token.pp tok ppf ()

(* Print a variable, with underscore for unnamed variables. *)
let pp_var : formatter -> string option -> unit =
  pp_print_option ~none:(Token.pp Underscore) pp_utf_8

(* Print constructors and fields *)
let pp_constr (ppf : formatter) (c : string) : unit = fprintf ppf "%a." pp_utf_8 c
let pp_field (ppf : formatter) (c : string) : unit = fprintf ppf ".%a" pp_utf_8 c

(* Print a parse tree interpreted as a term. *)
let rec pp_term (ppf : formatter) (tr : parse_tree) : unit =
  match tr with
  | Notn (n, obs) -> (
      match Hashtbl.find_opt pp_terms n with
      | Some pp -> pp ppf obs
      | None -> fatal (Anomaly "Unprintable notation"))
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
        pp_term body

and pp_spine (ppf : formatter) (tr : parse_tree) : unit =
  match tr with
  | App (head, arg) -> fprintf ppf "%a@ %a" pp_spine head pp_term arg
  | _ -> pp_term ppf tr

(* Print a parse tree interpreted as a case tree. *)
let rec pp_case (ppf : formatter) (tr : parse_tree) : unit =
  match tr with
  | Notn (n, obs) -> (
      match Hashtbl.find_opt pp_cases n with
      | Some pp -> pp ppf obs
      | None -> pp_term ppf tr)
  | Abs (cube, vars, body) ->
      fprintf ppf "@[<b 0>@[<hov 2>%a %a@]@ %a@]"
        (pp_print_list ~pp_sep:pp_print_space pp_var)
        vars pp_tok
        (match cube with
        | `Normal -> Mapsto
        | `Cube -> DblMapsto)
        pp_case body
  | _ -> pp_term ppf tr
