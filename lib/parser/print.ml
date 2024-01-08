open Core
open Format
open Uuseg_string
open Reporter
open Notation
open Printconfig

(* Print a token, with arguments swapped so that it takes the token as an argument. *)
let pp_tok (ppf : formatter) (tok : Token.t) : unit = Token.pp tok ppf ()

(* Print a variable, with underscore for unnamed variables. *)
let pp_var : formatter -> string option -> unit =
  pp_print_option ~none:(Token.pp Underscore) pp_utf_8

(* Print constructors and fields *)
let pp_constr (ppf : formatter) (c : string) : unit = fprintf ppf "%a." pp_utf_8 c
let pp_field (ppf : formatter) (c : string) : unit = fprintf ppf ".%a" pp_utf_8 c

(* Print a parse tree. *)
let rec pp_term (ppf : formatter) (wtr : observation) : unit =
  let (Term tr) = wtr in
  match state () with
  | `Case -> (
      match tr.value with
      | Notn n -> pp_notn_case ppf (notn n) (args n) wtr
      | _ -> as_term @@ fun () -> pp_term ppf wtr)
  | `Term -> (
      match tr.value with
      | Notn n -> pp_notn ppf (notn n) (args n)
      | App _ -> fprintf ppf "@[<hov 2>%a@]" pp_spine wtr
      | Placeholder -> pp_tok ppf Underscore
      | Ident x -> pp_utf_8 ppf (String.concat "." x)
      | Constr c -> pp_constr ppf c
      | Field f -> pp_field ppf f)

and pp_notn_case :
    type left tight right.
    formatter -> (left, tight, right) notation -> observation list -> observation -> unit =
 fun ppf n obs tr ->
  match print_as_case n with
  | Some pp -> pp ppf obs
  | None -> as_term @@ fun () -> pp_term ppf tr

and pp_notn :
    type left tight right. formatter -> (left, tight, right) notation -> observation list -> unit =
 fun ppf n obs ->
  match print n with
  | Some pp -> pp ppf obs
  | None -> fatal (Anomaly "Unprintable term")

and pp_spine (ppf : formatter) (tr : observation) : unit =
  match tr with
  | Term { value = App { fn; arg; _ }; _ } ->
      fprintf ppf "%a@ %a" pp_spine (Term fn) pp_term (Term arg)
  | _ -> pp_term ppf tr
