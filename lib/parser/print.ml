open Core
open Format
open Uuseg_string
open Reporter
open Notation

(* We have two styles of output, compact and noncompact.  The caller can specify which to use with a reader effect.  We also have two different printing states, for case trees and terms. *)

type style = Compact | Noncompact
type context = Term | Case

module Reader = Algaeff.Reader.Make (struct
  type t = style * context
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
let rec pp_term (ppf : formatter) (wtr : observation) : unit =
  let (Term tr) = wtr in
  match state () with
  | Case -> (
      match tr with
      | Notn n -> pp_notn_case ppf (notn n) (args n) wtr
      | _ -> as_term @@ fun () -> pp_term ppf wtr)
  | Term -> (
      match tr with
      | Notn n -> pp_notn ppf (notn n) (args n)
      | App _ -> fprintf ppf "@[<hov 2>%a@]" pp_spine wtr
      | Placeholder -> pp_tok ppf Underscore
      | Ident x -> pp_utf_8 ppf x
      | Constr c -> pp_constr ppf c
      | Field f -> pp_field ppf f
      | Numeral n -> Q.pp_print ppf n)

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
  | Term (App { fn; arg; _ }) -> fprintf ppf "%a@ %a" pp_spine (Term fn) pp_term (Term arg)
  | _ -> pp_term ppf tr

let pp_as_term style f = Reader.run ~env:(style, Term) f
let pp_as_case style f = Reader.run ~env:(style, Case) f
