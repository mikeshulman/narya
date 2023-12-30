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

(* Print the comments and newlines following a token. *)
let pp_ws (ppf : formatter) (ws : Whitespace.t list) : unit =
  let pp_newlines ppf n =
    for _ = 1 to n do
      pp_force_newline ppf ()
    done in
  let rec pp (ppf : formatter) (ws : Whitespace.t list) : unit =
    match ws with
    | [] -> fatal (Anomaly "empty list in pp_ws")
    | [ `Newlines n ] -> fprintf ppf "@]%a" pp_newlines n
    | [ `Line str ] -> fprintf ppf "`%s@]@\n" str
    | [ `Block str ] -> fprintf ppf "{`%s`}@]@\n" str
    | `Newlines n :: ws ->
        for _ = 1 to n do
          pp_print_cut ppf ()
        done;
        pp ppf ws
    | `Line str :: ws -> fprintf ppf "`%s@,%a" str pp ws
    | `Block str :: (`Line _ :: _ as ws) | `Block str :: (`Block _ :: _ as ws) ->
        fprintf ppf "{`%s`}@ %a" str pp ws
    | `Block str :: (`Newlines _ :: _ as ws) -> fprintf ppf "{`%s`}%a" str pp ws in
  match ws with
  | [] -> ()
  | [ `Newlines n ] -> if n >= 2 then pp_newlines ppf n else ()
  | `Newlines n :: ws -> fprintf ppf "%a@[<v 0>%a" pp_newlines n pp ws
  | _ -> fprintf ppf "@ @[<v 0>%a" pp ws

(* Print a parse tree. *)
let rec pp_term (ppf : formatter) (wtr : observation) : unit =
  let (Term tr) = wtr in
  match state () with
  | `Case -> (
      match tr with
      | Notn n -> pp_notn_case ppf (notn n) (args n) wtr
      | _ -> as_term @@ fun () -> pp_term ppf wtr)
  | `Term -> (
      match tr with
      | Notn n -> pp_notn ppf (notn n) (args n)
      | App _ -> fprintf ppf "@[<hov 2>%a@]" pp_spine wtr
      | Placeholder w ->
          pp_tok ppf Underscore;
          pp_ws ppf w
      | Ident (x, w) ->
          pp_utf_8 ppf (String.concat "." x);
          pp_ws ppf w
      | Constr (c, w) ->
          pp_constr ppf c;
          pp_ws ppf w
      | Field (f, w) ->
          pp_field ppf f;
          pp_ws ppf w)

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
  | Term (App { fn; arg; _ }) ->
      pp_spine ppf (Term fn);
      pp_print_space ppf ();
      pp_term ppf (Term arg)
  | _ -> pp_term ppf tr
