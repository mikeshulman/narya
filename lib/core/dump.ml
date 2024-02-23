(* This module should not be imported, but used qualified (including its constructor names for printable). *)

open Dim
open Util
open Reporter
open Format
open Syntax
open Value
open Term

(* Functions to dump a partial direct representation of various kinds of syntax, avoiding the machinery of readback, unparsing, etc. that's needed for ordinary pretty-printing.  Intended only for debugging. *)

type printable +=
  | Val : value -> printable
  | Uninst : uninst -> printable
  | Head : head -> printable
  | Binder : 'b binder -> printable
  | Term : 'b term -> printable
  | Env : ('n, 'b) env -> printable

let dim : formatter -> 'a D.t -> unit =
 fun ppf d -> fprintf ppf "%d" (String.length (string_of_deg (id_deg d)))

let rec value : formatter -> value -> unit =
 fun ppf v ->
  match v with
  | Uninst (tm, _) -> fprintf ppf "Uninst (%a, ?)" uninst tm
  | Inst { tm; dim = d; args = _; tys = _ } ->
      fprintf ppf "Inst (%a, %a, ?, ?)" uninst tm dim (D.pos d)
  | Lam (_, _) -> fprintf ppf "Lam ?"
  | Struct (f, _) -> fprintf ppf "Struct (%a)" fields f
  | Constr (_, _, _) -> fprintf ppf "Constr ?"

and fields : formatter -> (Field.t, tree_value Lazy.t * [ `Labeled | `Unlabeled ]) Abwd.t -> unit =
 fun ppf -> function
  | Emp -> fprintf ppf "Emp"
  | Snoc (flds, (f, ((lazy v), l))) ->
      fprintf ppf "%a <: (%s, %a, %s)" fields flds (Field.to_string f) tree_value v
        (match l with
        | `Unlabeled -> "`Unlabeled"
        | `Labeled -> "`Labeled")

and tree_value : formatter -> tree_value -> unit =
 fun ppf v ->
  match v with
  | True_neutral -> fprintf ppf "True_neutral"
  | Leaf v -> fprintf ppf "Leaf (%a)" value v
  | Noleaf v -> fprintf ppf "Noleaf (%a)" value v

and uninst : formatter -> uninst -> unit =
 fun ppf u ->
  match u with
  | UU n -> fprintf ppf "UU %a" dim n
  | Pi (_, _, _) -> fprintf ppf "Pi ?"
  | Neu { head = h; args = _; alignment = al } -> fprintf ppf "Neu (%a, ?, %a)" head h alignment al

and alignment : formatter -> alignment -> unit =
 fun ppf al ->
  match al with
  | True -> fprintf ppf "True"
  | Chaotic v -> fprintf ppf "Chaotic (%a)" value v

and head : formatter -> head -> unit =
 fun ppf h ->
  match h with
  | Var _ -> fprintf ppf "Var ?"
  | Const { name; ins } ->
      fprintf ppf "Const (%a, %s)" pp_printed (print (PConstant name))
        (string_of_deg (perm_of_ins ins))

and binder : type b. formatter -> b binder -> unit =
 fun ppf (Bind { env = e; perm; plus_dim = _; body; args = _ }) ->
  fprintf ppf "Binder (%a, %s, ?, %a ,?)" env e (string_of_deg perm) term body

and env : type b n. formatter -> (n, b) env -> unit =
 fun ppf e ->
  match e with
  | Emp d -> fprintf ppf "Emp %a" dim d
  | Ext (e, _) -> fprintf ppf "%a <: ?" env e
  | Act (e, Op (f, d)) -> fprintf ppf "%a <* (%s,%s)" env e (string_of_sface f) (string_of_deg d)

and term : type b. formatter -> b term -> unit =
 fun ppf tm ->
  match tm with
  | Var _ -> fprintf ppf "Var ?"
  | Const c -> fprintf ppf "Const %a" pp_printed (print (PConstant c))
  | Field (tm, fld) -> fprintf ppf "Field (%a, %s)" term tm (Field.to_string fld)
  | UU n -> fprintf ppf "UU %s" (string_of_deg (id_deg n))
  | Inst (tm, _) -> fprintf ppf "Inst (%a, ?)" term tm
  | Pi (_, _, _) -> fprintf ppf "Pi (?, ?, ?)"
  | App (fn, _) -> fprintf ppf "App (%a, ?)" term fn
  | Lam (_, _, body) -> fprintf ppf "Lam (?, ?, %a)" term body
  | Constr (c, _, _) -> fprintf ppf "Constr (%s, ?, ?)" (Constr.to_string c)
  | Act (tm, s) -> fprintf ppf "Act (%a, %s)" term tm (string_of_deg s)
  | Let (_, _, _) -> fprintf ppf "Let (?,?,?)"
  | Struct (_, _) -> fprintf ppf "Struct (?,?)"
  | Match (_, _, _) -> fprintf ppf "Match (?,?,?)"
  | Leaf tm -> fprintf ppf "Leaf %a" term tm
