(* This module should not be opened, but used qualified. *)

open Util
open Term

type ('a, 'b, 'ab) t =
  | Emp : ('a, N.zero, 'a) t
  | Ext : 'a term * ('a N.suc, 'b, 'ab) t -> ('a, 'b N.suc, 'ab) t

let rec length : type a b ab. (a, b, ab) t -> b N.t = function
  | Emp -> Nat Zero
  | Ext (_, tel) -> N.suc (length tel)

let rec plus : type a b ab. (a, b, ab) t -> (a, b, ab) N.plus = function
  | Emp -> Zero
  | Ext (_, tel) -> N.suc_plus (plus tel)

let rec pis : type a b ab. (a, b, ab) t -> ab term -> a term =
 fun doms cod ->
  match doms with
  | Emp -> cod
  | Ext (dom, doms) -> pi dom (pis doms cod)
