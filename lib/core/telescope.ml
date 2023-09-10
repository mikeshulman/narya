(* This module should nto be opened, but used qualified. *)

open Util
open Term

type ('a, 'b, 'ab) t =
  | Emp : ('a, N.zero, 'a) t
  | Ext : 'a term * ('a N.suc, 'b, 'ab) t -> ('a, 'b N.suc, 'ab) t

let rec length : type a b ab. (a, b, ab) t -> b N.t = function
  | Emp -> Nat Zero
  | Ext (_, tel) -> N.suc (length tel)
