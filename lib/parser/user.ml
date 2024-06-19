open Notation

(* User notations *)

module PrintKey = struct
  type t = [ `Constant of Core.Constant.t | `Constr of Core.Constr.t * int ]

  let compare : t -> t -> int = compare
end

module PrintMap = Map.Make (PrintKey)

type permuted_notation = { notn : Notation.t; pat_vars : string list; val_vars : string list }
