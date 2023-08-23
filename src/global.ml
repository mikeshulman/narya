open Term

(* The global environment of constants *)

let types : (Constant.t, N.zero term) Hashtbl.t = Hashtbl.create 10
let trees : (Constant.t, N.zero Case.tree) Hashtbl.t = Hashtbl.create 10

(* A record type is a constant associated with a number of parameters together with a collection of fields, each of which has a type that depends on the parameters and also the term of the record type itself. *)

type record = Record : 'a N.t * (Field.t, 'a N.suc term) Hashtbl.t -> record

let records : (Constant.t, record) Hashtbl.t = Hashtbl.create 10

type field = Field : 'a N.t * 'a N.suc term -> field

let find_record : Constant.t -> Field.t -> field option =
 fun name fld ->
  let open Monad.Ops (Monad.Maybe) in
  let* (Record (k, fields)) = Hashtbl.find_opt records name in
  let* fldty = Hashtbl.find_opt fields fld in
  return (Field (k, fldty))
