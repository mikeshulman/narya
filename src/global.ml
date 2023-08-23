open Term

(* The global environment of constants *)

let types : (Constant.t, N.zero term) Hashtbl.t = Hashtbl.create 10
let trees : (Constant.t, N.zero Case.tree) Hashtbl.t = Hashtbl.create 10

(* A record type is a constant associated with a number of parameters together with a collection of fields, each of which has a type that depends on the parameters and also the term of the record type itself.  It also remembers whether the record admits eta-conversion. *)

type eta = Eta | Noeta
type record = Record : eta * 'a N.t * (Field.t * 'a N.suc term) list -> record

let records : (Constant.t, record) Hashtbl.t = Hashtbl.create 10

type field = Field : 'a N.t * 'a N.suc term -> field

let find_record_field : Constant.t -> Field.t -> field =
 fun name fld ->
  let (Record (_, k, fields)) = Hashtbl.find records name in
  let _, fldty = List.find (fun (f, _) -> f = fld) fields in
  Field (k, fldty)
