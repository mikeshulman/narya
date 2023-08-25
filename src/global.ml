open Term
open Dim

(* The global environment of constants *)

let types : (Constant.t, N.zero term) Hashtbl.t = Hashtbl.create 10
let trees : (Constant.t, N.zero Case.tree) Hashtbl.t = Hashtbl.create 10

type record =
  | Record : {
      (* Whether the record type supports eta-conversion *)
      eta : bool;
      (* The number of parameters of an instance of the record type *)
      params : 'a N.t;
      (* The dimension of the record type itself, as a type.  In nearly all cases this will be zero; the main exception is Gel/Corr. *)
      dim : 'n D.t;
      (* The fields are listed in order, so that each can depend on the previous ones.  Each field has a type that depends on the parameters of the record type, along with an element of that type and its boundaries if any. *)
      dim_faces : ('n, 'f) count_faces;
      params_plus : ('a, 'f, 'af) N.plus;
      fields : (Field.t * 'af term) list;
    }
      -> record

let records : (Constant.t, record) Hashtbl.t = Hashtbl.create 10

type field =
  | Field : {
      params : 'a N.t;
      dim : 'n D.t;
      dim_faces : ('n, 'f) count_faces;
      params_plus : ('a, 'f, 'af) N.plus;
      ty : 'af term;
    }
      -> field

let find_record_field : Constant.t -> Field.t -> field =
 fun name fld ->
  let (Record { eta = _; params; dim; dim_faces; params_plus; fields }) =
    Hashtbl.find records name in
  let _, ty = List.find (fun (f, _) -> f = fld) fields in
  Field { params; dim; dim_faces; params_plus; ty }
