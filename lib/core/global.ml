(* This module should not be opened, but used qualified. *)

open Util
open Logger
open Term
open Dim

(* The global environment of constants *)

let types : (Constant.t, N.zero term) Hashtbl.t = Hashtbl.create 10

(* Each constant either is an axiom, has a definition (a case tree), is a record (including coinductive ones), or is a datatype (including indexed ones). *)
type definition =
  | Axiom : definition
  | Defined : N.zero Case.tree -> definition
  | Record : {
      (* Whether the record type supports eta-conversion *)
      eta : bool;
      (* The number of parameters of an instance of the record type, which must also be the number of Pis in its type (which is where the types *of* the parameters are recorded). *)
      params : 'p N.t;
      (* The dimension of the record type itself, as a type.  In nearly all cases this will be zero; the main exception is Gel/Corr. *)
      dim : 'n D.t;
      (* The fields are listed in order, so that each can depend on the previous ones.  Each field has a type that depends on the parameters of the record type, along with an element of that type and its boundaries if any. *)
      dim_faces : ('n, 'f) count_faces;
      params_plus : ('p, 'f, 'pf) N.plus;
      fields : (Field.t * 'pf term) list;
    }
      -> definition
  | Data : {
      (* The number of parameters *)
      params : 'p N.t;
      (* The number of indices.  Together these sum to the number of Pis in its type.  *)
      indices : ('p, 'i, 'pi) N.plus;
      (* The constructors.  These are typechecked in order, but once the datatype is defined the order doesn't matter any more, so we store them in a map. *)
      constrs : ('p, 'i) constr Constr.Map.t;
    }
      -> definition

(* A data constructor with 'p parameters and 'i indices.  Currently, all constructors are 0-dimensional, but we aim to generalize this to HITs in future. *)
and (_, _) constr =
  | Constr : {
      (* The types of the arguments, given the parameters of the datatype. *)
      args : ('p, 'a, 'pa) Telescope.t;
      (* The values of the indices, given the parameters and the arguments. *)
      indices : ('pa term, 'i) Bwv.t;
    }
      -> ('p, 'i) constr

let constants : (Constant.t, definition) Hashtbl.t = Hashtbl.create 10

(* TODO: More generally, any function on a fully general instance of some canonical type can be declared a "method" and parsed and typechecked like a field, with the argument and all its parameters synthesizing.  Similarly, any function into an instance of a canonical type with some of its arguments fully general can be declared a "generator" and parsed and typechecked like a constructor, with those arguments as "parameters" that are checked and hence can be omitted.  *)

type field =
  | Field : {
      params : 'p N.t;
      dim : 'n D.t;
      dim_faces : ('n, 'f) count_faces;
      params_plus : ('p, 'f, 'pf) N.plus;
      ty : 'pf term;
    }
      -> field

let find_record_field ?severity (name : Constant.t) (fld : Field.t) : field =
  match Hashtbl.find constants name with
  | Record { eta = _; params; dim; dim_faces; params_plus; fields } -> (
      match List.find_opt (fun (f, _) -> f = fld) fields with
      | Some (_, ty) -> Field { params; dim; dim_faces; params_plus; ty }
      | None -> die ?severity (No_such_field (Some name, fld)))
  | _ -> die ?severity (No_such_field (None, fld))
