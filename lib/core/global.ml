(* This module should not be opened, but used qualified. *)

open Util
open Reporter
open Syntax
open Term
open Dim
open Hctx

(* The global environment of constants *)

let types : (Constant.t, (emp, kinetic) term) Hashtbl.t = Hashtbl.create 10

(* Each constant either is an axiom, has a definition (a case tree), is a record (including coinductive ones), or is a datatype (including indexed ones). *)
type definition =
  | Axiom : definition
  | Defined : (emp, potential) term -> definition
  | Record : {
      (* Whether the type supports eta-conversion, i.e. whether it is really a record type or a codatatype. *)
      eta : potential eta;
      (* The number of parameters of an instance of the record type, which must also be the number of Pis in its type (which is where the types *of* the parameters are recorded). *)
      params : (emp, 'p, 'pc, D.zero) exts;
      (* The dimension of the record type itself, as a type.  In nearly all cases this will be zero; the main exception is Gel/Corr. *)
      dim : 'n D.t;
      (* The fields are listed in order, so that each can depend on the previous ones.  But instead of explicitly depending on those prevous fields as variables, each field has a type that depends on the parameters of the record type, along with an element of the record type itself (and its boundaries, if any), by way of projecting out its fields. *)
      fields : (Field.t, (('pc, 'n) ext, kinetic) term) Abwd.t;
    }
      -> definition
  | Data : {
      (* The number of parameters *)
      params : (emp, 'p, 'pc, D.zero) exts;
      (* The number of indices.  Together these sum to the number of Pis in its type.  *)
      indices : ('p, 'i, 'pi) N.plus;
      (* The constructors.  These are typechecked in order, but once the datatype is defined the order doesn't matter any more, so we store them in a map. *)
      constrs : ('pc, 'i) constr Constr.Map.t;
    }
      -> definition

(* A data constructor with 'p parameters and 'i indices.  Currently, all constructors are 0-dimensional, but we aim to generalize this to HITs in future. *)
and (_, _) constr =
  | Constr : {
      (* The types of the arguments, given the parameters of the datatype. *)
      args : ('p, 'a, 'pa) Telescope.t;
      (* The values of the indices, given the parameters and the arguments. *)
      indices : (('pa, kinetic) term, 'i) Bwv.t;
    }
      -> ('p, 'i) constr

let constants : (Constant.t, definition) Hashtbl.t = Hashtbl.create 10

type field =
  | Field : {
      name : Field.t;
      params : (emp, 'p, 'pc, D.zero) exts;
      dim : 'n D.t;
      ty : (('pc, 'n) ext, kinetic) term;
    }
      -> field

let find_record_field ?severity (const : Constant.t) (fld : Field.or_index) : field =
  match Hashtbl.find constants const with
  | Record { eta = _; params; dim; fields } -> (
      match fld with
      | `Name fld -> (
          match Abwd.find_opt fld fields with
          | Some ty -> Field { name = fld; params; dim; ty }
          | None -> fatal ?severity (No_such_field (`Record (PConstant const), `Name fld)))
      | `Index n -> (
          match Mbwd.fwd_nth_opt fields n with
          | Some (fld, ty) -> Field { name = fld; params; dim; ty }
          | None -> fatal ?severity (No_such_field (`Record (PConstant const), fld))))
  | _ -> fatal ?severity (No_such_field (`Nonrecord (PConstant const), fld))
