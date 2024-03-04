(* This module should not be opened, but used qualified. *)

open Util
open Tbwd
open Syntax
open Term

(* The global environment of constants *)

let types : (Constant.t, (emp, kinetic) term) Hashtbl.t = Hashtbl.create 10

(* Each constant either is an axiom or has a definition (a case tree).  The latter includes canonical types. *)
type definition = Axiom | Defined of (emp, potential) term

let constants : (Constant.t, definition) Hashtbl.t = Hashtbl.create 10
