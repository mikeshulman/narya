open Notation
open Postprocess
open Format
open Print

(* See user.ml for discussion.  This function goes here to avoid a circular dependency. *)

let make_user : User.prenotation -> User.notation =
 fun (User { name; fixity; pattern; key; val_vars }) ->
  let n = make name fixity in
  let pat_vars = User.Pattern.vars pattern in
  set_tree n (User.tree n pattern);
  set_processor n
    { process = (fun ctx obs loc _ -> process_user key pat_vars val_vars ctx obs loc) };
  set_print n (fun space ppf obs ws ->
      pp_open_hvbox ppf 0;
      User.pp_user pattern n true ppf pattern obs ws `None;
      pp_close_box ppf ();
      pp_space ppf space);
  { key; notn = Wrap n; pat_vars; val_vars }
