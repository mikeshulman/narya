open Notation
open Postprocess
open Format
open Print

let make_user : User.prenotation -> User.notation =
 fun (User { name; fixity; pattern; key; val_vars }) ->
  let n = make name fixity in
  let pat_vars =
    List.filter_map
      (function
        | `Op _ | `Ellipsis _ -> None
        | `Var (x, _, _) -> Some x)
      pattern in
  set_tree n (User.tree fixity n pattern);
  set_processor n
    { process = (fun ctx obs loc _ -> process_user key pat_vars val_vars ctx obs loc) };
  set_print n (fun space ppf obs ws ->
      pp_open_hvbox ppf 0;
      pp_user pattern n true ppf pattern obs ws `None;
      pp_close_box ppf ();
      pp_space ppf space);
  { key; notn = Wrap n; pat_vars; val_vars }
