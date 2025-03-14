open Parser
open Notation

let make op name tree =
  make op
    {
      name;
      tree;
      processor = (fun _ _ _ -> raise (Failure "no arith processor"));
      print_term = None;
      print_case = None;
      is_case = (fun _ -> false);
    }
