open Core
open Reporter
open Notation
open Postprocess
open Print
open User
open PPrint

(* See user.ml for discussion.  This function goes here to avoid a circular dependency. *)

let make_user : User.prenotation -> User.notation =
 fun (User (type l t r) ({ name; fixity; pattern; key; val_vars } : (l, t, r) prenotation_data)) ->
  let module New = Make (struct
    type nonrec left = l
    type nonrec tight = t
    type nonrec right = r
  end) in
  let n = (New.User, fixity) in
  let pat_vars = User.Pattern.vars pattern in
  let inner_symbols = User.Pattern.inner_symbols pattern in
  make n
    {
      name;
      (* Convert a user notation pattern to a notation tree.  Note that our highly structured definition of the type of patterns, that enforces invariants statically, means that this function CANNOT FAIL. *)
      tree =
        (* We have to handle the beginning specially, since the start and end of a notation tree are different depending on whether it is left-open or left-closed.  So we have an internal recursive function that handles everything except the first operator symbol. *)
        (let rec go : type left l tight.
             (l, r) Pattern.t -> (tight, left) tree -> (tight, left) tree =
          fun pat n ->
           match pat with
           | Op_nil (tok, _) -> op tok n
           | Var_nil ((tok, _, _), _) -> op tok n
           | Op ((tok, _, _), pat) -> op tok (go pat n)
           | Var (_, Op ((tok, _, _), pat)) -> term tok (go pat n)
           | Var (_, Op_nil (tok, _)) -> term tok n
           | Var (_, Var_nil ((tok, _, _), _)) -> term tok n in
         match pattern with
         | Op_nil (tok, _) -> Closed_entry (eop tok (Done_closed n))
         | Var (_, Op ((tok, _, _), pat)) -> Open_entry (eop tok (go pat (done_open n)))
         | Var (_, Op_nil (tok, _)) -> Open_entry (eop tok (done_open n))
         | Var (_, Var_nil ((tok, _, _), _)) -> Open_entry (eop tok (done_open n))
         | Op ((tok, _, _), pat) -> Closed_entry (eop tok (go pat (Done_closed n)))
         | Var_nil ((tok, _, _), _) -> Closed_entry (eop tok (Done_closed n)));
      processor =
        (fun ctx obs loc ->
          let args =
            List.fold_left2
              (fun acc k -> function
                | Wrap x -> acc |> StringMap.add k (process ctx x))
              StringMap.empty pat_vars
              (List.filter_map
                 (function
                   | Term x -> Some (Wrap x)
                   | Token _ -> None)
                 obs) in
          let value =
            match key with
            | `Constant c ->
                let spine =
                  List.fold_left
                    (fun acc k ->
                      Raw.App
                        ( { value = acc; loc },
                          StringMap.find_opt k args <|> Anomaly "not found processing user",
                          Asai.Range.locate_opt None `Explicit ))
                    (Const c) val_vars in
                Raw.Synth spine
            | `Constr (c, _) ->
                let args = List.map (fun k -> StringMap.find k args) val_vars in
                Raw.Constr ({ value = c; loc }, args) in
          { value; loc });
      (* We define this function inline here so that it can match against the constructor New.User that was generated above by the inline Make functor application.  The only way I can think of to factor this function out (and, for instance, put it in user.ml instead of this file) would be to pass it a first-class module as an argument.  At the moment, that seems like unnecessary complication. *)
      print_term =
        Some
          (fun obs ->
            let rec go : type l r.
                bool -> (l, r) Pattern.t -> observation list -> document * Whitespace.t list =
             fun first pat obs ->
              match (pat, obs) with
              | Op ((op, br, _), pat), Token (op', wsop) :: obs when op = op' ->
                  let rest, ws = go false pat obs in
                  (Token.pp op ^^ pp_ws br wsop ^^ rest, ws)
              | Op_nil (op, _), [ Token (op', wsop) ] when op = op' -> (Token.pp op, wsop)
              | Var_nil ((op, opbr, _), _), [ Token (op', wsop); Term x ] when op = op' ->
                  (* Deal with right-associativity *)
                  let xdoc, xws =
                    match x.value with
                    | Notn ((New.User, _), d) -> go false pattern (args d)
                    | _ -> pp_term x in
                  (Token.pp op ^^ pp_ws opbr wsop ^^ xdoc, xws)
              | Var ((_, br, _), pat), Term x :: obs ->
                  (* Deal with left-associativity *)
                  let xdoc, xws =
                    match (first, x.value) with
                    | true, Notn ((New.User, _), d) -> go true pattern (args d)
                    | _ -> pp_term x in
                  let rest, ws = go false pat obs in
                  (xdoc ^^ pp_ws br xws ^^ rest, ws)
              | _ -> fatal (Anomaly ("invalid notation arguments for user notation: " ^ name)) in
            (* Note the choice here.  "group" means that the whole notation, including associative repetitions, must all fit on one line or all be broken.  Where it is broken depends on the space arguments in the notation, which specify where there are spaces and where breaks are allowed.  "align" says that if it is broken, later lines will line up below the starting point. *)
            let doc, ws = go true pattern obs in
            (align (group doc), ws));
      print_case = None;
      is_case = (fun _ -> false);
    };
  { key; notn = Wrap n; pat_vars; val_vars; inner_symbols }
