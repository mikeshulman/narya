open Util
open Dim
open Core
open Parser
open Norm
open Check
open Value
open Term
open Raw

let parse_term (tm : string) : (N.zero check, string) result =
  Result.bind (Parse.parse !Builtins.builtins tm) (fun res ->
      match Compile.compile Emp res with
      | None -> Error "Compilation error"
      | Some t -> Ok t)

let must_parse_term (tm : string) : N.zero check =
  match parse_term tm with
  | Ok t -> t
  | Error e ->
      print_endline e;
      raise (Failure "Parse error")

module Terminal = Asai.Tty.Make (Core.Logger.Code)

let check_type (rty : N.zero check) : N.zero term =
  Logger.run ~emit:Terminal.display ~fatal:(fun d ->
      Terminal.display d;
      raise (Failure "Failed to check type"))
  @@ fun () -> check Ctx.empty rty (universe D.zero)

let check_term (rtm : N.zero check) (ety : value) : N.zero term =
  Logger.run ~emit:Terminal.display ~fatal:(fun d ->
      Terminal.display d;
      raise (Failure "Failed to check term"))
  @@ fun () -> check Ctx.empty rtm ety

let assume (name : string) (ty : string) : unit =
  let const = Constant.intern name in
  if Hashtbl.mem Global.types const then raise (Failure ("Constant " ^ name ^ " already defined"))
  else
    let rty = must_parse_term ty in
    let cty = check_type rty in
    Hashtbl.add Global.types const cty;
    Hashtbl.add Global.constants const Axiom

let def (name : string) (ty : string) (tm : string) : unit =
  let const = Constant.intern name in
  if Hashtbl.mem Global.types const then raise (Failure ("Constant " ^ name ^ " already defined"))
  else
    let rty = must_parse_term ty in
    let rtm = must_parse_term tm in
    let cty = check_type rty in
    let ety = eval (Emp D.zero) cty in
    Hashtbl.add Global.types const cty;
    let tree = ref Case.Empty in
    Hashtbl.add Global.constants const (Defined tree);
    let hd = eval (Emp D.zero) (Const const) in
    Logger.run ~emit:Terminal.display ~fatal:(fun d ->
        Hashtbl.remove Global.types const;
        Hashtbl.remove Global.constants const;
        Terminal.display d;
        raise (Failure "Failed to check type"))
    @@ fun () -> check_tree Ctx.empty rtm ety hd tree

let undef (name : string) : unit =
  let const = Constant.intern name in
  Hashtbl.remove Global.types const;
  Hashtbl.remove Global.constants const

let equal_at (tm1 : string) (tm2 : string) (ty : string) : unit =
  let rty = must_parse_term ty in
  let rtm1 = must_parse_term tm1 in
  let rtm2 = must_parse_term tm2 in
  let cty = check_type rty in
  let ety = eval (Emp D.zero) cty in
  let ctm1 = check_term rtm1 ety in
  let ctm2 = check_term rtm2 ety in
  let etm1 = eval (Emp D.zero) ctm1 in
  let etm2 = eval (Emp D.zero) ctm2 in
  match Equal.equal_at 0 etm1 etm2 ety with
  | None -> raise (Failure "Unequal terms")
  | Some () -> ()

let unequal_at (tm1 : string) (tm2 : string) (ty : string) : unit =
  let rty = must_parse_term ty in
  let rtm1 = must_parse_term tm1 in
  let rtm2 = must_parse_term tm2 in
  let cty = check_type rty in
  let ety = eval (Emp D.zero) cty in
  let ctm1 = check_term rtm1 ety in
  let ctm2 = check_term rtm2 ety in
  let etm1 = eval (Emp D.zero) ctm1 in
  let etm2 = eval (Emp D.zero) ctm2 in
  match Equal.equal_at 0 etm1 etm2 ety with
  | None -> ()
  | Some () -> raise (Failure "Equal terms")
