open Util
open Dim
open Core
open Parser
open Norm
open Check
open Value
open Term
open Raw
open Hctx

let parse_term (tm : string) : N.zero check =
  let (Wrap tm) = Parse.term !Builtins.builtins tm in
  Compile.compile Emp tm

module Terminal = Asai.Tty.Make (Core.Reporter.Code)

let check_type (rty : N.zero check) : emp term =
  Reporter.trace "when checking type" @@ fun () -> check Ctx.empty rty (universe D.zero)

let check_term (rtm : N.zero check) (ety : value) : emp term =
  Reporter.trace "when checking term" @@ fun () -> check Ctx.empty rtm ety

let assume (name : string) (ty : string) : unit =
  match Parser.Lexer.Parser.single name with
  | Some (Ident name) ->
      let const = Scope.define name in
      if Hashtbl.mem Global.types const then
        (* TODO: This should be an Asai message *)
        raise (Failure ("Constant " ^ name ^ " already defined"))
      else
        let rty = parse_term ty in
        let cty = check_type rty in
        Hashtbl.add Global.types const cty;
        Hashtbl.add Global.constants const Axiom
  | _ ->
      (* TODO: This should be an Asai message *)
      raise (Failure (Printf.sprintf "\"%s\" is not a valid constant name" name))

let def (name : string) (ty : string) (tm : string) : unit =
  match Parser.Lexer.Parser.single name with
  | Some (Ident name) ->
      Reporter.tracef "when defining %s" name @@ fun () ->
      let const = Scope.define name in
      if Hashtbl.mem Global.types const then
        (* TODO: This should be an Asai message *)
        raise (Failure ("Constant " ^ name ^ " already defined"))
      else
        let rty = parse_term ty in
        let rtm = parse_term tm in
        let cty = check_type rty in
        let ety = eval (Emp D.zero) cty in
        Hashtbl.add Global.types const cty;
        let tree = ref Case.Empty in
        Hashtbl.add Global.constants const (Defined tree);
        let hd = eval (Emp D.zero) (Const const) in
        Reporter.try_with ~fatal:(fun d ->
            Hashtbl.remove Global.types const;
            Hashtbl.remove Global.constants const;
            Reporter.fatal_diagnostic d)
        @@ fun () ->
        Reporter.trace "when checking case tree" @@ fun () -> check_tree Ctx.empty rtm ety hd tree
  | _ ->
      (* TODO: This should be an Asai message *)
      raise (Failure (Printf.sprintf "\"%s\" is not a valid constant name" name))

let undef (name : string) : unit =
  match Scope.lookup name with
  | Some const ->
      Hashtbl.remove Global.types const;
      Hashtbl.remove Global.constants const
  | None -> raise (Failure ("Can't undefine undefined constant " ^ name))

let equal_at (tm1 : string) (tm2 : string) (ty : string) : unit =
  let rty = parse_term ty in
  let rtm1 = parse_term tm1 in
  let rtm2 = parse_term tm2 in
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
  let rty = parse_term ty in
  let rtm1 = parse_term tm1 in
  let rtm2 = parse_term tm2 in
  let cty = check_type rty in
  let ety = eval (Emp D.zero) cty in
  let ctm1 = check_term rtm1 ety in
  let ctm2 = check_term rtm2 ety in
  let etm1 = eval (Emp D.zero) ctm1 in
  let etm2 = eval (Emp D.zero) ctm2 in
  match Equal.equal_at 0 etm1 etm2 ety with
  | None -> ()
  | Some () -> raise (Failure "Equal terms")

let run f =
  Reporter.run ~emit:Terminal.display ~fatal:(fun d ->
      Terminal.display d;
      raise (Failure "Fatal error"))
  @@ fun () -> Scope.run f
