open Util
open Tbwd
open Dim
open Core
open Readback
open Reporter
open Parser
open Unparse
open Print
open Norm
open Check
open Syntax
open Term
open Value
open Raw
open Asai.Range

let () = Arity.install ()

let parse_term (tm : string) : N.zero check located =
  let p = Parse.Term.parse (`String { content = tm; title = Some "user-supplied term" }) in
  let (Term tm) = Parse.Term.final p in
  Postprocess.process Emp tm

module Terminal = Asai.Tty.Make (Core.Reporter.Code)

let check_type (rty : N.zero check located) : (emp, kinetic) term =
  Reporter.trace "when checking type" @@ fun () ->
  check (Kinetic `Nolet) Ctx.empty rty (universe D.zero)

let check_term (rtm : N.zero check located) (ety : kinetic value) : (emp, kinetic) term =
  Reporter.trace "when checking term" @@ fun () -> check (Kinetic `Nolet) Ctx.empty rtm ety

let assume (name : string) (ty : string) : unit =
  let p = Parse.Term.parse (`String { title = Some "constant name"; content = name }) in
  match Parse.Term.final p with
  | Term { value = Ident (name, _); _ } ->
      Scope.check_name name None;
      let const = Scope.define Compunit.basic name in
      Reporter.try_with ~fatal:(fun d ->
          Scope.modify_visible (Yuujinchou.Language.except name);
          Scope.modify_export (Yuujinchou.Language.except name);
          Reporter.fatal_diagnostic d)
      @@ fun () ->
      let rty = parse_term ty in
      let cty = check_type rty in
      Global.add const cty (Axiom `Nonparametric)
  | _ -> fatal (Invalid_constant_name name)

let def (name : string) (ty : string) (tm : string) : unit =
  let p = Parse.Term.parse (`String { title = Some "constant name"; content = name }) in
  match Parse.Term.final p with
  | Term { value = Ident (name, _); _ } ->
      Reporter.tracef "when defining %s" (String.concat "." name) @@ fun () ->
      Scope.check_name name None;
      let const = Scope.define Compunit.basic name in
      Reporter.try_with ~fatal:(fun d ->
          Scope.modify_visible (Yuujinchou.Language.except name);
          Scope.modify_export (Yuujinchou.Language.except name);
          Reporter.fatal_diagnostic d)
      @@ fun () ->
      let rty = parse_term ty in
      let rtm = parse_term tm in
      let cty = check_type rty in
      let ety = eval_term (Emp D.zero) cty in
      Reporter.trace "when checking case tree" @@ fun () ->
      Global.add const cty (Axiom `Parametric);
      let tree = check (Potential (Constant const, Emp, fun x -> x)) Ctx.empty rtm ety in
      Global.add const cty (Defined tree)
  | _ -> fatal (Invalid_constant_name name)

let equal_at (tm1 : string) (tm2 : string) (ty : string) : unit =
  let rty = parse_term ty in
  let rtm1 = parse_term tm1 in
  let rtm2 = parse_term tm2 in
  let cty = check_type rty in
  let ety = eval_term (Emp D.zero) cty in
  let ctm1 = check_term rtm1 ety in
  let ctm2 = check_term rtm2 ety in
  let etm1 = eval_term (Emp D.zero) ctm1 in
  let etm2 = eval_term (Emp D.zero) ctm2 in
  match Equal.equal_at 0 etm1 etm2 ety with
  | None -> raise (Failure "Unequal terms")
  | Some () -> ()

let unequal_at (tm1 : string) (tm2 : string) (ty : string) : unit =
  let rty = parse_term ty in
  let rtm1 = parse_term tm1 in
  let rtm2 = parse_term tm2 in
  let cty = check_type rty in
  let ety = eval_term (Emp D.zero) cty in
  let ctm1 = check_term rtm1 ety in
  let ctm2 = check_term rtm2 ety in
  let etm1 = eval_term (Emp D.zero) ctm1 in
  let etm2 = eval_term (Emp D.zero) ctm2 in
  match Equal.equal_at 0 etm1 etm2 ety with
  | None -> ()
  | Some () -> raise (Failure "Equal terms")

let print (tm : string) : unit =
  let rtm = parse_term tm in
  match rtm with
  | { value = Synth rtm; loc } ->
      let ctm, ety = synth (Kinetic `Nolet) Ctx.empty { value = rtm; loc } in
      let etm = eval_term (Emp D.zero) ctm in
      Display.run ~env:true @@ fun () ->
      let btm = readback_at Ctx.empty etm ety in
      let utm = unparse Names.empty btm Interval.entire Interval.entire in
      pp_term `None Format.std_formatter (Term utm);
      Format.pp_print_newline Format.std_formatter ()
  | _ -> fatal (Nonsynthesizing "argument of print")

let run f =
  Parser.Unparse.install ();
  Eternity.run ~init:Eternity.empty @@ fun () ->
  Global.run ~init:Global.empty @@ fun () ->
  Builtins.run @@ fun () ->
  Printconfig.run ~env:{ style = `Compact; state = `Term; chars = `Unicode } @@ fun () ->
  Readback.Display.run ~env:false @@ fun () ->
  Discrete.run ~env:false @@ fun () ->
  Compunit.Current.run ~env:Compunit.basic @@ fun () ->
  Reporter.run ~emit:Terminal.display ~fatal:(fun d ->
      Terminal.display d;
      raise (Failure "Fatal error"))
  @@ fun () ->
  let init_visible = Parser.Pi.install Scope.Trie.empty in
  Scope.run ~init_visible @@ fun () -> f ()

let gel_install () =
  def "Gel" "(A B : Type) (R : A → B → Type) → Id Type A B" "A B R ↦ sig a b ↦ ( ungel : R a b )"
