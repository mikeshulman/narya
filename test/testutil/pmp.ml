open Util
open Core
open Logger

(* Poor man's parser, reusing the OCaml parser to make a vaguely usable syntax *)

(* Abstract syntax terms with variable names *)
type pmt =
  | Var : string -> pmt
  | Const : string -> pmt
  | Field : pmt * string -> pmt
  | UU : pmt
  | Pi : string * pmt * pmt -> pmt
  | App : pmt * pmt -> pmt
  | Id : pmt * pmt * pmt -> pmt
  | Refl : pmt -> pmt
  | Sym : pmt -> pmt
  | Asc : pmt * pmt -> pmt
  | Lam : string * pmt -> pmt
  | Struct : (string * pmt) list -> pmt
  | Constr : string -> pmt

(* Using a Bwv of variable names, to turn them into De Bruijn indices, we can parse such a term into a synth/checkable one. *)
let rec parse_chk : type n. (string, n) Bwv.t -> pmt -> n Raw.check =
 fun ctx -> function
  | Lam (x, body) -> Lam (parse_chk (Snoc (ctx, x)) body)
  | Struct tms ->
      Struct
        (List.fold_left
           (fun acc (fld, tm) -> Field.Map.add (Field.intern fld) [ parse_chk ctx tm ] acc)
           Field.Map.empty tms)
  | Constr c -> Constr (Constr.intern c, Emp)
  | App (fn, arg) as tm -> (
      match parse_chk ctx fn with
      | Constr (c, args) -> Constr (c, Snoc (args, parse_chk ctx arg))
      | _ -> Synth (parse_syn ctx tm))
  | tm -> Synth (parse_syn ctx tm)

and parse_syn : type n. (string, n) Bwv.t -> pmt -> n Raw.synth =
 fun ctx -> function
  | Var x -> (
      match Bwv.index x ctx with
      | Some v -> Var v
      | None -> die Unbound_variable x)
  | Const x -> (
      match Scope.lookup x with
      | Some c -> Const c
      | None -> die Unbound_variable x)
  | UU -> Symbol (UU, Zero, Emp)
  | Field (x, fld) -> Field (parse_syn ctx x, Field.intern fld)
  | Pi (x, dom, cod) -> Pi (parse_chk ctx dom, parse_chk (Snoc (ctx, x)) cod)
  | App (fn, arg) -> App (parse_syn ctx fn, parse_chk ctx arg)
  | Id (a, x, y) ->
      App (App (Symbol (Refl, Zero, Snoc (Emp, parse_chk ctx a)), parse_chk ctx x), parse_chk ctx y)
  | Refl x -> Symbol (Refl, Zero, Snoc (Emp, parse_chk ctx x))
  | Sym x -> Symbol (Sym, Zero, Snoc (Emp, parse_chk ctx x))
  | Asc (tm, ty) -> Asc (parse_chk ctx tm, parse_chk ctx ty)
  | _ -> raise (Failure "Non-synthesizing")

(* Nicer syntax, with a prefix operator for using a variable by name, and infix operators for abstraction, application, and ascription. *)
let ( !! ) x = Var x
let ( !~ ) x = Const x
let ( !. ) x = Constr x

(* let pi x dom cod = Pi (x, dom, cod) *)
let ( @=> ) (x, dom) cod = Pi (x, dom, cod)
let ( $ ) fn arg = App (fn, arg) (* Left-associative *)
let id a x y = Id (a, x, y)
let refl x = Refl x
let sym x = Sym x
let ( <:> ) tm ty = Asc (tm, ty)
let ( @-> ) x body = Lam (x, body) (* Right-associative *)
let ( $. ) x fld = Field (x, fld)
let struc tms = Struct tms

module Terminal = Asai.Tty.Make (Core.Logger.Code)

(* The current context of assumptions, including names. *)
type ctx = Ctx : 'n Ctx.t * (string, 'n) Bwv.t -> ctx

let ectx = Ctx (Ctx.empty, Emp)
let context = ref ectx

(* Functions to synth and check terms *)

let synth (tm : pmt) : Value.value * Value.value =
  let (Ctx (ctx, names)) = !context in
  Logger.run ~emit:Terminal.display ~fatal:(fun d ->
      Terminal.display d;
      raise (Failure "Failed to synthesize"))
  @@ fun () ->
  let raw = parse_syn names tm in
  let syn, ty = Check.synth ctx raw in
  let esyn = Ctx.eval ctx syn in
  (esyn, ty)

let check (tm : pmt) (ty : Value.value) : Value.value =
  let (Ctx (ctx, names)) = !context in
  Logger.run ~emit:Terminal.display ~fatal:(fun d ->
      Terminal.display d;
      raise (Failure "Failed to check"))
  @@ fun () ->
  let raw = parse_chk names tm in
  let chk = Check.check ctx raw ty in
  Ctx.eval ctx chk

(* Assert that a term *doesn't* synthesize or check *)

let unsynth (tm : pmt) : unit =
  let (Ctx (ctx, names)) = !context in
  Logger.run ~emit:Terminal.display ~fatal:(fun _ -> ()) @@ fun () ->
  let raw = parse_syn names tm in
  let _ = Check.synth ctx raw in
  raise (Failure "Synthesis success")

let uncheck (tm : pmt) (ty : Value.value) : unit =
  let (Ctx (ctx, names)) = !context in
  Logger.run ~emit:Terminal.display ~fatal:(fun _ -> ()) @@ fun () ->
  let raw = parse_chk names tm in
  let _ = Check.check ctx raw ty in
  raise (Failure "Checking success")

(* Add to the context of assumptions *)

let assume (x : string) (ty : Value.value) : Value.value =
  let (Ctx (ctx, names)) = !context in
  context := Ctx (Ctx.ext ctx ty, Snoc (names, x));
  fst (synth !!x)

(* Check that two terms are, or aren't, equal, at a type or synthesizing *)

let equal_at (tm1 : Value.value) (tm2 : Value.value) (ty : Value.value) : unit =
  let (Ctx (ctx, _)) = !context in
  if Option.is_some (Equal.equal_at (Ctx.level ctx) tm1 tm2 ty) then ()
  else raise (Failure "Unequal terms")

let unequal_at (tm1 : Value.value) (tm2 : Value.value) (ty : Value.value) : unit =
  let (Ctx (ctx, _)) = !context in
  if Option.is_none (Equal.equal_at (Ctx.level ctx) tm1 tm2 ty) then ()
  else raise (Failure "Equal terms")

let equal (tm1 : Value.value) (tm2 : Value.value) : unit =
  let (Ctx (ctx, _)) = !context in
  if Option.is_some (Equal.equal_val (Ctx.level ctx) tm1 tm2) then ()
  else raise (Failure "Unequal terms")

let unequal (tm1 : Value.value) (tm2 : Value.value) : unit =
  let (Ctx (ctx, _)) = !context in
  if Option.is_none (Equal.equal_val (Ctx.level ctx) tm1 tm2) then ()
  else raise (Failure "Equal terms")

(* Infix notation for applying values *)

let ( $$ ) (fn : Value.value) (arg : Value.value) : Value.value =
  Norm.apply fn (Dim.CubeOf.singleton arg)

let run f =
  Logger.run ~emit:Terminal.display ~fatal:(fun d ->
      Terminal.display d;
      raise (Failure "Fatal error"))
  @@ fun () -> Scope.run f
