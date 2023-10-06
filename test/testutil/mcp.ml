open Util
open Core
open Parser

(* The current context of assumptions, including names. *)
type ctx = Ctx : 'n Ctx.t * (string option, 'n) Bwv.t -> ctx

let ectx = Ctx (Ctx.empty, Emp)
let context = ref ectx

(* Functions to synth and check terms *)

let parse_term : type n. (string option, n) Bwv.t -> string -> (n Raw.check, string) result =
 fun names tm ->
  Result.bind (Parse.parse !Builtins.builtins tm) (fun res ->
      match Compile.compile names res with
      | None -> Error "Compilation error"
      | Some t -> Ok t)

module Term = Asai.Tty.Make (Core.Logger.Code)

let synth (tm : string) : Value.value * Value.value =
  let (Ctx (ctx, names)) = !context in
  match parse_term names tm with
  | Ok (Synth raw) ->
      Logger.run ~emit:Term.display ~fatal:(fun d ->
          Term.display d;
          raise (Failure "Failed to synthesize"))
      @@ fun () ->
      let syn, ty = Check.synth ctx raw in
      let esyn = Ctx.eval ctx syn in
      (esyn, ty)
  | Ok _ -> raise (Failure "Non-synthesizing")
  | Error str ->
      print_endline str;
      raise (Failure "Parse error")

let check (tm : string) (ty : Value.value) : Value.value =
  let (Ctx (ctx, names)) = !context in
  match parse_term names tm with
  | Ok raw ->
      Logger.run ~emit:Term.display ~fatal:(fun d ->
          Term.display d;
          raise (Failure "Failed to check"))
      @@ fun () ->
      let chk = Check.check ctx raw ty in
      Ctx.eval ctx chk
  | Error str ->
      print_endline str;
      raise (Failure "Parse error")

(* Assert that a term *doesn't* synthesize or check, and possibly ensure it gives a specific error code. *)

let unsynth ?code (tm : string) : unit =
  let (Ctx (ctx, names)) = !context in
  match parse_term names tm with
  | Ok (Synth raw) ->
      Logger.run ~emit:Term.display ~fatal:(fun d ->
          match code with
          | None -> ()
          | Some c ->
              if d.code = c then ()
              else (
                Term.display d;
                raise (Failure "Unexpected error code")))
      @@ fun () ->
      let _ = Check.synth ctx raw in
      raise (Failure "Synthesis success")
  | Ok _ -> raise (Failure "Non-synthesizing")
  | Error str ->
      print_endline str;
      raise (Failure "Parse error")

let uncheck ?code (tm : string) (ty : Value.value) : unit =
  let (Ctx (ctx, names)) = !context in
  match parse_term names tm with
  | Ok raw ->
      Logger.run ~emit:Term.display ~fatal:(fun d ->
          match code with
          | None -> ()
          | Some c ->
              if d.code = c then ()
              else (
                Term.display d;
                raise (Failure "Unexpected error code")))
      @@ fun () ->
      let _ = Check.check ctx raw ty in
      raise (Failure "Checking success")
  | Error str ->
      print_endline str;
      raise (Failure "Parse error")

(* Assert that a term doesn't parse *)

let unparse (tm : string) : unit =
  let (Ctx (_, names)) = !context in
  match parse_term names tm with
  | Ok _ -> raise (Failure "Unexpected parse success")
  | Error _ -> ()

(* Add to the context of assumptions *)

let assume (x : string) (ty : Value.value) : Value.value =
  let (Ctx (ctx, names)) = !context in
  context := Ctx (Ctx.ext ctx ty, Snoc (names, Some x));
  fst (synth x)

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
