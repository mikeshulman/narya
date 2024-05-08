(* This module should not be opened, but used qualified. *)

open Syntax
open Term

(* In contrast to the "Global" state which stores constants and their definitions, the "Galactic" state stores metavariables and their definitions.  We think of this as "outside" the global state because, firstly, metavariables aren't scoped and aren't affected by import and sectioning commands, but even more importantly, each metavariable stores its own copy of the Global state when it was created.  This way we can be sure that any solution of that metavariable  would have been valid in its original location. *)

type (_, _) data =
  | Data : {
      varscope : 'a Varscope.t;
      (* TODO: Global state. *)
      termctx : ('a, 'b) Termctx.t;
      ty : ('b, kinetic) term;
      tm : ('b, 's) term option;
      energy : 's energy;
    }
      -> (unit, 'b * 's) data

(* As with Global, we track Galactic state using a State effect.  In this case, the state is an intrinsically well-typed map, since metavariables are parametrized by their context length and energy. *)

module Data = struct
  type ('x, 'bs) t = ('x, 'bs) data
end

module M = Meta.Map.Make (Data)

module S = Algaeff.State.Make (struct
  type t = unit M.t
end)

let find_opt v = M.find_opt (MetaKey v) (S.get ())
let add v x = S.modify (M.add (MetaKey v) x)
let update v f = S.modify (M.update (MetaKey v) f)

(* When running in a new Galactic state, we also trap the temporary lookup effect from Galaxy1 and turn it into an actual lookup. *)
let run_empty f =
  let open Effect.Deep in
  S.run ~init:M.empty @@ fun () ->
  try_with f ()
    {
      effc =
        (fun (type a) (eff : a Effect.t) ->
          match eff with
          | Galaxy1.Find v ->
              Some
                (fun (k : (a, _) continuation) ->
                  match find_opt v with
                  | Some (Data { ty; tm; energy; _ }) -> continue k (Some { ty; tm; energy })
                  | None -> continue k None)
          | _ -> None);
    }
