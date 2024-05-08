open Syntax
open Term

(* See Galaxy for general explanation.  However, for dependency reasons, we have to be able to write code that looks up up metavariables in the Galactic state (e.g. when normalizing) before we can have imported the whole Galactic state module (since it uses Termctx, among other things).  So here we define a special effect that can be used for this purpose, and then later in Galaxy.run we trap this effect and turn it into an actual lookup. *)

type ('b, 's) found = { tm : ('b, 's) term option; ty : ('b, kinetic) term; energy : 's energy }
type _ Effect.t += Find : ('b, 's) Meta.t -> ('b, 's) found option Effect.t

let find meta = Effect.perform (Find meta)
