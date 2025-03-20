open Term

(* Whether the -discreteness flag is on globally *)
module R = Algaeff.Reader.Make (Bool)

let () = R.register_printer (function `Read -> Some "unhandled Discreteness.read effect")
let enabled () = R.read ()
let run = R.run

(* Given a case tree definition, check whether it could be discrete, which means it's an abstracted datatype with all parameters/indices/constructor arguments discrete or currently being defined.  Return a version of it with discrete turned on for sure if possible, and a boolean indicating whether it could be discrete.  *)
let rec discrete_def : type b. (b, potential) term -> (b, potential) term * bool = function
  | Lam (x, body) ->
      let t, d = discrete_def body in
      (Lam (x, t), d)
  | Canonical (Data { indices; constrs; discrete = `Maybe }) ->
      (Canonical (Data { indices; constrs; discrete = `Yes }), true)
  | tm -> (tm, false)
