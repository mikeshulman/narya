open Parser
open Notations
open Compile

(* Translate a parse observation into something that shows the names of notations rather than their internal abstract representations, for easier inspection and testing. *)

type obs = Flag of flag | Name of string option | Term of res

and res =
  | Notn of string * obs list
  | App of res * res
  | Name of string
  | Constr of string
  | Field of string
  | Numeral of float
  | Abs of string option list * res

let rec get_obs (obs : observation) : obs =
  match obs with
  | Flag f -> Flag f
  | Name x -> Name x
  | Term r -> Term (get_res r)

and get_res (r : result) : res =
  match r with
  | Notn (n, args) ->
      let d = get_data n in
      Notn (d.name, List.map get_obs args)
  | App (x, y) -> App (get_res x, get_res y)
  | Name x -> Name x
  | Constr x -> Constr x
  | Field x -> Field x
  | Numeral n -> Numeral n
  | Abs (vars, body) -> Abs (vars, get_res body)

let parse state str =
  match Parse.parse state str with
  | Left res -> Either.Left (get_res res)
  | Right err -> Right err
