module D = D
module Dmap = Util.Nmap

type dim_wrapped = Wrap : 'n D.t -> dim_wrapped

let is_pos : type n. n D.t -> bool = function
  | Nat Zero -> false
  | Nat (Suc _) -> true

module Endpoints = Endpoints
include Arith
include Singleton
include Deg
include Perm
include Sface
include Bwsface
include Cube
include Tface
include Bwtface
include Tube
include Icube
include Face
include Op
include Insertion
include Shuffle
include Pbij
module Plusmap = Plusmap

type any_dim = Any : 'n D.t -> any_dim

let dim_of_string : string -> any_dim option =
 fun str -> Option.map (fun (Any_deg s) -> Any (dom_deg s)) (deg_of_string str)

let string_of_dim : type n. n D.t -> string = fun n -> string_of_deg (deg_zero n)

(* ********** Special generators ********** *)

let refl : (one, D.zero) deg = Zero D.one

type two = D.two

let sym : (two, two) deg = Suc (Suc (Zero D.zero, Now), Later Now)

let deg_of_name : string -> any_deg option =
 fun str ->
  if List.exists (fun s -> s = str) (Endpoints.refl_names ()) then Some (Any_deg refl)
  else if str = "sym" then Some (Any_deg sym)
  else None

let name_of_deg : type a b. (a, b) deg -> string option = function
  | Zero (Nat (Suc Zero)) -> (
      match Endpoints.refl_names () with
      | [] -> None
      | name :: _ -> Some name)
  | Suc (Suc (Zero (Nat Zero), Now), Later Now) -> Some "sym"
  | _ -> None
