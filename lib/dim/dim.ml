module D = D
module Dmap = Util.Nmap

type dim_wrapped = Wrap : 'n D.t -> dim_wrapped

let is_pos : type n. n D.t -> bool = function
  | Nat Zero -> false
  | Nat (Suc _) -> true

module Endpoints = Endpoints
include Arith
include Deg
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
module Plusmap = Plusmap

type any_dim = Any : 'n D.t -> any_dim

let dim_of_string : string -> any_dim option =
 fun str -> Option.map (fun (Deg.Any s) -> Any (dom_deg s)) (deg_of_string str)

let string_of_dim : type n. n D.t -> string = fun n -> string_of_deg (deg_zero n)

(* ********** Special generators ********** *)

type one = D.one

let one = D.one
let refl : (one, D.zero) deg = Zero D.one

type two = D.two

let sym : (two, two) deg = Suc (Suc (Zero D.zero, Top), Pop Top)

type _ is_suc = Is_suc : 'n D.t * ('n, one, 'm) D.plus -> 'm is_suc

let suc_pos : type n. n D.pos -> n is_suc = fun (Pos n) -> Is_suc (n, Suc Zero)

let deg_of_name : string -> any_deg option =
 fun str ->
  if List.exists (fun s -> s = str) (Endpoints.refl_names ()) then Some (Any refl)
  else if str = "sym" then Some (Any sym)
  else None

let name_of_deg : type a b. (a, b) deg -> string option = function
  | Zero (Nat (Suc Zero)) -> (
      match Endpoints.refl_names () with
      | [] -> None
      | name :: _ -> Some name)
  | Suc (Suc (Zero (Nat Zero), Top), Pop Top) -> Some "sym"
  | _ -> None
