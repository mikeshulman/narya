module D = D

let to_int = D.to_int

include Arith
include Deg
include Sface
include Bwsface
include Cube
include Tface
include Bwtface
include Tube
include Face
include Op
include Insertion

(* ********** Special generators ********** *)

type one = D.one

let one = D.one
let refl : (one, D.zero) deg = Zero D.one
let zero_sface_one : (D.zero, one) sface = End (Zero, Pop Top)
let one_sface_one : (D.zero, one) sface = End (Zero, Top)

type two = D.two

let sym : (two, two) deg = Suc (Suc (Zero D.zero, Top), Pop Top)

type _ is_suc = Is_suc : 'n D.t * ('n, one, 'm) D.plus -> 'm is_suc

let suc_pos : type n. n D.pos -> n is_suc = fun (Pos n) -> Is_suc (n, Suc Zero)

let deg_of_name : string -> any_deg option = function
  | "refl" -> Some (Any refl)
  | "Id" -> Some (Any refl)
  | "sym" -> Some (Any sym)
  | _ -> None

let name_of_deg : type a b. (a, b) deg -> string option = function
  | Zero (Nat (Suc Zero)) -> Some "refl"
  | Suc (Suc (Zero (Nat Zero), Top), Pop Top) -> Some "sym"
  | _ -> None
