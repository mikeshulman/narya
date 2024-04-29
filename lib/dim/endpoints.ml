open Util

(* We parametrize over an abstract module specifying how many endpoints our cubes have. *)

type 'l len = ..
type wrapped = Wrap : 'l len -> wrapped
type 'l t = 'l len * 'l N.index

module type Data_sig = sig
  val wrapped : unit -> wrapped
  val uniq : 'l1 'l2. 'l1 len -> 'l2 len -> ('l1, 'l2) Eq.t
  val len : 'l len -> 'l N.t
end

module Data_unset = struct
  let wrapped : unit -> wrapped = fun _ -> raise (Failure "arity unset (wrapped)")

  let uniq : type l1 l2. l1 len -> l2 len -> (l1, l2) Eq.t =
   fun _ _ -> raise (Failure "arity unset (uniq)")

  let len : type l. l len -> l N.t = fun _ -> raise (Failure "arity unset (len)")
end

module type Nat = sig
  type t

  val len : t N.t
end

module Zero : Nat = struct
  type t = N.zero

  let len = N.zero
end

module Suc (X : Nat) : Nat = struct
  type t = X.t N.suc

  let len = N.suc X.len
end

let rec module_of_int (x : int) =
  if x < 0 then raise (Invalid_argument "module_of_int")
  else if x = 0 then (module Zero : Nat)
  else
    let module X = (val module_of_int (x - 1) : Nat) in
    (module Suc (X) : Nat)

module Data (X : Nat) = struct
  type _ len += Len : X.t len

  let wrapped () = Wrap Len

  let uniq : type l1 l2. l1 len -> l2 len -> (l1, l2) Eq.t =
   fun l1 l2 ->
    match (l1, l2) with
    | Len, Len -> Eq
    | _ -> raise (Failure "arity can only be set once")

  let len : type l. l len -> l N.t = function
    | Len -> X.len
    | _ -> raise (Failure "arity can only be set once")
end

let data : (module Data_sig) ref = ref (module Data_unset : Data_sig)

let set_len x =
  let module X = (val module_of_int x : Nat) in
  data := (module Data (X) : Data_sig)

let wrapped () =
  let module M = (val !data : Data_sig) in
  M.wrapped ()

let uniq l1 l2 =
  let module M = (val !data : Data_sig) in
  M.uniq l1 l2

let len l =
  let module M = (val !data : Data_sig) in
  M.len l

let indices : type l. l len -> (l t, l) Bwv.t =
 fun l -> Bwv.map (fun i -> (l, i)) (Bwv.all_indices (len l))

let to_string : type l. l t option -> string =
 fun i ->
  let (Wrap l) = wrapped () in
  match i with
  | Some i -> string_of_int (N.to_int (len l) - N.int_of_index (snd i) - 1)
  | None -> string_of_int (N.to_int (len l))

let of_char : type l. l len -> char -> (l t option, unit) result =
 fun l c ->
  try
    let i = N.to_int (len l) - (int_of_char c - int_of_char '0') in
    if i = 0 then Ok None else Ok (Some (l, N.index_of_int (len l) (i - 1)))
  with Failure _ -> Error ()

let refl_char_data : char ref = ref 'e'
let refl_string_data : string ref = ref "e"
let refl_names_data : string list ref = ref [ "refl"; "Id" ]

let set_char c =
  refl_char_data := c;
  refl_string_data := String.make 1 c

let set_names strs = refl_names_data := strs
let refl_string () = !refl_string_data
let refl_names () = !refl_names_data

(*  *)
let internal_data : (unit -> bool) ref = ref (fun () -> raise (Failure "internality unset"))
let internal () = !internal_data ()
let set_internal i = internal_data := fun () -> i
