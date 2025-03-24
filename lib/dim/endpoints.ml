open Util

(* We parametrize over an abstract module specifying how many endpoints our cubes have.  Internally it just counts them with a stored natural number *)

type 'l len = 'l N.t
type wrapped = Wrap : 'l len -> wrapped
type 'l t = 'l len * 'l N.index

module Data = struct
  type t = { arity : wrapped; refl_string : string; refl_names : string list; internal : bool }
end

module Config = Algaeff.Reader.Make (Data)

let () = Config.register_printer (function `Read -> Some "unhandled Endpoints.Config.read effect")

let run ~arity ~refl_char ~refl_names ~internal f =
  let (Plus_something arity) = N.plus_of_int arity in
  let refl_string = String.make 1 refl_char in
  let env : Data.t = { arity = Wrap (Nat arity); refl_string; refl_names; internal } in
  Config.run ~env f

let wrapped () = (Config.read ()).arity
let refl_string () = (Config.read ()).refl_string
let refl_names () = (Config.read ()).refl_names
let internal () = (Config.read ()).internal

let uniq : type l1 l2. l1 len -> l2 len -> (l1, l2) Eq.t =
 fun l1 l2 ->
  match N.compare l1 l2 with
  | Eq -> Eq
  | _ -> raise (Failure "unexpected arity")

let len l = l

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
    if i = 0 then Ok None
    else
      match N.index_of_int (len l) (i - 1) with
      | Some j -> Ok (Some (l, j))
      | None -> Error ()
  with Failure _ -> Error ()
