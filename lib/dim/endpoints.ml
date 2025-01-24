open Util

(* We parametrize over an abstract module specifying how many endpoints our cubes have.  Internally it just counts them with a stored natural number *)

type 'l len = 'l N.t
type wrapped = Wrap : 'l len -> wrapped
type 'l t = 'l len * 'l N.index

let data : wrapped option ref = ref None

let set_len x =
  match !data with
  | Some _ -> raise (Failure "arity can only be set once")
  | None ->
      let (Plus_something x) = N.plus_of_int x in
      data := Some (Wrap (Nat x))

let wrapped () =
  match !data with
  | Some x -> x
  | None -> raise (Failure "arity unset")

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
  let i = N.to_int (len l) - (int_of_char c - int_of_char '0') in
  if i = 0 then Ok None
  else
    match N.index_of_int (len l) (i - 1) with
    | Some j -> Ok (Some (l, j))
    | None -> Error ()

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
