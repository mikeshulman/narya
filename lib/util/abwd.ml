(* Backwards association lists.  Use in place of Map when the order of entries also matters.  This module should not be opened, but used qualified. *)

open Bwd

type ('k, 'a) t = ('k * 'a) Bwd.t

let empty : ('k, 'a) t = Emp

let map (f : 'a -> 'b) (map : ('k, 'a) t) : ('k, 'b) t =
  Mbwd.mmap (fun [ (x, a) ] -> (x, f a)) [ map ]

let mapi (f : 'k -> 'a -> 'b) (map : ('k, 'a) t) : ('k, 'b) t =
  Mbwd.mmap (fun [ (x, a) ] -> (x, f x a)) [ map ]

let find_opt (x : 'k) (map : ('k, 'a) t) : 'a option =
  Option.map snd (Bwd.find_opt (fun (y, _) -> x = y) map)

let add (x : 'k) (a : 'a) (map : ('k, 'a) t) = Snoc (map, (x, a))

let fold (f : 'k -> 'a -> 'acc -> 'acc) (map : ('k, 'a) t) (start : 'acc) =
  Bwd.fold_left (fun acc (x, a) -> f x a acc) start map

let rec find_opt_and_update_key (oldkey : 'k) (newkey : 'k) (map : ('k, 'a) t) =
  match map with
  | Emp -> None
  | Snoc (map, (x, y)) -> (
      match find_opt_and_update_key oldkey newkey map with
      | Some (v, newmap) -> Some (v, Snoc (newmap, (x, y)))
      | None -> if x = oldkey then Some (y, Snoc (map, (newkey, y))) else None)

let bindings (map : ('k, 'a) t) = Bwd.to_list map
