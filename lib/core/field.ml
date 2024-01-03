open Bwd
open Util

module Field = struct
  type t = string

  let compare (x : t) (y : t) = compare x y
end

type t = Field.t

let intern (str : string) : t = str

(* Instead of using a Map we use an association Bwd, so that we can maintain the ordering of fields in a struct. *)
module Map = struct
  (* Map.Make (Field) *)
  type 'a t = (Field.t * 'a) Bwd.t

  let empty : 'a t = Emp
  let map (f : 'a -> 'b) (map : 'a t) : 'b t = Mbwd.mmap (fun [ (x, a) ] -> (x, f a)) [ map ]

  let mapi (f : Field.t -> 'a -> 'b) (map : 'a t) : 'b t =
    Mbwd.mmap (fun [ (x, a) ] -> (x, f x a)) [ map ]

  let find_opt (x : Field.t) (map : 'a t) : 'a option =
    Option.map snd (Bwd.find_opt (fun (y, _) -> x = y) map)

  let find (x : Field.t) (map : 'a t) : 'a = snd (Bwd.find (fun (y, _) -> x = y) map)
  let add (x : Field.t) (a : 'a) (map : 'a t) = Snoc (map, (x, a))

  let fold (f : Field.t -> 'a -> 'acc -> 'acc) (map : 'a t) (start : 'acc) =
    Bwd.fold_left (fun acc (x, a) -> f x a acc) start map

  let of_abwd (alist : (Field.t * 'a) Bwd.t) : 'a t = alist
  let bindings (map : 'a t) = Bwd.to_list map

  module Monadic (M : Monad.Plain) = struct
    open Mbwd.Monadic (M)
    open Monad.Ops (M)

    let mapiM (f : Field.t -> 'a -> 'b M.t) (map : 'a t) : 'b t M.t =
      mmapM
        (fun [ (x, a) ] ->
          let* fxa = f x a in
          return (x, fxa))
        [ map ]
  end
end

module Set = Set.Make (Field)

let to_string (x : t) : string = x
