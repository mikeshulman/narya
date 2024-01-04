open Bwd

type ('k, 'a) t = ('k * 'a) Bwd.t

let empty : ('k, 'a) t = Emp

let map (f : 'a -> 'b) (map : ('k, 'a) t) : ('k, 'b) t =
  Mbwd.mmap (fun [ (x, a) ] -> (x, f a)) [ map ]

let mapi (f : 'k -> 'a -> 'b) (map : ('k, 'a) t) : ('k, 'b) t =
  Mbwd.mmap (fun [ (x, a) ] -> (x, f x a)) [ map ]

let find_opt (x : 'k) (map : ('k, 'a) t) : 'a option =
  Option.map snd (Bwd.find_opt (fun (y, _) -> x = y) map)

let find (x : 'k) (map : ('k, 'a) t) : 'a = snd (Bwd.find (fun (y, _) -> x = y) map)
let add (x : 'k) (a : 'a) (map : ('k, 'a) t) = Snoc (map, (x, a))

let fold (f : 'k -> 'a -> 'acc -> 'acc) (map : ('k, 'a) t) (start : 'acc) =
  Bwd.fold_left (fun acc (x, a) -> f x a acc) start map

let bindings (map : ('k, 'a) t) = Bwd.to_list map

module Monadic (M : Monad.Plain) = struct
  open Mbwd.Monadic (M)
  open Monad.Ops (M)

  let mapiM (f : 'k -> 'a -> 'b M.t) (map : ('k, 'a) t) : ('k, 'b) t M.t =
    mmapM
      (fun [ (x, a) ] ->
        let* fxa = f x a in
        return (x, fxa))
      [ map ]
end
