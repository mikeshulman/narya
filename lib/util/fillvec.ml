(* A type of length-indexed vectors, of predetermined intended length, that is filled progressively from left to right like a backwards vector, but then converted automatically to a forwards vector when full.  An ('a, 'n, 'mn) Fillvec.t means that 'm and 'mn are forwards natural numbers where 'mn is the intended length and 'n measures how many empty spaces are left to fill. *)

type (_, _, _) t =
  | Filled : ('a, 'n) Vec.t -> ('a, Fwn.zero, 'n) t
  | Unfilled :
      ('a, 'm) Bwv.t * 'n Fwn.t * ('m, 'n Fwn.suc, 'mn) Fwn.fplus
      -> ('a, 'n Fwn.suc, 'mn) t

let empty : type a n. n Fwn.t -> (a, n, n) t = function
  | Zero -> Filled []
  | Suc n -> Unfilled (Emp, n, Zero)

let snoc : type a n mn. (a, n Fwn.suc, mn) t -> a -> (a, n, mn) t =
 fun (Unfilled (xs, n, mn)) x ->
  match n with
  | Zero -> Filled (Bwv.prepend mn xs [ x ])
  | Suc n -> Unfilled (Snoc (xs, x), n, Suc mn)

let remaining : type a n mn. (a, n, mn) t -> n Fwn.t = function
  | Filled _ -> Zero
  | Unfilled (_, n, _) -> Suc n

let get : type a mn. (a, Fwn.zero, mn) t -> (a, mn) Vec.t = function
  | Filled xs -> xs

let map : type a b n mn. (a -> b) -> (a, n, mn) t -> (b, n, mn) t =
 fun f -> function
  | Filled xs -> Filled (Vec.mmap (fun [ x ] -> f x) [ xs ])
  | Unfilled (xs, n, mn) -> Unfilled (Bwv.mmap (fun [ x ] -> f x) [ xs ], n, mn)
