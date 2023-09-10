open Bwd

type (_, _) t = [] : ('a, N.zero) t | ( :: ) : 'a * ('a, 'n) t -> ('a, 'n N.suc) t

let nil : type a. (a, N.zero) t = []
let cons : type a n. a -> (a, n) t -> (a, n N.suc) t = fun x xs -> x :: xs

let rec map : type a b n. (a -> b) -> (a, n) t -> (b, n) t =
 fun f xs ->
  match xs with
  | [] -> []
  | x :: xs -> f x :: map f xs

(* If a Bwd has exactly n elements, form a vector from them; otherwise raise an exception. *)
let of_bwd : type a n. n N.t -> a Bwd.t -> string -> (a, n) t =
 fun n xs err ->
  let rec of_bwd : type m n mn. m N.t -> (m, n, mn) N.plus -> a Bwd.t -> (a, n) t -> (a, mn) t =
   fun m mn xs acc ->
    match (m, xs) with
    | Nat Zero, Emp ->
        let Eq = N.plus_uniq mn (N.zero_plus (N.plus_right mn)) in
        acc
    | Nat (Suc m), Snoc (xs, x) -> of_bwd (Nat m) (N.suc_plus mn) xs (x :: acc)
    | _ -> raise (Failure ("Wrong number of arguments in " ^ err)) in
  of_bwd n Zero xs []
