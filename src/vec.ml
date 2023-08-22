type (_, _) t = [] : ('a, N.zero) t | ( :: ) : 'a * ('a, 'n) t -> ('a, 'n N.suc) t

let rec map : type a b n. (a -> b) -> (a, n) t -> (b, n) t =
 fun f xs ->
  match xs with
  | [] -> []
  | x :: xs -> f x :: map f xs
