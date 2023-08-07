(* Don't import this module, use it qualified. *)

type ('a, 'b) t = { gen : 'a -> 'b; reduce : 'a -> 'a; memo : ('a, 'b) Hashtbl.t }

let create ?(reduce = fun x -> x) f = { gen = f; reduce; memo = Hashtbl.create 10 }

let get tbl x =
  let x = tbl.reduce x in
  match Hashtbl.find_opt tbl.memo x with
  | Some y -> y
  | None ->
      let y = tbl.gen x in
      Hashtbl.add tbl.memo x y;
      y
