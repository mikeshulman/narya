open Bwd
open Util
open Deg
open Insertion
open Shuffle

(* A partial bijection is an insertion together with a shuffle. *)

type (_, _) pbij =
  | Pbij :
      ('evaluation, 'result, 'shared) insertion * ('remaining, 'shared, 'intrinsic) shuffle
      -> ('evaluation, 'intrinsic) pbij

let dom_pbij : type e i. (e, i) pbij -> e D.t = fun (Pbij (ins, _)) -> dom_ins ins
let cod_pbij : type e i. (e, i) pbij -> i D.t = fun (Pbij (_, shuf)) -> out_shuffle shuf

let pbij_of_ins : type a b c. (a, b, c) insertion -> (a, c) pbij =
 fun ins -> Pbij (ins, zero_shuffle (cod_right_ins ins))

type _ pbij_of = Pbij_of : ('evaluation, 'intrinsic) pbij -> 'evaluation pbij_of

let rec pbij_of_int_strings :
    type e. e D.t -> [ `Int of int | `Str of string ] Bwd.t -> e pbij_of option =
 fun e strs ->
  match strs with
  | Emp -> Some (Pbij_of (Pbij (ins_zero e, Zero)))
  | Snoc (strs, `Int n) -> (
      try
        let ix = N.index_of_int e (N.to_int e - n) in
        match e with
        | Nat (Suc e) -> (
            let e = N.Nat e in
            let strs =
              Bwd.map
                (function
                  | `Int i ->
                      if i < n then `Int i
                      else if i > n then `Int (i - 1)
                      else raise (Invalid_argument "pbij_of_int_strings")
                  | `Str str -> `Str str)
                strs in
            match pbij_of_int_strings e strs with
            | Some (Pbij_of (Pbij (ins, shuf))) ->
                Some (Pbij_of (Pbij (Suc (ins, N.insert_of_index ix), Right shuf)))
            | None -> None)
        | Nat Zero -> (
            match ix with
            | _ -> .)
      with Invalid_argument _ -> None)
  | Snoc (strs, `Str str) when str = Endpoints.refl_string () -> (
      match pbij_of_int_strings e strs with
      | Some (Pbij_of (Pbij (ins, shuf))) -> Some (Pbij_of (Pbij (ins, Left shuf)))
      | None -> None)
  | Snoc (_, `Str _) -> None

let pbij_of_strings : type e. e D.t -> string Bwd.t -> e pbij_of option =
 fun e strs ->
  pbij_of_int_strings e
    (Bwd.map
       (fun x ->
         match int_of_string_opt x with
         | Some i -> `Int i
         | None -> `Str x)
       strs)

let rec int_strings_of_pbij : type n i. (n, i) pbij -> [ `Int of int | `Str of string ] Bwd.t =
 fun (Pbij (ins, shuf)) ->
  match shuf with
  | Zero -> Emp
  | Left shuf -> Snoc (int_strings_of_pbij (Pbij (ins, shuf)), `Str (Endpoints.refl_string ()))
  | Right shuf ->
      let (Suc (ins, ix)) = ins in
      let x = N.to_int (dom_ins ins) + 1 - N.int_of_index (N.index_of_insert ix) in
      Snoc
        ( Bwd.map
            (function
              | `Int i -> if i >= x then `Int (i + 1) else `Int i
              | `Str str -> `Str str)
            (int_strings_of_pbij (Pbij (ins, shuf))),
          `Int x )

let strings_of_pbij : type n i. (n, i) pbij -> string Bwd.t =
 fun pbij ->
  Bwd.map
    (function
      | `Str s -> s
      | `Int i -> string_of_int i)
    (int_strings_of_pbij pbij)

let string_of_pbij : type n i. (n, i) pbij -> string =
 fun pbij ->
  let strs = Bwd.to_list (strings_of_pbij pbij) in
  if List.fold_right (fun s m -> max (String.length s) m) strs 0 > 1 then
    ".." ^ String.concat "." strs
  else "." ^ String.concat "" strs

let all_pbij_between :
    type evaluation intrinsic. evaluation D.t -> intrinsic D.t -> (evaluation, intrinsic) pbij Seq.t
    =
 fun evaluation intrinsic ->
  let open Monad.Ops (Monad.Seq) in
  let* (Ins_of ins) = all_ins_of evaluation in
  let* (Of_right shuf) = all_shuffles_right (cod_right_ins ins) intrinsic in
  return (Pbij (ins, shuf))

type (_, _, _) deg_comp_pbij_internal =
  | DCP :
      ('evaluation, 'result, 'shared) insertion
      * ('remaining, 'shared, 'intrinsic) shuffle
      * ('old_result, 'result) deg
      -> ('evaluation, 'old_result, 'intrinsic) deg_comp_pbij_internal

let rec deg_comp_pbij_internal :
    type m n i res rem sh.
    (m, n) deg ->
    (m, res, sh) insertion ->
    (rem, sh, i) shuffle ->
    (n, res, i) deg_comp_pbij_internal =
 fun deg ins shuf ->
  match shuf with
  | Zero ->
      let (Zero _) = ins in
      DCP (ins_zero (cod_deg deg), Zero, deg)
  | Left shuf ->
      let (DCP (ins, shuf, s)) = deg_comp_pbij_internal deg ins shuf in
      DCP (ins, Left shuf, s)
  | Right shuf -> (
      let (Suc (ins, i)) = ins in
      match deg_coresidual deg i with
      | Coresidual_zero deg ->
          let (DCP (ins, shuf, s)) = deg_comp_pbij_internal deg ins shuf in
          DCP (ins, Left shuf, s)
      | Coresidual_suc (deg, j) ->
          let (DCP (ins, shuf, s)) = deg_comp_pbij_internal deg ins shuf in
          DCP (Suc (ins, j), Right shuf, s))

type (_, _) deg_comp_pbij =
  | Deg_comp_pbij :
      ('evaluation, 'intrinsic) pbij * ('old_result, 'result) deg
      -> ('evaluation, 'intrinsic) deg_comp_pbij

let deg_comp_pbij : type m n i. (m, n) deg -> (m, i) pbij -> (n, i) deg_comp_pbij =
 fun d (Pbij (ins, shuf)) ->
  let (DCP (ins, shuf, s)) = deg_comp_pbij_internal d ins shuf in
  Deg_comp_pbij (Pbij (ins, shuf), s)
