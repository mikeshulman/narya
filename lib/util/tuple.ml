open Signatures

(* A "tuple" is an intrinsically well-typed *total* map whose keys are insertions into some (backwards) nat, and whose values are parametrized by the result of removing that inserted element. *)

module Make (F : Fam2) : sig
  type ('a, 'p) t

  val empty : (N.zero, 'p) t
  val find : ('a, 'asuc) N.insert -> ('asuc, 'p) t -> ('a, 'p) F.t
  val set : ('a, 'asuc) N.insert -> ('a, 'p) F.t -> ('asuc, 'p) t -> ('asuc, 'p) t

  val update :
    ('a, 'asuc) N.insert -> (('a, 'p) F.t -> ('a, 'p) F.t) -> ('asuc, 'p) t -> ('asuc, 'p) t

  type ('asuc, 'p) builder = { build : 'a. ('a, 'asuc) N.insert -> ('a, 'p) F.t }

  val build : 'a N.t -> ('a, 'p) builder -> ('a, 'p) t

  type ('p, 'q) mapper = { map : 'a. ('a, 'p) F.t -> ('a, 'q) F.t }

  val map : ('p, 'q) mapper -> ('a, 'p) t -> ('a, 'q) t

  type ('asuc, 'p) iterator = { it : 'a. ('a, 'asuc) N.insert -> ('a, 'p) F.t -> unit }

  val iter : ('a, 'p) iterator -> ('a, 'p) t -> unit

  type ('asuc, 'p, 'acc) folder = {
    fold : 'a. ('a, 'asuc) N.insert -> ('a, 'p) F.t -> 'acc -> 'acc;
  }

  val fold : ('a, 'p, 'acc) folder -> ('a, 'p) t -> 'acc -> 'acc
end = struct
  type ('asuc, 'p) builder = { build : 'a. ('a, 'asuc) N.insert -> ('a, 'p) F.t }
  type ('p, 'q) mapper = { map : 'a. ('a, 'p) F.t -> ('a, 'q) F.t }
  type ('asuc, 'p) iterator = { it : 'a. ('a, 'asuc) N.insert -> ('a, 'p) F.t -> unit }

  type ('asuc, 'p, 'acc) folder = {
    fold : 'a. ('a, 'asuc) N.insert -> ('a, 'p) F.t -> 'acc -> 'acc;
  }

  (* The intermediate pieces of such a map are additionally parametrized by a forwards nat 'b that is to be added on the right to produce the true "outer" parameter. *)
  module Internal = struct
    type (_, _, _) t =
      | Emp : (N.zero, 'b, 'p) t
      | Map : {
          now : ('a, 'b, 'ab) Fwn.bplus * ('ab, 'p) F.t;
          later : ('a, 'b Fwn.suc, 'p) t;
        }
          -> ('a N.suc, 'b, 'p) t

    let empty : type b p. (N.zero, b, p) t = Emp

    let rec find :
        type a asuc b ab p.
        (a, asuc) N.insert -> (asuc, b, p) t -> (a, b, ab) Fwn.bplus -> (ab, p) F.t =
     fun i m ab ->
      match i with
      | Now ->
          let (Map { now = ab', v; _ }) = m in
          let Eq = Fwn.bplus_uniq ab ab' in
          v
      | Later i ->
          let (Map { later; _ }) = m in
          find i later (Suc ab)

    let rec set :
        type a asuc b ab p.
        (a, asuc) N.insert ->
        (ab, p) F.t ->
        (asuc, b, p) t ->
        (a, b, ab) Fwn.bplus ->
        (asuc, b, p) t =
     fun i v m ab ->
      match i with
      | Now ->
          let (Map { now = ab', _; later }) = m in
          let Eq = Fwn.bplus_uniq ab ab' in
          Map { now = (ab', v); later }
      | Later i ->
          let (Map { later; now }) = m in
          Map { later = set i v later (Suc ab); now }

    let rec update :
        type a asuc b ab p.
        (a, asuc) N.insert ->
        ((ab, p) F.t -> (ab, p) F.t) ->
        (asuc, b, p) t ->
        (a, b, ab) Fwn.bplus ->
        (asuc, b, p) t =
     fun i f m ab ->
      match i with
      | Now ->
          let (Map { now = ab', v; later }) = m in
          let Eq = Fwn.bplus_uniq ab ab' in
          Map { now = (ab', f v); later }
      | Later i ->
          let (Map { later; now }) = m in
          Map { later = update i f later (Suc ab); now }

    let rec build : type a b ab p. a N.t -> (a, b, ab) Fwn.bplus -> (ab, p) builder -> (a, b, p) t =
     fun a ab builder ->
      match a with
      | Nat Zero -> Emp
      | Nat (Suc a) ->
          let (Bplus ab') = Fwn.bplus (Fwn.bplus_right ab) in
          Map
            {
              now = (ab', builder.build (Fwn.insert_bplus Now ab' ab));
              later = build (Nat a) (Suc ab) builder;
            }

    let rec map : type a b p q. (p, q) mapper -> (a, b, p) t -> (a, b, q) t =
     fun f m ->
      match m with
      | Emp -> Emp
      | Map { now = ab, v; later } -> Map { now = (ab, f.map v); later = map f later }

    let rec iter : type a b ab p. (a, b, ab) Fwn.bplus -> (ab, p) iterator -> (a, b, p) t -> unit =
     fun ab f m ->
      match m with
      | Emp -> ()
      | Map { now = ab', v; later } ->
          f.it (Fwn.insert_bplus Now ab' ab) v;
          iter (Suc ab) f later

    let rec fold :
        type a b ab p acc. (a, b, ab) Fwn.bplus -> (ab, p, acc) folder -> (a, b, p) t -> acc -> acc
        =
     fun ab f m acc ->
      match m with
      | Emp -> acc
      | Map { now = ab', v; later } ->
          let acc = f.fold (Fwn.insert_bplus Now ab' ab) v acc in
          fold (Suc ab) f later acc
  end

  type ('a, 'p) t = ('a, Fwn.zero, 'p) Internal.t

  let empty : type p. (N.zero, p) t = Internal.empty

  let find : type a asuc p. (a, asuc) N.insert -> (asuc, p) t -> (a, p) F.t =
   fun i m -> Internal.find i m Zero

  let set : type a asuc p. (a, asuc) N.insert -> (a, p) F.t -> (asuc, p) t -> (asuc, p) t =
   fun i v m -> Internal.set i v m Zero

  let update :
      type a asuc p. (a, asuc) N.insert -> ((a, p) F.t -> (a, p) F.t) -> (asuc, p) t -> (asuc, p) t
      =
   fun i f m -> Internal.update i f m Zero

  let build : type a p. a N.t -> (a, p) builder -> (a, p) t =
   fun a builder -> Internal.build a Zero builder

  let map : type a p q. (p, q) mapper -> (a, p) t -> (a, q) t = fun f m -> Internal.map f m
  let iter : type a p. (a, p) iterator -> (a, p) t -> unit = fun f m -> Internal.iter Zero f m

  let fold : type a p acc. (a, p, acc) folder -> (a, p) t -> acc -> acc =
   fun f m acc -> Internal.fold Zero f m acc
end
