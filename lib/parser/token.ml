type t =
  | Proj of string (* Starting with . *)
  | Constr of string (* Ending with . *)
  | Coercion of string (* Starting and ending with . *)
  | LParen (* ( *)
  | RParen (* ) *)
  | LBrace (* { *)
  | RBrace (* } *)
  | Arrow (* Both -> and → *)
  | Mapsto (* Both |-> and ↦ *)
  | Colon (* : *)
  | Coloneq (* Both := and ≔ *)
  | Dot (* . *)
  | String of string (* Double-quoted *)
  | Numeral of string (* Digits with internal dots *)
  | Underscore (* _ *)
  | Internal of string (* Starting or ending with _ *)
  | Match
  | Comatch
  | With
  | End
  | Record
  | Data
  | Section
  | Let
  | In
  | Op of string (* Sequence of common ASCII symbols *)
  (* Alphanumeric/unicode with only internal dots and underscores only.  We can't separate these out into those that are parts of mixfix notations and those that are potential identifiers, since the mixfix notations in scope change as we go through a file. *)
  | Name of string
  | Eof

let compare : t -> t -> int = compare
