type t = [ `Block of string | `Line of string | `Newlines of int ]

(* Ensure that blank lines never come in groups of more than one.  Also return OK if there is a block of at least DESIRED newlines. *)
let rec condense (desired : int) (seen : int) (ws : t list) : t list * bool =
  match ws with
  | [] -> ([], false)
  | `Line l :: ws ->
      let ws, ok = condense desired 1 ws in
      (`Line l :: ws, ok)
  | `Block b :: ws ->
      let ws, ok = condense desired 0 ws in
      (`Block b :: ws, ok)
  | `Newlines n :: `Newlines m :: ws -> condense desired seen (`Newlines (n + m) :: ws)
  | `Newlines n :: ws ->
      let ws, ok = condense desired (seen + n) ws in
      (`Newlines (min n (2 - seen)) :: ws, ok || seen + n >= desired)

(* Ensure that blank lines never come in groups of more than one, and that there is a block of at least DESIRED (which should be 0, 1 or 2) newlines (if not, add more newlines to the front after any comments).  Note that single newlines are not printed by pp_ws, so we need to also add a `Cut when printing when we expect those. *)
let normalize (desired : int) (ws : t list) : t list =
  let rec prepend (ws : t list) : t list =
    match ws with
    | [] -> [ `Newlines desired ]
    | `Block b :: ws -> `Block b :: prepend ws
    | [ `Line l ] -> [ `Line l; `Newlines (desired - 1) ]
    | `Line l :: `Newlines _ :: ws | `Line l :: ws -> `Line l :: `Newlines (desired - 1) :: ws
    | `Newlines _ :: ws -> `Newlines desired :: ws in
  let ws, ok = condense desired 0 ws in
  if ok then ws else prepend ws

(* Ensure that blank lines never come in groups of more than one, and that there are no blank lines at the beginning.  *)
let normalize_no_blanks (ws : t list) : t list =
  let rec no_blanks = function
    | `Newlines _ :: ws -> no_blanks ws
    | ws -> ws in
  let ws, _ = condense 0 0 ws in
  no_blanks ws

(* This used to be more nontrivial, but at the moment the trivial version seems to be what works. *)
let split (ws : t list) : t list * t list = ([], ws)
