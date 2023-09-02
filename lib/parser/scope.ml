(* This module should not be imported, but used qualified. *)

(* ***************************
   Scopes (notation groups)
   *************************** *)

(* According to DN, the vertices of the precedence graph are finite sets of notations.  We call these sets "scopes", and allow the user to add notations to scopes separately from defining precedence relations between scopes. *)

module Scope = struct
  (* There are three special scopes called "Minimum", "Maximum", and "Premaximum" that are least, greatest, and next-to-greatest in the precedence graph.  The user cannot add notations to these; they are used only for builtins.  Specifically, Maximum is used for parentheses and argumentless symbols, Premaximum is used for function application and field projections, and Minimum is used for type ascription and lambda-abstractions.  *)
  type t = Minimum | Maximum | Premaximum | User of string

  let compare : t -> t -> int = compare
end

type t = Scope.t

let max = Scope.Maximum
let premax = Scope.Premaximum
let min = Scope.Minimum

(* We record the Set of all scopes. *)

module ScopeSet = Set.Make (Scope)

let scopes : ScopeSet.t ref = ref (ScopeSet.of_list [ min; premax; max ])
let exists name = ScopeSet.mem (Scope.User name) !scopes

(* We record the DAG of scope precedences as a Map associating to each scope the list of scopes of higher precedence.  (A list rather than a set, because the most common operation is to iterate over it.)  *)

module ScopeMap = Map.Make (Scope)

let get_list (key : Scope.t) (map : 'a list ScopeMap.t) : 'a list =
  Option.value (ScopeMap.find_opt key map) ~default:[]

let highers : Scope.t list ScopeMap.t ref =
  ref (ScopeMap.empty |> ScopeMap.add premax [ max ] |> ScopeMap.add min [ premax; max ])

(* To check to prevent directed cycles, we maintain the reflexive-transitive closure of the precedence relation, which is a Map associating to each scope the Set of all scopes reflexive-transitively higher than it.  (Now a set, because the relevant operation is to check for membership.) *)

let transitive_highers : ScopeSet.t ScopeMap.t ref =
  ref
    (ScopeMap.empty
    |> ScopeMap.add min (ScopeSet.of_list [ min; premax; max ])
    |> ScopeMap.add premax (ScopeSet.of_list [ premax; max ])
    |> ScopeMap.add max (ScopeSet.of_list [ max ]))

(* To add a new scope... *)
let make name =
  let scope = Scope.User name in
  (* If such a scope already exists, we just return it *)
  if exists name then scope
  else (
    (* Otherwise, we add it to the Set of all scopes *)
    scopes := ScopeSet.add scope !scopes;
    (* We ensure that it is lower than max and premax, and greater than min *)
    highers := !highers |> ScopeMap.add scope [ premax; max ] |> ScopeMap.add_to_list min scope;
    (* And ensure that the refl-trans closure remains consistent. *)
    transitive_highers :=
      !transitive_highers
      |> ScopeMap.add scope (ScopeSet.of_list [ scope; premax; max ])
      |> ScopeMap.add min !scopes;
    scope)

(* To add a new precedence relation... *)
let add_prec low high =
  (* If it would create a loop, meaning that the new "higher" scope is already refl-trans below the new "lower" scope, we do nothing and return None. *)
  if ScopeSet.mem low (ScopeMap.find high !transitive_highers) then None
  else (
    (* Otherwise, we add it to the precedence list. *)
    highers := ScopeMap.add_to_list low high !highers;
    (* And then we keep the refl-trans closure consistent, imposing that every scope refl-trans below the new "lower" one is also refl-trans below everything refl-trans below the new "higher" one. *)
    ScopeSet.iter
      (fun scope ->
        let hs = ScopeMap.find scope !transitive_highers in
        if ScopeSet.mem low hs then
          transitive_highers :=
            ScopeMap.add scope
              (ScopeSet.union (ScopeMap.find high !transitive_highers) (ScopeSet.add high hs))
              !transitive_highers
        else ())
      !scopes;
    Some ())

(* We also maintain a Set of currently "open" scopes, which are the only ones that are currently usable.  The min, max, and premax scopes are always open and can't be closed. *)
let open_scopes : ScopeSet.t ref = ref (ScopeSet.of_list [ min; premax; max ])
let get_opens () = ScopeSet.elements !open_scopes

(* Open or close a scope. *)
let open_scope scope = open_scopes := ScopeSet.add scope !open_scopes

let close_scope (scope : t) =
  match scope with
  | User _ -> Some (open_scopes := ScopeSet.remove scope !open_scopes)
  (* The special built-in scopes can't be closed. *)
  | _ -> None

(* When inspecting the scopes higher than a given one, we include only the open scopes. *)
let get_highers scope =
  List.filter
    (fun s -> ScopeSet.mem s !open_scopes)
    (Option.value (ScopeMap.find_opt scope !highers) ~default:[])

(* We expose the type of maps from scopes to lists.  This is used elsewhere to maintain the notations associated to each scope.  (This file can't do that because it doesn't know anything about notations, only scopes.) *)

type 'a map = 'a list ScopeMap.t

module Map = struct
  let make = ScopeMap.empty
  let add key elt map = ScopeMap.add_to_list key elt map
  let get key map = get_list key map

  type 'a t = 'a map
end

(* In addition to the special notation scopes, there's a built-in scope for function notation, which is not special (i.e. the user can and must declare precedences relating to it).  *)
let arrow = make "arrow"

(* It is open by default, but a sufficiently devilish user could close it. *)
let () = open_scope arrow
