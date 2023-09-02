(* This module should not be imported, but used qualified. *)

(* ***************************
   Nodes (notation groups)
   *************************** *)

(* According to DN, the vertices of the precedence graph are finite sets of notations.  We call these sets "nodes", and allow the user to add notations to nodes separately from defining precedence relations between nodes. *)

module Node = struct
  (* There are three special nodes called "Minimum", "Maximum", and "Premaximum" that are least, greatest, and next-to-greatest in the precedence graph.  The user cannot add notations to these; they are used only for builtins.  Specifically, Maximum is used for parentheses and argumentless symbols, Premaximum is used for function application and field projections, and Minimum is used for type ascription and lambda-abstractions.  *)
  type t = Minimum | Maximum | Premaximum | User of string

  let compare : t -> t -> int = compare
end

type t = Node.t

let max = Node.Maximum
let premax = Node.Premaximum
let min = Node.Minimum

(* We record the Set of all nodes. *)

module NodeSet = Set.Make (Node)

let nodes : NodeSet.t ref = ref (NodeSet.of_list [ min; premax; max ])
let exists name = NodeSet.mem (Node.User name) !nodes

(* We record the DAG of node precedences as a Map associating to each node the list of nodes of higher precedence.  (A list rather than a set, because the most common operation is to iterate over it.)  *)

module NodeMap = Map.Make (Node)

let get_list (key : Node.t) (map : 'a list NodeMap.t) : 'a list =
  Option.value (NodeMap.find_opt key map) ~default:[]

let highers : Node.t list NodeMap.t ref =
  ref (NodeMap.empty |> NodeMap.add premax [ max ] |> NodeMap.add min [ premax; max ])

(* To check to prevent directed cycles, we maintain the reflexive-transitive closure of the precedence relation, which is a Map associating to each node the Set of all nodes reflexive-transitively higher than it.  (Now a set, because the relevant operation is to check for membership.) *)

let transitive_highers : NodeSet.t NodeMap.t ref =
  ref
    (NodeMap.empty
    |> NodeMap.add min (NodeSet.of_list [ min; premax; max ])
    |> NodeMap.add premax (NodeSet.of_list [ premax; max ])
    |> NodeMap.add max (NodeSet.of_list [ max ]))

(* To add a new node... *)
let make name =
  let node = Node.User name in
  (* If such a node already exists, we just return it *)
  if exists name then node
  else (
    (* Otherwise, we add it to the Set of all nodes *)
    nodes := NodeSet.add node !nodes;
    (* We ensure that it is lower than max and premax, and greater than min *)
    highers := !highers |> NodeMap.add node [ premax; max ] |> NodeMap.add_to_list min node;
    (* And ensure that the refl-trans closure remains consistent. *)
    transitive_highers :=
      !transitive_highers
      |> NodeMap.add node (NodeSet.of_list [ node; premax; max ])
      |> NodeMap.add min !nodes;
    node)

(* To add a new precedence relation... *)
let add_prec low high =
  (* If it would create a loop, meaning that the new "higher" node is already refl-trans below the new "lower" node, we do nothing and return None. *)
  if NodeSet.mem low (NodeMap.find high !transitive_highers) then None
  else (
    (* Otherwise, we add it to the precedence list. *)
    highers := NodeMap.add_to_list low high !highers;
    (* And then we keep the refl-trans closure consistent, imposing that every node refl-trans below the new "lower" one is also refl-trans below everything refl-trans below the new "higher" one. *)
    NodeSet.iter
      (fun node ->
        let hs = NodeMap.find node !transitive_highers in
        if NodeSet.mem low hs then
          transitive_highers :=
            NodeMap.add node
              (NodeSet.union (NodeMap.find high !transitive_highers) (NodeSet.add high hs))
              !transitive_highers
        else ())
      !nodes;
    Some ())

(* We also maintain a Set of currently "open" nodes, which are the only ones that are currently usable.  The min, max, and premax nodes are always open and can't be closed. *)
let open_nodes : NodeSet.t ref = ref (NodeSet.of_list [ min; premax; max ])
let get_opens () = NodeSet.elements !open_nodes

(* Open or close a node. *)
let open_node node = open_nodes := NodeSet.add node !open_nodes

let close_node (node : t) =
  match node with
  | User _ -> Some (open_nodes := NodeSet.remove node !open_nodes)
  (* The special built-in nodes can't be closed. *)
  | _ -> None

(* When inspecting the nodes higher than a given one, we include only the open nodes. *)
let get_highers node =
  List.filter
    (fun s -> NodeSet.mem s !open_nodes)
    (Option.value (NodeMap.find_opt node !highers) ~default:[])

(* We expose the type of maps from nodes to lists.  This is used elsewhere to maintain the notations associated to each node.  (This file can't do that because it doesn't know anything about notations, only nodes.) *)

type 'a map = 'a list NodeMap.t

module Map = struct
  let make = NodeMap.empty
  let add key elt map = NodeMap.add_to_list key elt map
  let get key map = get_list key map

  type 'a t = 'a map
end

(* In addition to the special notation nodes, there's a built-in node for function notation, which is not special (i.e. the user can and must declare precedences relating to it).  *)
let arrow = make "arrow"

(* It is open by default, but a sufficiently devilish user could close it. *)
let () = open_node arrow
