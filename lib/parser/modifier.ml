open Format
open Uuseg_string
open Print
module Trie = Yuujinchou.Trie
module Language = Yuujinchou.Language

(* Our abstract syntax for modifiers *)
type modifier =
  | All of { wsall : Whitespace.t list }
  | Id of { wsid : Whitespace.t list }
  | Only of { wsonly : Whitespace.t list; path : Trie.path; wspath : Whitespace.t list }
  | In of { wsin : Whitespace.t list; path : Trie.path; wspath : Whitespace.t list; op : modifier }
  | MNone of { wsnone : Whitespace.t list }
  | Except of { wsexcept : Whitespace.t list; path : Trie.path; wspath : Whitespace.t list }
  | Renaming of {
      wsrenaming : Whitespace.t list;
      source : Trie.path;
      wssource : Whitespace.t list;
      target : Trie.path;
      wstarget : Whitespace.t list;
    }
  | Seq of {
      wsseq : Whitespace.t list;
      wslparen : Whitespace.t list;
      ops : (modifier * Whitespace.t list) list;
      wsrparen : Whitespace.t list;
    }
  | Union of {
      wsunion : Whitespace.t list;
      wslparen : Whitespace.t list;
      ops : (modifier * Whitespace.t list) list;
      wsrparen : Whitespace.t list;
    }

let rec process_modifier = function
  | All _ -> Language.all
  | Id _ -> Language.id
  | Only { path; _ } -> Language.only path
  | In { path; op; _ } -> Language.in_ path (process_modifier op)
  | MNone _ -> Language.none
  | Except { path; _ } -> Language.except path
  | Renaming { source; target; _ } -> Language.renaming source target
  | Seq { ops; _ } -> Language.seq (List.map (fun x -> process_modifier (fst x)) ops)
  | Union { ops; _ } -> Language.union (List.map (fun x -> process_modifier (fst x)) ops)

let pp_path ppf = function
  | [] -> pp_tok ppf Dot
  | path -> pp_utf_8 ppf (String.concat "." path)

let rec pp_modifier ppf = function
  | All { wsall } ->
      pp_print_string ppf "all";
      wsall
  | Id { wsid } ->
      pp_print_string ppf "id";
      wsid
  | Only { wsonly; path; wspath } ->
      pp_print_string ppf "only";
      pp_ws `Break ppf wsonly;
      pp_path ppf path;
      wspath
  | In { wsin; path; wspath; op } ->
      pp_print_string ppf "in";
      pp_ws `Break ppf wsin;
      pp_path ppf path;
      pp_ws `Break ppf wspath;
      pp_modifier ppf op
  | MNone { wsnone } ->
      pp_print_string ppf "none";
      wsnone
  | Except { wsexcept; path; wspath } ->
      pp_print_string ppf "except";
      pp_ws `Break ppf wsexcept;
      pp_path ppf path;
      wspath
  | Renaming { wsrenaming; source; wssource; target; wstarget } ->
      pp_print_string ppf "renaming";
      pp_ws `Break ppf wsrenaming;
      pp_path ppf source;
      pp_ws `Break ppf wssource;
      pp_path ppf target;
      wstarget
  | Seq { wsseq; wslparen; ops; wsrparen } ->
      pp_print_string ppf "seq";
      pp_ws `Nobreak ppf wsseq;
      pp_print_string ppf "(";
      pp_ws `Break ppf wslparen;
      List.iter
        (fun (op, ws) ->
          pp_ws `None ppf (pp_modifier ppf op);
          pp_print_string ppf ";";
          pp_ws `Break ppf ws)
        ops;
      pp_print_string ppf ")";
      wsrparen
  | Union { wsunion; wslparen; ops; wsrparen } ->
      pp_print_string ppf "union";
      pp_ws `Nobreak ppf wsunion;
      pp_print_string ppf "(";
      pp_ws `Break ppf wslparen;
      List.iter
        (fun (op, ws) ->
          pp_ws `None ppf (pp_modifier ppf op);
          pp_print_string ppf ";";
          pp_ws `Break ppf ws)
        ops;
      pp_print_string ppf ")";
      wsrparen
