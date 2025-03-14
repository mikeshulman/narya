open PPrint
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

let pp_path = function
  | [] -> Token.pp Dot
  | path -> separate_map (char '.') utf8string path

let rec pp_modifier : modifier -> document * Whitespace.t list = function
  | All { wsall } -> (string "all", wsall)
  | Id { wsid } -> (string "id", wsid)
  | Only { wsonly; path; wspath } -> (string "only" ^^ pp_ws `Nobreak wsonly ^^ pp_path path, wspath)
  | In { wsin; path; wspath; op } ->
      let pop, wop = pp_modifier op in
      (string "in" ^^ pp_ws `Nobreak wsin ^^ pp_path path ^^ pp_ws `Nobreak wspath ^^ pop, wop)
  | MNone { wsnone } -> (string "none", wsnone)
  | Except { wsexcept; path; wspath } ->
      (string "except" ^^ pp_ws `Nobreak wsexcept ^^ pp_path path, wspath)
  | Renaming { wsrenaming; source; wssource; target; wstarget } ->
      ( string "renaming"
        ^^ pp_ws `Nobreak wsrenaming
        ^^ pp_path source
        ^^ pp_ws `Nobreak wssource
        ^^ pp_path target,
        wstarget )
  | Seq { wsseq; wslparen; ops; wsrparen } -> pp_modifier_list "seq" wsseq wslparen ops wsrparen
  | Union { wsunion; wslparen; ops; wsrparen } ->
      pp_modifier_list "union" wsunion wslparen ops wsrparen

and pp_modifier_list op wsop wslparen ops wsrparen =
  let pops, wops =
    List.fold_left
      (fun (accum, prews) (op, ws) ->
        let pop, wop = pp_modifier op in
        ( accum ^^ optional (fun ws -> char ',' ^^ pp_ws `Break ws) prews ^^ pop ^^ pp_ws `None wop,
          Some ws ))
      (empty, None) ops in
  ( string op
    ^^ pp_ws `Nobreak wsop
    ^^ string "("
    ^^ pp_ws `None wslparen
    ^^ align (group pops)
    ^^ optional (pp_ws `None) wops
    ^^ string ")",
    wsrparen )
