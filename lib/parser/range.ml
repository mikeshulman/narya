open Fmlib_parse
open Asai.Range
open Core.Reporter

(* To convert Fmlib positions to Asai ranges, we need to know the string or file they're being run on.  We also store its length so that we can test for EOF. *)

module Data = struct
  type t = { source : source; length : int64 }
end

module S = Algaeff.Reader.Make (Data)

let convert_pos (src : source) pos =
  let start_of_line = Position.byte_offset_bol pos in
  (* It appears that fmlib lines are 0-indexed and Asai lines are 1-indexed *)
  let line_num = Position.line pos + 1 in
  let offset = Position.byte_offset pos in
  { source = src; offset; start_of_line; line_num }

let convert (pos1, pos2) =
  (* In case of a lexing or parsing error at end of input, Fmlib returns a 0-width range, which we convert into Asai's special "eof" position. *)
  let src = S.read () in
  if pos1 = pos2 then
    if Int64.of_int (Position.byte_offset pos2) = src.length then eof (convert_pos src.source pos1)
      (* Fmlib also reports a 0-width range in mid-parse if we fail directly (i.e. with "fail" or "unexpected" rather than during a lookahead such as "step").  But our calls to "fail" all include an explicit range, and we never call "unexpected".  Thus I don't think this should happen, so we flag it as an Anomaly.  *)
    else fatal (Anomaly "zero-width range during parse failure before EOF")
  else make (convert_pos src.source pos1, convert_pos src.source pos2)

let merge loc1 loc2 =
  match (view loc1, view loc2) with
  | `Range (p1, _), `Range (_, p2) -> make (p1, p2)
  | _, `End_of_file p -> eof p
  | `End_of_file p, _ -> eof p

let merge_opt loc1 loc2 =
  match (loc1, loc2) with
  | Some loc1, Some loc2 -> Some (merge loc1 loc2)
  | Some loc1, None -> Some loc1
  | None, Some loc2 -> Some loc2
  | None, None -> None

let merge_opt3 loc1 loc2 loc3 = merge_opt (merge_opt loc1 loc2) loc3
let run = S.run
let locate : type a. a -> Asai.Range.t option -> a located = fun value loc -> { value; loc }
