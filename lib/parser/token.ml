(* This module should not be opened, but used qualified. *)

type t = Tok of string | Indent of int

let compile str = Pcre.regexp ~flags:[ `UTF8 ] str

(* A token is either a single one of these characters: *)
let singletons = "(){}→↦≔"

(* Or a sequence of one or more of these characters: *)
let operators = "[\\]~!@#$%\\^&*/?=+\\\\|,<>:;\\-"

(* Or a sequence of non-whitespace characters other than these.  Note that this includes letters, digits, underscores, periods, and most non-ASCII unicode characters. *)

(* In addition:
   - line comments start at ` and extend to a newline (but don't include the newline)
   - block comments start at {` and extend to the first `} (non-nesting, but extensible to {`` ... ``} etc. that must match)
   - string literals start at " and extend to the next " not escaped with a backslash
   - comments cannot start inside a string literal
   - when a new line starts (outside a comment), we record the number of 0x20 spaces, for layout
*)

(* TODO: This doesn't enforce that code lines can't start with non-space whitespace. *)
let delims =
  Pcre.regexp ~flags:[ `UTF8; `MULTILINE ]
    (Printf.sprintf "\n( *)|`.*$|{(`+)(?s:.)*?\\2}|\"((?:[^\"]|\\\")*)\"|\\s+|([%s]|[%s]+)"
       singletons operators)

let ize (str : string) : t list =
  (* With grouping parentheses, Pcre.full_split seems to return, for every delimiter, a Delim containing the full value of that delimiter *followed* by either a Group or a NoGroup for *each* group in the regex.  So we can ignore the Delims and act accordingly on the Groups. *)
  let rec ize = function
    | [] -> []
    | Pcre.Text str :: rest -> Tok str :: ize rest
    | Delim _ :: Group (1, spaces) :: NoGroup :: NoGroup :: NoGroup :: rest ->
        Indent (String.length spaces) :: ize rest
    | Delim _ :: NoGroup :: NoGroup :: Group (3, _) :: NoGroup :: _ ->
        raise (Failure "String literals not yet implemented")
    (* For some reason, when the third group matches, the first two return a Group with an empty string rather than a NoGroup.  Fortunately, when the first two groups match they don't seem to do that with the third group, so we can unambiguously find which group actually matched. *)
    | Delim _ :: _ :: _ :: _ :: Group (4, op) :: rest -> Tok op :: ize rest
    | _ :: rest -> ize rest in
  ize (Pcre.full_split ~rex:delims str)

(*
The first set of (single-character) tokens have only built-in meaning.

The second set of tokens are available for use in user-defined notations, and some of them have built-in meanings as well.

The third set of tokens divides into:
1. Those which start or end with "_", which have built-in meaning (or are invalid).
2. Those which start with ".", which have the built-in meaning of field projections.
3. Those which end with ".", which have the built-in meaning of constructors.
4. Reserved keywords
5. All others, which are available for use in user-defined notations, and can also be identifiers (names of variables and constants).

Thus, an identifier is a sequence of non-singleton, non-operator characters that doesn't start or end with an underscore or period, and which is not a reserved keyword.
*)

let ident =
  compile
    (Printf.sprintf "^[^_.%s%s]|[^_.%s%s][^%s%s]*[^_.%s%s]$" singletons operators singletons
       operators singletons operators singletons operators)

let reserved = [ "Type"; "Id"; "refl"; "sym" ]
let is_ident str = Pcre.pmatch ~rex:ident str && not (List.mem str reserved)

(* Internal periods in an identifier denote namespace qualifiers (unimplemented so far), hence are disallowed in local variable names. *)

let vble_str =
  Printf.sprintf "[^_.%s%s]|[^_.%s%s][^.%s%s]*[^_.%s%s]" singletons operators singletons operators
    singletons operators singletons operators

let vble = compile ("^" ^ vble_str ^ "$")
let is_vble str = Pcre.pmatch ~rex:vble str && not (List.mem str reserved)

(* Similarly, a field name is an allowed variable name, and a field access is a dot followed by a field name. *)

let fieldname = vble
let is_fieldname str = Pcre.pmatch ~rex:fieldname str && not (List.mem str reserved)
let field = compile (Printf.sprintf "^\\.(%s)$" vble_str)

let is_field str =
  try Some (Pcre.get_substring (Pcre.exec ~rex:field str) 1) with Not_found -> None

(* And dually for constructors. *)

let constrname = vble
let is_constrname str = Pcre.pmatch ~rex:constrname str && not (List.mem str reserved)
let constr = compile (Printf.sprintf "^(%s)\\.$" vble_str)

let is_constr str =
  try Some (Pcre.get_substring (Pcre.exec ~rex:constr str) 1) with Not_found -> None

(* A valid notation part is a sequence of operator characters or an identifier. *)

let notnpart =
  compile
    (Printf.sprintf "^([%s]+|[^0-9_.%s%s][^%s%s]*)$" operators singletons operators singletons
       operators)

let is_notnpart str = Pcre.pmatch ~rex:notnpart str && not (List.mem str reserved)
