open Bwd
open Core
open Reporter
open PPrint
open Notation

let must_start_with tok obs =
  match obs with
  | Token (tok', _) :: _ when tok = tok' -> obs
  | _ -> Token (tok, []) :: obs

(* Print a variable, with underscore for unnamed variables. *)
let pp_var : string option -> document = function
  | Some x -> utf8string x
  | None -> Token.pp Underscore

(* Print constructors and fields *)
let pp_constr (c : string) : document = utf8string c ^^ char '.'

let pp_field (c : string) (p : string list) : document =
  char '.'
  ^^ utf8string c
  ^^
  if List.is_empty p then empty
  else if List.fold_right (fun s m -> max (String.length s) m) p 0 > 1 then
    char '.' ^^ concat_map (fun p -> char '.' ^^ utf8string p) p
  else char '.' ^^ concat_map utf8string p

let pp_space (space : space) : document =
  match space with
  | `None -> empty
  | `Cut -> break 0
  | `Break -> break 1
  | `Nobreak -> blank 1

(* Like PPrint.lines, but also excludes the indentation after each newline from the substrings. *)
let unindented_lines str =
  let rec go start =
    if start >= String.length str then [ empty ]
    else
      let pos = ref start in
      while !pos < String.length str && str.[!pos] <> '\n' do
        pos := !pos + 1
      done;
      let len = !pos - start in
      if !pos >= String.length str then [ substring str start len ]
      else (
        pos := !pos + 1;
        while !pos < String.length str && (str.[!pos] = ' ' || str.[!pos] = '\t') do
          pos := !pos + 1
        done;
        substring str start len :: go !pos) in
  go 0

(* Print the comments and newlines following a token, except if there is exactly one newline in which case do not print it.  (Single newlines entered by the user are not respected, but are reformatted.)  If this would not resulting in printing anything, instead print the supplied space.  Moreover, if there *is* whitespace printed and the supplied space would allow a linebreak, ensure that what is printed also at least allows a linebreak. *)
let pp_ws (space : space) (ws : Whitespace.t list) : document =
  let rec pp (ws : Whitespace.t list) (any_hardlines : bool) : document =
    match ws with
    | [] -> empty
    | [ `Newlines n ] -> repeat n hardline
    | [ `Line str ] -> char '`' ^^ utf8string str ^^ hardline
    | [ `Block str ] ->
        let ls = unindented_lines str in
        let ending =
          match space with
          | (`Cut | `Break) when not any_hardlines -> break 1
          | _ -> blank 1 in
        string "{`" ^^ separate hardline ls ^^ string "`}" ^^ ending
    | `Newlines n :: ws -> repeat n hardline ^^ pp ws true
    | `Line str :: ws -> char '`' ^^ utf8string str ^^ hardline ^^ pp ws true
    | `Block str :: ws ->
        let ls = unindented_lines str in
        string "{`"
        ^^ separate hardline ls
        ^^ string "`}"
        ^^ blank 1
        ^^ pp ws (any_hardlines || List.length ls > 1) in
  match ws with
  | [] -> pp_space space
  | [ `Newlines n ] when n < 2 -> pp_space space
  | `Newlines n :: ws -> repeat n hardline ^^ pp ws true
  | _ -> blank 1 ^^ pp ws false

(* We print an application spine, possibly containing field/method calls, with possible linebreaks as
     f a b c
       .meth1 d e f
         g h
       .meth2 i j
         k l m
   Accordingly, this function returns a list of lists, broken at field applications.  For the above example it would return
   [ [f; a; b; c]; [.meth1; d; e; f; g; h]; [.meth2; i; j; k; l; m] ]. *)
let get_spine :
    type lt ls rt rs. (lt, ls, rt, rs) parse Asai.Range.located -> wrapped_parse list list =
 fun tm ->
  let rec go :
      type lt ls rt rs.
      (lt, ls, rt, rs) parse Asai.Range.located ->
      wrapped_parse list ->
      wrapped_parse list list ->
      wrapped_parse list list =
   fun tm nonfields spines ->
    match tm.value with
    | App { fn; arg = { value = Field _; _ } as arg; _ } ->
        go fn [] ((Wrap arg :: nonfields) :: spines)
    | App { fn; arg; _ } -> go fn (Wrap arg :: nonfields) spines
    | _ -> (Wrap tm :: nonfields) :: spines in
  go tm [] []

(* Print a parse tree as a term.  Return the whitespace at the end instead of printing it, so the caller can exclude it from any surrounding groups and decide whether to add an additional break. *)
let rec pp_term :
    type lt ls rt rs. (lt, ls, rt, rs) parse Asai.Range.located -> document * Whitespace.t list =
 fun tm ->
  match tm.value with
  | Notn (n, d) -> (
      (* If a notation can be printed as a term, do that. *)
      match print_term n with
      | Some printer -> printer (args d)
      | None ->
          (* If a notation can only be printed as a case tree, we have to start a new "potential as kinetic" case tree that is aligned to the current column and grouped.  We do that here because while in case state, case trees do not align; indentations increase only a bit at a time from the left margin per nesting, and in general the whole case tree has breaks or not at all (with possible exceptions).  Moreover, the intendation increase is set outside each case-tree notation, i.e. each notation sets the increased indentation for its children. *)
          let intro, triv, doc, ws = (print_case n <|> Anomaly "missing print_case") (args d) in
          (align (intro ^^ triv_act triv doc), ws))
  | App _ ->
      (* Narrow spacing removes the default spaces before function arguments, but not before field projections. *)
      let sep =
        match Display.spacing () with
        | `Wide -> `Break
        | `Narrow -> `None in
      (* We allow the entire spine to appear on one line, but if it doesn't fit, we insist on breaking it before *every* method call, by concatenating all the method calls rather than 'flow'ing them, in a single group.  We separate them by the last whitespace in each line, returning the whitespace that ends the final one. *)
      let doc, ws =
        List.fold_left
          (fun (outer, prews) xs ->
            let line, postws =
              (* In each sublist of get_spine (that is, each method call), we combine the arguments as in PPrint.flow, except with the "separators" being the variable whitespace (or 'sep' space). *)
              List.fold_left
                (fun (inner, prews) (Wrap x) ->
                  let px, wx = pp_term x in
                  (inner ^^ group (optional (pp_ws sep) prews ^^ px), Some wx))
                (empty, None) xs in
            (outer ^^ optional (pp_ws `Break) prews ^^ hang 2 (group line), postws))
          (empty, None) (get_spine tm) in
      (group doc, ws <|> Anomaly "missing ws in pp_term")
  | Placeholder w -> (Token.pp Underscore, w)
  | Ident (x, w) -> (separate_map (char '.') utf8string x, w)
  | Constr (c, w) -> (pp_constr c, w)
  | Field (f, p, w) -> (pp_field f p, w)
  | Superscript (Some x, s, w) ->
      let px, wx = pp_term x in
      (px ^^ pp_ws `None wx ^^ pp_superscript s, w)
  | Superscript (None, s, w) -> (pp_superscript s, w)
  | Hole { num; ws; _ } ->
      ( utf8string
          (match Display.holes () with
          | `With_number -> "¿" ^ string_of_int !num ^ "?"
          | `Without_number -> "?"),
        ws )

and pp_superscript str =
  match Display.chars () with
  | `Unicode ->
      utf8string (Token.super_lparen_string ^ Token.to_super str ^ Token.super_rparen_string)
  | `ASCII -> utf8string ("^(" ^ str ^ ")")

(* Print a parse tree as a case tree.  Return the "intro" separately so that it can be grouped with any introductory code from a "def" or "let" so that the primary linebreaks are the case tree ones.  Deals with whitespace like pp_term; the whitespace that ends the intro goes into the main doc (including an allowed break).  The intro doesn't need to start with a break. *)
let pp_case :
    type lt ls rt rs.
    (lt, ls, rt, rs) parse Asai.Range.located ->
    PPrint.document * triviality * document * Whitespace.t list =
 fun tm ->
  match tm.value with
  | Notn (n, d) -> (
      (* If a notation can be printed as a case tree, do that. *)
      match print_case n with
      | Some printer -> printer (args d)
      | None ->
          (* If a notation can only be printed as a term, do that instead, and there is no intro.  An additional "group" shouldn't be necessary here, the term printer should put groups around its result. *)
          let doc, ws = (print_term n <|> Anomaly ("missing print_term for " ^ name n)) (args d) in
          (* TODO *)
          (empty, Nontrivial (fun x -> x), hang 2 doc, ws))
  | _ ->
      let doc, ws = pp_term tm in
      (empty, Nontrivial (fun x -> x), hang 2 doc, ws)

let pp_complete_term : wrapped_parse -> space -> document =
 fun (Wrap tm) space ->
  let doc, ws = pp_term tm in
  doc ^^ pp_ws space ws

let rec pp_ctx
    (ctx :
      (string * [ `Original | `Renamed | `Locked ] * wrapped_parse option * wrapped_parse) Bwd.t) :
    document =
  match ctx with
  | Emp -> empty
  | Snoc (ctx, (x, r, tm, Wrap ty)) ->
      let ptm, wtm =
        match tm with
        | Some (Wrap tm) ->
            let doc, ws = pp_term tm in
            (Token.pp Coloneq ^^ blank 1 ^^ group (hang 2 doc), pp_ws `Break ws)
        | None -> (empty, empty) in
      let pty, wty = pp_term ty in
      pp_ctx ctx
      ^^ hardline
      ^^ pp_var (Some x)
      ^^ blank 1
      ^^ ptm
      ^^ group
           (nest 2
              (wtm
              ^^ Token.pp Colon
              ^^ blank 1
              ^^ align
                   (match r with
                   | `Original -> group (pty ^^ pp_ws `None wty)
                   | `Renamed -> group (pty ^^ pp_ws `Break wty ^^ string "(not in scope)")
                   | `Locked -> group (pty ^^ pp_ws `Break wty ^^ string "(blocked by modal lock)"))
              ))

let pp_hole ctx ty =
  pp_ctx ctx ^^ hardline ^^ repeat 70 (char '-') ^^ hardline ^^ pp_complete_term ty `None
