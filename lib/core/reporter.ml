open Dim
open Hctx
open Asai.Diagnostic
open Format
open Uuseg_string

(* In order to display terms and suchlike in Asai messages, we utilize a double indirection.  Firstly, displaying a term requires "unparsing" it to a parse tree and then printing the parse tree, but parse trees and unparsing aren't defined until the Parser library, which is loaded after Core.  (Displaying a value additionally requires reading it back into a term, which is defined later in Core.)  For this reason, we introduce a wrapper type "printable" that can contain a term, value, etc.  Since terms and values haven't been defined yet in this file, we make "printable" an extensible variant, so they can be added later (in the module Printable) after they are defined.  (They also have to be bundled with their context.) *)

type printable = ..
type printable += PConstant of Constant.t

(* The function that actually does the work of printing a "printable" will be defined in Parser.Unparse.  But we need to be able to "call" that function in this file to define "default_text" that converts structured messages to text.  Thus, in this file we define a mutable global variable to contain that function, starting with a dummy function, and call its value to print "printable"s; then in Parser.Unparse we will set the value of that variable after defining the function it should contain. *)

(* Secondly, in Asai messages are emitted by performing an effect or raising an exception that carries with it the data of a function of type "formatter -> unit", which is then called by the handler Reporter.run to format the message text as part of a larger display formatting.  This causes problems if we define our printing functions naively, since it means that any effects performed by the formatting function (such as looking up names in a Yuujinchou Scope) will take place in the context of the handler, not that where the message was invoked, and hence in the wrong scope.  To deal with this, we introduce another wrapper "printed" that stores an existential type, a value of that type, and a function that can format a value of that type. *)

type printed = Printed : (formatter -> 'a -> unit) * 'a -> printed

(* Obviously the only thing that can be done with a value of type "printed" is to apply the function to the argument and a formatter.  But the virtue of wrapping it up this way is that the argument is evaluated when the "printed" value is computed, not when the function is called, and hence takes place in the correct scope.  The function to be defined in Parser.Unparse will thus have type "printable -> printed", and here is where we store it. *)

let printer : (printable -> printed) ref =
  ref (fun _ -> raise (Failure "print not set (hint: Parser.Unparse must be loaded)"))

(* Finally, here are some convenience functions. *)

let pp_printed ppf (Printed (pp, x)) = pp ppf x
let print pr = !printer pr

module Code = struct
  type t =
    | Parse_error : t
    | Encoding_error : t
    | Parsing_ambiguity : string -> t
    | No_relative_precedence : string * string -> t
    | Invalid_variable : string list -> t
    | Invalid_numeral : string -> t
    | Invalid_constr : string -> t
    | Invalid_field : string -> t
    | Invalid_degeneracy : string -> t
    | Not_enough_lambdas : int -> t
    | Not_enough_arguments_to_function : t
    | Not_enough_arguments_to_instantiation : t
    | Type_not_fully_instantiated : string -> t
    | Instantiating_zero_dimensional_type : printable -> t
    | Unequal_synthesized_type : printable * printable -> t
    | Checking_tuple_at_degenerated_record : printable -> t
    | Missing_field_in_tuple : Field.t -> t
    | Missing_method_in_comatch : Field.t -> t
    | Extra_field_in_tuple : Field.t option -> t
    | Extra_method_in_comatch : Field.t -> t
    | Invalid_field_in_tuple : t
    | Duplicate_field_in_tuple : Field.t -> t
    | Invalid_method_in_comatch : t
    | Duplicate_method_in_comatch : Field.t -> t
    | Missing_constructor_in_match : Constr.t -> t
    | Unnamed_variable_in_match : t
    | Checking_lambda_at_nonfunction : printable -> t
    | Checking_tuple_at_nonrecord : printable -> t
    | Comatching_at_noncodata : printable -> t
    | Comatching_at_degenerated_codata : printable -> t
    | No_such_constructor :
        [ `Data of printable | `Nondata of printable | `Other of printable ] * Constr.t
        -> t
    | Wrong_number_of_arguments_to_constructor : Constr.t * int -> t
    | No_such_field :
        [ `Record of printable | `Nonrecord of printable | `Other ] * Field.or_index
        -> t
    | Missing_instantiation_constructor :
        Constr.t * [ `Constr of Constr.t | `Nonconstr of printable ]
        -> t
    | Unequal_indices : printable * printable -> t
    | Unbound_variable : string -> t
    | Undefined_constant : printable -> t
    | Nonsynthesizing : string -> t
    | Low_dimensional_argument_of_degeneracy : (string * 'a D.t) -> t
    | Missing_argument_of_degeneracy : string -> t
    | Applying_nonfunction_nontype : printable * printable -> t
    | Unimplemented : string -> t
    | Matching_datatype_has_degeneracy : printable -> t
    | Invalid_match_index : printable -> t
    | Wrong_number_of_arguments_to_pattern : Constr.t * int -> t
    | No_such_constructor_in_match : printable * Constr.t -> t
    | Duplicate_constructor_in_match : Constr.t -> t
    | Index_variable_in_index_value : t
    | Matching_on_nondatatype : printable -> t
    | Matching_on_let_bound_variable : printable -> t
    | Dimension_mismatch : string * 'a D.t * 'b D.t -> t
    | Invalid_variable_face : 'a D.t * ('n, 'm) sface -> t
    | Unsupported_numeral : Q.t -> t
    | Anomaly : string -> t
    | No_such_level : printable * level -> t
    | Constant_already_defined : string -> t
    | Invalid_constant_name : string -> t
    | Too_many_commands : t
    | Invalid_tightness : string -> t
    | Invalid_fixity : t
    | Invalid_notation_part : string -> t
    | Invalid_notation_head : string -> t
    | Invalid_notation_pattern : string -> t
    | Constant_assumed : printable -> t
    | Constant_defined : printable -> t
    | Notation_defined : string -> t
    | Show : string * printable -> t
    | Comment_end_in_string : t

  (** The default severity of messages with a particular message code. *)
  let default_severity : t -> Asai.Diagnostic.severity = function
    | Parse_error -> Error
    | Encoding_error -> Error
    | Parsing_ambiguity _ -> Error
    | No_relative_precedence _ -> Error
    | Invalid_variable _ -> Error
    | Invalid_numeral _ -> Error
    | Invalid_constr _ -> Error
    | Invalid_field _ -> Error
    | Invalid_degeneracy _ -> Error
    | Not_enough_lambdas _ -> Error
    | Type_not_fully_instantiated _ -> Error
    | Unequal_synthesized_type _ -> Error
    | Checking_tuple_at_degenerated_record _ -> Error
    | Missing_field_in_tuple _ -> Error
    | Missing_method_in_comatch _ -> Error
    | Extra_field_in_tuple _ -> Error
    | Extra_method_in_comatch _ -> Error
    | Invalid_field_in_tuple -> Error
    | Duplicate_field_in_tuple _ -> Error
    | Invalid_method_in_comatch -> Error
    | Duplicate_method_in_comatch _ -> Error
    | Missing_constructor_in_match _ -> Error
    | Unnamed_variable_in_match -> Error
    | Checking_lambda_at_nonfunction _ -> Error
    | Checking_tuple_at_nonrecord _ -> Error
    | Comatching_at_noncodata _ -> Error
    | Comatching_at_degenerated_codata _ -> Error
    | No_such_constructor _ -> Error
    | Missing_instantiation_constructor _ -> Error
    | Unequal_indices _ -> Error
    | Unbound_variable _ -> Error
    | Undefined_constant _ -> Bug
    | No_such_field _ -> Error
    | Nonsynthesizing _ -> Error
    | Low_dimensional_argument_of_degeneracy _ -> Error
    | Missing_argument_of_degeneracy _ -> Error
    | Not_enough_arguments_to_function -> Error
    | Instantiating_zero_dimensional_type _ -> Error
    | Invalid_variable_face _ -> Error
    | Not_enough_arguments_to_instantiation -> Error
    | Applying_nonfunction_nontype _ -> Error
    | Wrong_number_of_arguments_to_constructor _ -> Error
    | Unimplemented _ -> Error
    | Matching_datatype_has_degeneracy _ -> Error
    | Invalid_match_index _ -> Error
    | Wrong_number_of_arguments_to_pattern _ -> Error
    | No_such_constructor_in_match _ -> Error
    | Duplicate_constructor_in_match _ -> Error
    | Index_variable_in_index_value -> Error
    | Matching_on_nondatatype _ -> Error
    | Matching_on_let_bound_variable _ -> Error
    | Dimension_mismatch _ -> Bug (* Sometimes Error? *)
    | Unsupported_numeral _ -> Error
    | Anomaly _ -> Bug
    | No_such_level _ -> Bug
    | Constant_already_defined _ -> Warning
    | Invalid_constant_name _ -> Error
    | Too_many_commands -> Error
    | Invalid_tightness _ -> Error
    | Invalid_fixity -> Error
    | Invalid_notation_part _ -> Error
    | Invalid_notation_head _ -> Error
    | Invalid_notation_pattern _ -> Error
    | Constant_assumed _ -> Info
    | Constant_defined _ -> Info
    | Notation_defined _ -> Info
    | Show _ -> Info
    | Comment_end_in_string -> Warning

  (** A short, concise, ideally Google-able string representation for each message code. *)
  let short_code : t -> string = function
    (* Usually bugs *)
    | Anomaly _ -> "E0000"
    | No_such_level _ -> "E0001"
    (* Unimplemented future features *)
    | Unimplemented _ -> "E0100"
    | Unsupported_numeral _ -> "E0101"
    (* Parse errors *)
    | Parse_error -> "E0200"
    | Parsing_ambiguity _ -> "E0201"
    | Invalid_variable _ -> "E0202"
    | Invalid_field _ -> "E0203"
    | Invalid_constr _ -> "E0204"
    | Invalid_numeral _ -> "E0205"
    | Invalid_degeneracy _ -> "E0206"
    | No_relative_precedence _ -> "E0207"
    | Comment_end_in_string -> "E0250"
    | Encoding_error -> "E0299"
    (* Scope errors *)
    | Unbound_variable _ -> "E0300"
    | Undefined_constant _ -> "E0301"
    (* Bidirectional typechecking *)
    | Nonsynthesizing _ -> "E0400"
    | Unequal_synthesized_type _ -> "E0401"
    (* Dimensions *)
    | Dimension_mismatch _ -> "E0500"
    | Not_enough_lambdas _ -> "E0501"
    | Not_enough_arguments_to_function -> "E0502"
    | Not_enough_arguments_to_instantiation -> "E0503"
    | Type_not_fully_instantiated _ -> "E0504"
    | Instantiating_zero_dimensional_type _ -> "E0505"
    | Invalid_variable_face _ -> "E0506"
    (* Degeneracies *)
    | Missing_argument_of_degeneracy _ -> "E0600"
    | Low_dimensional_argument_of_degeneracy _ -> "E0601"
    (* Function-types *)
    | Checking_lambda_at_nonfunction _ -> "E0700"
    | Applying_nonfunction_nontype _ -> "E0701"
    (* Record fields *)
    | No_such_field _ -> "E0800"
    (* Tuples *)
    | Checking_tuple_at_nonrecord _ -> "E0900"
    | Checking_tuple_at_degenerated_record _ -> "E0901"
    | Missing_field_in_tuple _ -> "E0902"
    | Extra_field_in_tuple _ -> "E0903"
    | Duplicate_field_in_tuple _ -> "E0904"
    | Invalid_field_in_tuple -> "E0905"
    (* Datatype constructors *)
    | No_such_constructor _ -> "E1000"
    | Wrong_number_of_arguments_to_constructor _ -> "E1001"
    | Missing_instantiation_constructor _ -> "E1002"
    | Unequal_indices _ -> "E1003"
    (* Matches *)
    (* - Match variable *)
    | Unnamed_variable_in_match -> "E1100"
    | Matching_on_let_bound_variable _ -> "E1101"
    (* - Match type *)
    | Matching_on_nondatatype _ -> "E1200"
    | Matching_datatype_has_degeneracy _ -> "E1201"
    | Invalid_match_index _ -> "E1202"
    (* - Match branches *)
    | Missing_constructor_in_match _ -> "E1300"
    | No_such_constructor_in_match _ -> "E1301"
    | Duplicate_constructor_in_match _ -> "E1302"
    | Wrong_number_of_arguments_to_pattern _ -> "E1303"
    | Index_variable_in_index_value -> "E1304"
    (* Comatches *)
    | Comatching_at_noncodata _ -> "E1400"
    | Comatching_at_degenerated_codata _ -> "E1401"
    | Missing_method_in_comatch _ -> "E1402"
    | Extra_method_in_comatch _ -> "E1403"
    | Duplicate_method_in_comatch _ -> "E1404"
    | Invalid_method_in_comatch -> "E1405"
    (* Commands *)
    | Constant_already_defined _ -> "E2000"
    | Invalid_constant_name _ -> "E2001"
    | Too_many_commands -> "E2002"
    | Invalid_fixity -> "E2003"
    | Invalid_tightness _ -> "E2004"
    | Invalid_notation_part _ -> "E2005"
    | Invalid_notation_head _ -> "E2006"
    | Invalid_notation_pattern _ -> "E2007"
    (* Information *)
    | Constant_defined _ -> "I0000"
    | Constant_assumed _ -> "I0001"
    | Notation_defined _ -> "I0002"
    (* Debugging *)
    | Show _ -> "I9999"

  let default_text : t -> text = function
    | Parse_error -> text "parse error"
    | Encoding_error -> text "UTF-8 encoding error"
    | Parsing_ambiguity str -> textf "potential parsing ambiguity: %s" str
    | Invalid_variable str -> textf "invalid local variable name: %s" (String.concat "." str)
    | Invalid_field str -> textf "invalid field name: %s" str
    | Invalid_constr str -> textf "invalid constructor name: %s" str
    | Invalid_numeral str -> textf "invalid numeral: %s" str
    | Invalid_degeneracy str ->
        if str = "" then text "missing degeneracy ('^' must not be followed by a space)"
        else textf "invalid degeneracy: %s" str
    | Invalid_variable_face (k, fa) ->
        textf "invalid face: %d-dimensional variable has no face %s" (to_int k) (string_of_sface fa)
    | No_relative_precedence (n1, n2) ->
        textf
          "notations \"%s\" and \"%s\" have no relative precedence or associativity; they can only be combined with parentheses"
          n1 n2
    | Not_enough_lambdas n ->
        textf "not enough non-cube variables for higher-dimensional abstraction: need %d more" n
    | Not_enough_arguments_to_function ->
        text "not enough arguments for a higher-dimensional function application"
    | Not_enough_arguments_to_instantiation ->
        text "not enough arguments to instantiate a higher-dimensional type"
    | Type_not_fully_instantiated str -> textf "type not fully instantiated in %s" str
    | Instantiating_zero_dimensional_type ty ->
        textf "@[<hv 0>can't apply/instantiate a zero-dimensional type@;<1 2>%a@]" pp_printed
          (print ty)
    | Unequal_synthesized_type (sty, cty) ->
        textf "@[<hv 0>term synthesized type@;<1 2>%a@ but is being checked against type@;<1 2>%a@]"
          pp_printed (print sty) pp_printed (print cty)
    | Checking_tuple_at_degenerated_record r ->
        textf "can't check a tuple against a record %a with a nonidentity degeneracy applied"
          pp_printed (print r)
    | Comatching_at_degenerated_codata r ->
        textf "can't comatch against a codatatype %a with a nonidentity degeneracy applied"
          pp_printed (print r)
    | Missing_field_in_tuple f -> textf "record field '%s' missing in tuple" (Field.to_string f)
    | Missing_method_in_comatch f ->
        textf "codata method '%s' missing in comatch" (Field.to_string f)
    | Extra_field_in_tuple f -> (
        match f with
        | Some f -> textf "field '%s' in tuple doesn't occur in record type" (Field.to_string f)
        | None -> text "too many un-labeled fields in tuple")
    | Extra_method_in_comatch f ->
        textf "method '%s' in comatch doesn't occur in codata type" (Field.to_string f)
    | Invalid_field_in_tuple -> text "invalid field in tuple"
    | Invalid_method_in_comatch -> text "invalid method in comatch"
    | Duplicate_field_in_tuple f ->
        textf "record field '%s' appears more than once in tuple" (Field.to_string f)
    | Duplicate_method_in_comatch f ->
        textf "method '%s' appears more than once in comatch" (Field.to_string f)
    | Missing_constructor_in_match c ->
        textf "missing match clause for constructor %s" (Constr.to_string c)
    | Unnamed_variable_in_match -> text "unnamed match variable"
    | Checking_lambda_at_nonfunction ty ->
        textf "@[<hv 0>checking abstraction against non-function type@;<1 2>%a@]" pp_printed
          (print ty)
    | Checking_tuple_at_nonrecord ty ->
        textf "@[<hv 0>checking tuple against non-record type@;<1 2>%a@]" pp_printed (print ty)
    | Comatching_at_noncodata ty ->
        textf "@[<hv 0>checking comatch against non-codata type@;<1 2>%a@]" pp_printed (print ty)
    | No_such_constructor (d, c) -> (
        match d with
        | `Data d ->
            textf "datatype %a has no constructor named %s" pp_printed (print d)
              (Constr.to_string c)
        | `Nondata d ->
            textf "non-datatype %a has no constructor named %s" pp_printed (print d)
              (Constr.to_string c)
        | `Other ty ->
            textf "@[<hv 0>non-datatype@;<1 2>%a@ has no constructor named %s@]" pp_printed
              (print ty) (Constr.to_string c))
    | Wrong_number_of_arguments_to_constructor (c, n) ->
        if n > 0 then textf "too many arguments to constructor %s (%d extra)" (Constr.to_string c) n
        else
          textf "not enough arguments to constructor %s (need %d more)" (Constr.to_string c) (abs n)
    | No_such_field (d, f) -> (
        match d with
        | `Record d ->
            textf "record type %a has no field named %s" pp_printed (print d)
              (Field.to_string_ori f)
        | `Nonrecord d ->
            textf "non-record type %a has no field named %s" pp_printed (print d)
              (Field.to_string_ori f)
        | `Other -> textf "term has no field named %s" (Field.to_string_ori f))
    | Missing_instantiation_constructor (exp, got) ->
        let pp_got =
          match got with
          | `Nonconstr tm -> print tm
          | `Constr c -> Printed (pp_print_string, Constr.to_string c) in
        fun ppf ->
          fprintf ppf
            "@[<hv 0>instantiation arguments of datatype must be matching constructors:@ expected@;<1 2>%s@ but got@;<1 2>"
            (Constr.to_string exp);
          pp_printed ppf pp_got;
          pp_close_box ppf ()
    | Unequal_indices (t1, t2) ->
        textf
          "@[<hv 0>index@;<1 2>%a@ of constructor application doesn't match the corresponding index@;<1 2>%a@ of datatype instance@]"
          pp_printed (print t1) pp_printed (print t2)
    | Unbound_variable c -> textf "unbound variable: %s" c
    | Undefined_constant c -> textf "undefined constant: %a" pp_printed (print c)
    | Nonsynthesizing pos -> textf "non-synthesizing term in synthesizing position (%s)" pos
    | Low_dimensional_argument_of_degeneracy (deg, dim) ->
        textf "argument of degeneracy '%s' must be at least %d-dimensional" deg (to_int dim)
    | Missing_argument_of_degeneracy deg -> textf "missing argument for degeneracy %s" deg
    | Applying_nonfunction_nontype (tm, ty) ->
        textf
          "@[<hv 0>attempt to apply/instantiate@;<1 2>%a@ of type@;<1 2>%a@ which is not a function-type or universe@]"
          pp_printed (print tm) pp_printed (print ty)
    | Unimplemented str -> textf "%s not yet implemented" str
    | Matching_datatype_has_degeneracy ty ->
        textf "@[<hv 0>can't match on element of datatype@;<1 2>%a@ that has a degeneracy applied@]"
          pp_printed (print ty)
    | Invalid_match_index tm ->
        textf
          "@[<hv 0>match variable has invalid or duplicate index@;<1 2>%a@ match indices must be distinct free variables without degeneracies@]"
          pp_printed (print tm)
    | Wrong_number_of_arguments_to_pattern (c, n) ->
        if n > 0 then
          textf "too many arguments to constructor %s in match pattern (%d extra)"
            (Constr.to_string c) n
        else
          textf "not enough arguments to constructor %s in match pattern (need %d more)"
            (Constr.to_string c) (abs n)
    | No_such_constructor_in_match (d, c) ->
        textf "datatype %a being matched against has no constructor %s" pp_printed (print d)
          (Constr.to_string c)
    | Duplicate_constructor_in_match c ->
        textf "constructor %s appears twice in match" (Constr.to_string c)
    | Index_variable_in_index_value -> text "free index variable occurs in inferred index value"
    | Matching_on_nondatatype ty ->
        textf "@[<hv 0>can't match on variable belonging to non-datatype@;<1 2>%a@]" pp_printed
          (print ty)
    | Matching_on_let_bound_variable name ->
        textf "can't match on let-bound variable %a" pp_printed (print name)
    | Dimension_mismatch (op, a, b) ->
        textf "dimension mismatch in %s (%d ≠ %d)" op (to_int a) (to_int b)
    | Unsupported_numeral n -> textf "unsupported numeral: %a" Q.pp_print n
    | Anomaly str -> textf "anomaly: %s" str
    | No_such_level (names, i) ->
        textf "@[<hov 2>no level variable@ (%d,%d)@ in context@ %a@]" (fst i) (snd i) pp_printed
          (print names)
    | Constant_already_defined name -> textf "redefining constant: %a" pp_utf_8 name
    | Invalid_constant_name name -> textf "invalid constant name: %a" pp_utf_8 name
    | Too_many_commands -> text "too many commands: enter one at a time"
    | Invalid_fixity -> text "declared fixity doesn't match notation pattern"
    | Invalid_tightness str -> textf "invalid tightness: %s" str
    | Invalid_notation_part str -> textf "invalid notation part: %s" str
    | Invalid_notation_head str -> textf "invalid notation head: %s" str
    | Invalid_notation_pattern str -> textf "invalid notation pattern: '%s'" str
    | Constant_assumed name -> textf "Axiom %a assumed" pp_printed (print name)
    | Constant_defined name -> textf "Constant %a defined" pp_printed (print name)
    | Notation_defined name -> textf "Notation %s defined" name
    | Show (str, x) -> textf "%s: %a" str pp_printed (print x)
    | Comment_end_in_string ->
        text "comment-end sequence `} in quoted string: cannot be commented out"
end

include Asai.StructuredReporter.Make (Code)
open Code

let struct_at_degenerated_type eta name =
  match eta with
  | `Eta -> Checking_tuple_at_degenerated_record name
  | `Noeta -> Comatching_at_degenerated_codata name

let missing_field_in_struct eta fld =
  match eta with
  | `Eta -> Missing_field_in_tuple fld
  | `Noeta -> Missing_method_in_comatch fld

let struct_at_nonrecord eta p =
  match eta with
  | `Eta -> Checking_tuple_at_nonrecord p
  | `Noeta -> Comatching_at_noncodata p

let duplicate_field eta fld =
  match eta with
  | `Eta -> Duplicate_field_in_tuple fld
  | `Noeta -> Duplicate_method_in_comatch fld
