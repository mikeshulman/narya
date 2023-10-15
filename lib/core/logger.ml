open Dim
open Scope
open Asai.Diagnostic

module Code = struct
  type t =
    | Parse_error : string -> t
    | Not_enough_lambdas : int -> t
    | Not_enough_arguments_to_function : t
    | Not_enough_arguments_to_instantiation : t
    | Type_not_fully_instantiated : string -> t
    | Instantiating_zero_dimensional_type : t
    | Unequal_synthesized_type : t
    | Checking_struct_at_degenerated_record : Constant.t -> t
    | Missing_field_in_struct : Field.t -> t
    | Unnamed_field_in_struct : t
    | Duplicate_field_in_struct : Field.t -> t
    | Missing_constructor_in_match : Constr.t -> t
    | Unnamed_variable_in_match : t
    | Checking_struct_against_nonrecord : Constant.t -> t
    | Checking_constructor_against_nondatatype : (Constr.t * Constant.t) -> t
    | No_such_constructor : (Constant.t * Constr.t) -> t
    | Wrong_number_of_arguments_to_constructor : (Constr.t * int) -> t
    | No_such_field : (Constant.t option * Field.t) -> t
    | Missing_instantiation_constructor : (Constr.t * Constr.t option) -> t
    | Unequal_indices : t
    | Checking_mismatch : t
    | Unbound_variable : string -> t
    | Undefined_constant : Constant.t -> t
    | Nonsynthesizing : string -> t
    | Low_dimensional_argument_of_degeneracy : (string * int) -> t
    | Missing_argument_of_degeneracy : t
    | Applying_nonfunction_nontype : t
    | Higher_dimensional_match_not_implemented : t
    | Matching_datatype_has_degeneracy : t
    | Index_variables_duplicated : t
    | Non_variable_index_in_match : t
    | Degenerated_variable_index_in_match : t
    | Wrong_number_of_arguments_to_pattern : (Constr.t * int) -> t
    | No_such_constructor_in_match : (Constant.t * Constr.t) -> t
    | Duplicate_constructor_in_match : Constr.t -> t
    | Index_variable_in_index_value : t
    | Matching_on_nondatatype : Constant.t option -> t
    | Matching_on_let_bound_variable : t
    | Dimension_mismatch : (string * 'a D.t * 'b D.t) -> t
    | Unsupported_numeral : float -> t
    | Anomaly : string -> t

  (** The default severity of messages with a particular message code. *)
  let default_severity : t -> Asai.Diagnostic.severity = function
    | Parse_error _ -> Error
    | Not_enough_lambdas _ -> Error
    | Type_not_fully_instantiated _ -> Error
    | Unequal_synthesized_type -> Error
    | Checking_struct_at_degenerated_record _ -> Error
    | Missing_field_in_struct _ -> Error
    | Unnamed_field_in_struct -> Error
    | Duplicate_field_in_struct _ -> Error
    | Missing_constructor_in_match _ -> Error
    | Unnamed_variable_in_match -> Error
    | Checking_struct_against_nonrecord _ -> Error
    | No_such_constructor _ -> Error
    | Missing_instantiation_constructor _ -> Error
    | Unequal_indices -> Error
    | Checking_constructor_against_nondatatype _ -> Error
    | Checking_mismatch -> Error
    | Unbound_variable _ -> Error
    | Undefined_constant _ -> Bug
    | No_such_field _ -> Error
    | Nonsynthesizing _ -> Error
    | Low_dimensional_argument_of_degeneracy _ -> Error
    | Missing_argument_of_degeneracy -> Error
    | Not_enough_arguments_to_function -> Error
    | Instantiating_zero_dimensional_type -> Error
    | Not_enough_arguments_to_instantiation -> Error
    | Applying_nonfunction_nontype -> Error
    | Wrong_number_of_arguments_to_constructor _ -> Error
    | Higher_dimensional_match_not_implemented -> Error
    | Matching_datatype_has_degeneracy -> Error
    | Index_variables_duplicated -> Error
    | Non_variable_index_in_match -> Error
    | Degenerated_variable_index_in_match -> Error
    | Wrong_number_of_arguments_to_pattern _ -> Error
    | No_such_constructor_in_match _ -> Error
    | Duplicate_constructor_in_match _ -> Error
    | Index_variable_in_index_value -> Error
    | Matching_on_nondatatype _ -> Error
    | Matching_on_let_bound_variable -> Error
    | Dimension_mismatch _ -> Bug (* Sometimes Error? *)
    | Unsupported_numeral _ -> Error
    | Anomaly _ -> Bug

  (** A short, concise, ideally Google-able string representation for each message code. *)
  let short_code : t -> string = function
    | Parse_error _ -> "E0000"
    | Not_enough_lambdas _ -> "E3349"
    | Type_not_fully_instantiated _ -> "E7375"
    | Unequal_synthesized_type -> "E9298"
    | Checking_struct_at_degenerated_record _ -> "E8550"
    | Missing_field_in_struct _ -> "E3907"
    | Unnamed_field_in_struct -> "E4032"
    | Duplicate_field_in_struct _ -> "E3907"
    | Missing_constructor_in_match _ -> "E4524"
    | Unnamed_variable_in_match -> "E9130"
    | Checking_struct_against_nonrecord _ -> "E5951"
    | No_such_constructor _ -> "E2441"
    | Missing_instantiation_constructor _ -> "E5012"
    | Unequal_indices -> "E2128"
    | Checking_constructor_against_nondatatype _ -> "E0980"
    | Checking_mismatch -> "E1639"
    | Unbound_variable _ -> "E5683"
    | Undefined_constant _ -> "E8902"
    | No_such_field _ -> "E9490"
    | Nonsynthesizing _ -> "E1561"
    | Low_dimensional_argument_of_degeneracy _ -> "E7321"
    | Missing_argument_of_degeneracy -> "E5827"
    | Not_enough_arguments_to_function -> "E2436"
    | Instantiating_zero_dimensional_type -> "E8486"
    | Not_enough_arguments_to_instantiation -> "E1920"
    | Applying_nonfunction_nontype -> "E0794"
    | Wrong_number_of_arguments_to_constructor _ -> "E3871"
    | Higher_dimensional_match_not_implemented -> "E2858"
    | Matching_datatype_has_degeneracy -> "E3802"
    | Index_variables_duplicated -> "E8825"
    | Non_variable_index_in_match -> "E7910"
    | Degenerated_variable_index_in_match -> "E2687"
    | Wrong_number_of_arguments_to_pattern _ -> "E8972"
    | No_such_constructor_in_match _ -> "E8969"
    | Duplicate_constructor_in_match _ -> "E8969"
    | Index_variable_in_index_value -> "E6437"
    | Matching_on_nondatatype _ -> "E1270"
    | Matching_on_let_bound_variable -> "E7098"
    | Dimension_mismatch _ -> "E0367"
    | Unsupported_numeral _ -> "E8920"
    | Anomaly _ -> "E9499"

  let default_text : t -> text = function
    | Parse_error msg -> textf "Parse error: %s" msg
    | Not_enough_lambdas n ->
        textf "Not enough variables for a higher-dimensional abstraction: need at least %d more" n
    | Not_enough_arguments_to_function ->
        text "Not enough arguments for a higher-dimensional function application"
    | Not_enough_arguments_to_instantiation ->
        text "Not enough arguments to instantiate a higher-dimensional type"
    | Type_not_fully_instantiated str -> textf "Type not fully instantiated in %s" str
    | Instantiating_zero_dimensional_type -> text "Can't apply/instantiate a zero-dimensional type"
    | Unequal_synthesized_type ->
        text "Term synthesized a different type than it's being checked against"
    | Checking_struct_at_degenerated_record r ->
        textf "Can't check a struct against a record %s with a nonidentity degeneracy applied"
          (name_of r)
    | Missing_field_in_struct f -> textf "Record field %s missing in struct" (Field.to_string f)
    | Unnamed_field_in_struct -> text "Unnamed field in struct"
    | Duplicate_field_in_struct f ->
        textf "Record field %s appears more than once in struct" (Field.to_string f)
    | Missing_constructor_in_match c ->
        textf "Missing match clause for constructor %s" (Constr.to_string c)
    | Unnamed_variable_in_match -> text "Unnamed match variable"
    | Checking_struct_against_nonrecord c ->
        textf "Attempting to check struct against non-record type %s" (name_of c)
    | Checking_constructor_against_nondatatype (c, d) ->
        textf "Attempting to check constructor %s against non-datatype %s" (Constr.to_string c)
          (name_of d)
    | No_such_constructor (d, c) ->
        textf "Datatype %s has no constructor named %s" (name_of d) (Constr.to_string c)
    | Wrong_number_of_arguments_to_constructor (c, n) ->
        if n > 0 then textf "Too many arguments to constructor %s (%d extra)" (Constr.to_string c) n
        else
          textf "Not enough arguments to constructor %s (need %d more)" (Constr.to_string c) (abs n)
    | No_such_field (d, f) ->
        textf "%s has no field named %s"
          (match d with
          | Some d -> "Record " ^ name_of d
          | None -> "Non-record type")
          (Field.to_string f)
    | Missing_instantiation_constructor (exp, got) ->
        textf
          "Instantiation arguments of datatype must be matching constructors: expected %s got %s"
          (Constr.to_string exp)
          (match got with
          | None -> "non-constructor"
          | Some c -> Constr.to_string c)
    | Unequal_indices ->
        text "Indices of constructor application don't match those of datatype instance"
    | Checking_mismatch -> text "Checking term doesn't check against that type"
    | Unbound_variable c -> textf "Unbound variable: %s" c
    | Undefined_constant c -> textf "Unbound variable: %s" (name_of c)
    | Nonsynthesizing pos -> textf "Non-synthesizing term in synthesizing position (%s)" pos
    | Low_dimensional_argument_of_degeneracy (deg, dim) ->
        textf "Argument of %s must be at least %d-dimensional" deg dim
    | Missing_argument_of_degeneracy -> text "Missing arguments of degeneracy"
    | Applying_nonfunction_nontype -> text "Attempt to apply/instantiate a non-function non-type"
    | Higher_dimensional_match_not_implemented ->
        text "Matching on higher-dimensional types is not yet implemented"
    | Matching_datatype_has_degeneracy ->
        text "Can't match on element of a datatype with degeneracy applied"
    | Index_variables_duplicated -> text "Indices of a match variable must be distinct variables"
    | Non_variable_index_in_match -> text "Indices of a match variable must be free variables"
    | Degenerated_variable_index_in_match ->
        text "Indices of a match variable must be free variables without degeneracies"
    | Wrong_number_of_arguments_to_pattern (c, n) ->
        if n > 0 then
          textf "Too many arguments to constructor %s in match pattern (%d extra)"
            (Constr.to_string c) n
        else
          textf "Not enough arguments to constructor %s in match pattern (need %d more)"
            (Constr.to_string c) (abs n)
    | No_such_constructor_in_match (d, c) ->
        textf "Datatype %s being matched against has no constructor %s" (name_of d)
          (Constr.to_string c)
    | Duplicate_constructor_in_match c ->
        textf "Constructor %s appears twice in match" (Constr.to_string c)
    | Index_variable_in_index_value -> text "Free index variable occurs in inferred index value"
    | Matching_on_nondatatype c -> (
        match c with
        | Some c -> textf "Can't match on variable belonging to non-datatype %s" (name_of c)
        | None -> text "Can't match on variable belonging to non-datatype")
    | Matching_on_let_bound_variable -> text "Can't match on a let-bound variable"
    | Dimension_mismatch (op, a, b) ->
        textf "Dimension mismatch in %s (%d ≠ %d)" op (to_int a) (to_int b)
    | Unsupported_numeral n -> textf "Unsupported numeral: %f" n
    | Anomaly str -> text ("Anomaly: " ^ str)
end

include Asai.StructuredReporter.Make (Code)
