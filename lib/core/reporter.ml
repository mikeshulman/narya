open Dim
open Scope
open Asai.Diagnostic

module Code = struct
  type t =
    | Parse_error : t
    | Parsing_ambiguity : string -> t
    | No_relative_precedence : string * string -> t
    | Invalid_variable : string -> t
    | Invalid_numeral : string -> t
    | Invalid_constr : string -> t
    | Invalid_field : string -> t
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
    | Checking_lambda_at_nonfunction : t
    | Checking_struct_at_nonrecord : Constant.t option -> t
    | No_such_constructor : Constant.t option * Constr.t -> t
    | Wrong_number_of_arguments_to_constructor : Constr.t * int -> t
    | No_such_field : Constant.t option * Field.t -> t
    | Missing_instantiation_constructor : Constr.t * Constr.t option -> t
    | Unequal_indices : t
    | Unbound_variable : string -> t
    | Undefined_constant : Constant.t -> t
    | Nonsynthesizing : string -> t
    | Low_dimensional_argument_of_degeneracy : (string * 'a D.t) -> t
    | Missing_argument_of_degeneracy : string -> t
    | Applying_nonfunction_nontype : t
    | Unimplemented : string -> t
    | Matching_datatype_has_degeneracy : t
    | Invalid_match_index : t
    | Wrong_number_of_arguments_to_pattern : Constr.t * int -> t
    | No_such_constructor_in_match : Constant.t * Constr.t -> t
    | Duplicate_constructor_in_match : Constr.t -> t
    | Index_variable_in_index_value : t
    | Matching_on_nondatatype : Constant.t option -> t
    | Matching_on_let_bound_variable : t
    | Dimension_mismatch : string * 'a D.t * 'b D.t -> t
    | Invalid_variable_face : 'a D.t * ('n, 'm) sface -> t
    | Unsupported_numeral : float -> t
    | Anomaly : string -> t

  (** The default severity of messages with a particular message code. *)
  let default_severity : t -> Asai.Diagnostic.severity = function
    | Parse_error -> Error
    | Parsing_ambiguity _ -> Error
    | No_relative_precedence _ -> Error
    | Invalid_variable _ -> Error
    | Invalid_numeral _ -> Error
    | Invalid_constr _ -> Error
    | Invalid_field _ -> Error
    | Not_enough_lambdas _ -> Error
    | Type_not_fully_instantiated _ -> Error
    | Unequal_synthesized_type -> Error
    | Checking_struct_at_degenerated_record _ -> Error
    | Missing_field_in_struct _ -> Error
    | Unnamed_field_in_struct -> Error
    | Duplicate_field_in_struct _ -> Error
    | Missing_constructor_in_match _ -> Error
    | Unnamed_variable_in_match -> Error
    | Checking_lambda_at_nonfunction -> Error
    | Checking_struct_at_nonrecord _ -> Error
    | No_such_constructor _ -> Error
    | Missing_instantiation_constructor _ -> Error
    | Unequal_indices -> Error
    | Unbound_variable _ -> Error
    | Undefined_constant _ -> Bug
    | No_such_field _ -> Error
    | Nonsynthesizing _ -> Error
    | Low_dimensional_argument_of_degeneracy _ -> Error
    | Missing_argument_of_degeneracy _ -> Error
    | Not_enough_arguments_to_function -> Error
    | Instantiating_zero_dimensional_type -> Error
    | Invalid_variable_face _ -> Error
    | Not_enough_arguments_to_instantiation -> Error
    | Applying_nonfunction_nontype -> Error
    | Wrong_number_of_arguments_to_constructor _ -> Error
    | Unimplemented _ -> Error
    | Matching_datatype_has_degeneracy -> Error
    | Invalid_match_index -> Error
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
    (* Usually bugs *)
    | Anomaly _ -> "E0000"
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
    | No_relative_precedence _ -> "E0206"
    (* Scope errors *)
    | Unbound_variable _ -> "E0300"
    | Undefined_constant _ -> "E0301"
    (* Bidirectional typechecking *)
    | Nonsynthesizing _ -> "E0400"
    | Unequal_synthesized_type -> "E0401"
    (* Dimensions *)
    | Dimension_mismatch _ -> "E0500"
    | Not_enough_lambdas _ -> "E0501"
    | Not_enough_arguments_to_function -> "E0502"
    | Not_enough_arguments_to_instantiation -> "E0503"
    | Type_not_fully_instantiated _ -> "E0504"
    | Instantiating_zero_dimensional_type -> "E0505"
    | Invalid_variable_face _ -> "E0506"
    (* Degeneracies *)
    | Missing_argument_of_degeneracy _ -> "E0600"
    | Low_dimensional_argument_of_degeneracy _ -> "E0601"
    (* Function-types *)
    | Checking_lambda_at_nonfunction -> "E0700"
    | Applying_nonfunction_nontype -> "E0701"
    (* Record fields *)
    | No_such_field _ -> "E0800"
    (* Structs *)
    | Checking_struct_at_nonrecord _ -> "E0900"
    | Checking_struct_at_degenerated_record _ -> "E0901"
    | Missing_field_in_struct _ -> "E0902"
    | Unnamed_field_in_struct -> "E0903"
    | Duplicate_field_in_struct _ -> "E0904"
    (* Datatype constructors *)
    | No_such_constructor _ -> "E1000"
    | Wrong_number_of_arguments_to_constructor _ -> "E1001"
    | Missing_instantiation_constructor _ -> "E1002"
    | Unequal_indices -> "E1003"
    (* Matches *)
    (* - Match variable *)
    | Unnamed_variable_in_match -> "E1100"
    | Matching_on_let_bound_variable -> "E1101"
    (* - Match type *)
    | Matching_on_nondatatype _ -> "E1200"
    | Matching_datatype_has_degeneracy -> "E1201"
    | Invalid_match_index -> "E1202"
    (* - Match branches *)
    | Missing_constructor_in_match _ -> "E1300"
    | No_such_constructor_in_match _ -> "E1301"
    | Duplicate_constructor_in_match _ -> "E1302"
    | Wrong_number_of_arguments_to_pattern _ -> "E1303"
    | Index_variable_in_index_value -> "E1304"

  let default_text : t -> text = function
    | Parse_error -> text "Parse error"
    | Parsing_ambiguity str -> textf "Potential parsing ambiguity: %s" str
    | Invalid_variable str -> textf "Invalid local variable name: %s" str
    | Invalid_field str -> textf "Invalid field name: %s" str
    | Invalid_constr str -> textf "Invalid constructor name: %s" str
    | Invalid_numeral str -> textf "Invalid numeral: %s" str
    | Invalid_variable_face (k, fa) ->
        textf "Invalid face: %d-dimensional variable has no face %s" (to_int k) (string_of_sface fa)
    | No_relative_precedence (n1, n2) ->
        textf
          "Notations \"%s\" and \"%s\" have no relative precedence or associativity; they can only be combined with parentheses"
          n1 n2
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
    | Checking_lambda_at_nonfunction -> text "Checking abstraction against non-function type"
    | Checking_struct_at_nonrecord c -> (
        match c with
        | Some c -> textf "Checking struct against non-record type %s" (name_of c)
        | None -> text "Checking struct against non-record type")
    | No_such_constructor (d, c) -> (
        match d with
        | Some d ->
            textf "Canonical type %s has no constructor named %s" (name_of d) (Constr.to_string c)
        | None -> textf "Non-datatype has no constructor named %s" (Constr.to_string c))
    | Wrong_number_of_arguments_to_constructor (c, n) ->
        if n > 0 then textf "Too many arguments to constructor %s (%d extra)" (Constr.to_string c) n
        else
          textf "Not enough arguments to constructor %s (need %d more)" (Constr.to_string c) (abs n)
    | No_such_field (d, f) -> (
        match d with
        | Some d -> textf "Record %s has no field named %s" (name_of d) (Field.to_string f)
        | None -> textf "Non-record type has no field named %s" (Field.to_string f))
    | Missing_instantiation_constructor (exp, got) ->
        textf
          "Instantiation arguments of datatype must be matching constructors: expected %s got %s"
          (Constr.to_string exp)
          (match got with
          | None -> "non-constructor"
          | Some c -> Constr.to_string c)
    | Unequal_indices ->
        text "Indices of constructor application don't match those of datatype instance"
    | Unbound_variable c -> textf "Unbound variable: %s" c
    | Undefined_constant c -> textf "Undefined constant: %s" (name_of c)
    | Nonsynthesizing pos -> textf "Non-synthesizing term in synthesizing position (%s)" pos
    | Low_dimensional_argument_of_degeneracy (deg, dim) ->
        textf "Argument of %s must be at least %d-dimensional" deg (to_int dim)
    | Missing_argument_of_degeneracy deg -> textf "Missing argument for degeneracy %s" deg
    | Applying_nonfunction_nontype -> text "Attempt to apply/instantiate a non-function non-type"
    | Unimplemented str -> textf "%s is not yet implemented" str
    | Matching_datatype_has_degeneracy ->
        text "Can't match on element of a datatype with degeneracy applied"
    | Invalid_match_index ->
        text "Indices of a match variable must be distinct free variables without degeneracies"
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
