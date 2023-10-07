open Dim

module Code = struct
  type t =
    | Not_enough_lambdas
    | Not_enough_arguments_to_function
    | Not_enough_arguments_to_instantiation
    | Type_not_fully_instantiated
    | Instantiating_zero_dimensional_type
    | Unequal_synthesized_type
    | Checking_struct_at_degenerated_record of Constant.t
    | Missing_field_in_struct of Field.t
    | Duplicate_field_in_struct of Field.t
    | Missing_constructor_in_match of Constr.t
    | Checking_struct_against_nonrecord of Constant.t
    | Checking_constructor_against_nondatatype of Constr.t * Constant.t
    | No_such_constructor of Constant.t * Constr.t
    | Wrong_number_of_arguments_to_constructor
    | No_such_field of Constant.t option * Field.t
    | Missing_instantiation_constructor of Constr.t * Constr.t option
    | Unequal_indices
    | Checking_mismatch
    | Unbound_variable of Constant.t
    | Nonsynthesizing_argument_of_degeneracy of string
    | Low_dimensional_argument_of_degeneracy of string * int
    | Missing_argument_of_degeneracy
    | Applying_nonfunction_nontype
    | Higher_dimensional_match_not_implemented
    | Matching_datatype_has_degeneracy
    | Index_variables_duplicated
    | Non_variable_index_in_match
    | Degenerated_variable_index_in_match
    | Wrong_number_of_arguments_to_pattern of Constr.t
    | No_such_constructor_in_match of Constant.t * Constr.t
    | Duplicate_constructor_in_match of Constr.t
    | Index_variable_in_index_value
    | Matching_on_nondatatype
    | Matching_on_let_bound_variable
    | Dimension_mismatch : string * 'a D.t * 'b D.t -> t
    | Anomaly

  (** The default severity of messages with a particular message code. *)
  let default_severity : t -> Asai.Diagnostic.severity = function
    | Not_enough_lambdas -> Error
    | Type_not_fully_instantiated -> Error
    | Unequal_synthesized_type -> Error
    | Checking_struct_at_degenerated_record _ -> Error
    | Missing_field_in_struct _ -> Error
    | Duplicate_field_in_struct _ -> Error
    | Missing_constructor_in_match _ -> Error
    | Checking_struct_against_nonrecord _ -> Error
    | No_such_constructor _ -> Error
    | Missing_instantiation_constructor _ -> Error
    | Unequal_indices -> Error
    | Checking_constructor_against_nondatatype _ -> Error
    | Checking_mismatch -> Error
    | Unbound_variable _ -> Error
    | No_such_field _ -> Error
    | Nonsynthesizing_argument_of_degeneracy _ -> Error
    | Low_dimensional_argument_of_degeneracy _ -> Error
    | Missing_argument_of_degeneracy -> Error
    | Not_enough_arguments_to_function -> Error
    | Instantiating_zero_dimensional_type -> Error
    | Not_enough_arguments_to_instantiation -> Error
    | Applying_nonfunction_nontype -> Error
    | Wrong_number_of_arguments_to_constructor -> Error
    | Higher_dimensional_match_not_implemented -> Error
    | Matching_datatype_has_degeneracy -> Error
    | Index_variables_duplicated -> Error
    | Non_variable_index_in_match -> Error
    | Degenerated_variable_index_in_match -> Error
    | Wrong_number_of_arguments_to_pattern _ -> Error
    | No_such_constructor_in_match _ -> Error
    | Duplicate_constructor_in_match _ -> Error
    | Index_variable_in_index_value -> Error
    | Matching_on_nondatatype -> Error
    | Matching_on_let_bound_variable -> Error
    | Dimension_mismatch _ -> Bug (* Sometimes Error? *)
    | Anomaly -> Bug

  (** A short, concise, ideally Google-able string representation for each message code. *)
  let to_string : t -> string = function
    | Not_enough_lambdas -> "E3349"
    | Type_not_fully_instantiated -> "E7375"
    | Unequal_synthesized_type -> "E9298"
    | Checking_struct_at_degenerated_record _ -> "E8550"
    | Missing_field_in_struct _ -> "E3907"
    | Duplicate_field_in_struct _ -> "E3907"
    | Missing_constructor_in_match _ -> "E4524"
    | Checking_struct_against_nonrecord _ -> "E5951"
    | No_such_constructor _ -> "E2441"
    | Missing_instantiation_constructor _ -> "E5012"
    | Unequal_indices -> "E2128"
    | Checking_constructor_against_nondatatype _ -> "E0980"
    | Checking_mismatch -> "E1639"
    | Unbound_variable _ -> "E5683"
    | No_such_field _ -> "E9490"
    | Nonsynthesizing_argument_of_degeneracy _ -> "E1561"
    | Low_dimensional_argument_of_degeneracy _ -> "E7321"
    | Missing_argument_of_degeneracy -> "E5827"
    | Not_enough_arguments_to_function -> "E2436"
    | Instantiating_zero_dimensional_type -> "E8486"
    | Not_enough_arguments_to_instantiation -> "E1920"
    | Applying_nonfunction_nontype -> "E0794"
    | Wrong_number_of_arguments_to_constructor -> "E3871"
    | Higher_dimensional_match_not_implemented -> "E2858"
    | Matching_datatype_has_degeneracy -> "E3802"
    | Index_variables_duplicated -> "E8825"
    | Non_variable_index_in_match -> "E7910"
    | Degenerated_variable_index_in_match -> "E2687"
    | Wrong_number_of_arguments_to_pattern _ -> "E8972"
    | No_such_constructor_in_match _ -> "E8969"
    | Duplicate_constructor_in_match _ -> "E8969"
    | Index_variable_in_index_value -> "E6437"
    | Matching_on_nondatatype -> "E1270"
    | Matching_on_let_bound_variable -> "E7098"
    | Dimension_mismatch _ -> "E0367"
    | Anomaly -> "E9499"
end

include Asai.Logger.Make (Code)

let die ?severity (e : Code.t) =
  match e with
  | Not_enough_lambdas ->
      fatal ?severity e "Not enough variables for a higher-dimensional abstraction"
  | Not_enough_arguments_to_function ->
      fatal ?severity e "Not enough arguments for a higher-dimensional function application"
  | Not_enough_arguments_to_instantiation ->
      fatal ?severity e "Not enough arguments to instantiate a higher-dimensional type"
  | Type_not_fully_instantiated ->
      fatal ?severity e "Can't check against a non-fully-instantiated higher-dimensional type"
  | Instantiating_zero_dimensional_type ->
      fatal ?severity e "Can't apply/instantiate a zero-dimensional type"
  | Unequal_synthesized_type ->
      fatal ?severity e "Term synthesized a different type than it's being checked against"
  | Checking_struct_at_degenerated_record r ->
      fatalf ?severity e
        "Can't check a struct against a record %s with a nonidentity degeneracy applied"
        (Constant.to_string r)
  | Missing_field_in_struct f ->
      fatalf ?severity e "Record field %s missing in struct" (Field.to_string f)
  | Duplicate_field_in_struct f ->
      fatalf ?severity e "Record field %s appears more than once in struct" (Field.to_string f)
  | Missing_constructor_in_match c ->
      fatalf ?severity e "Missing match clause for constructor %s" (Constr.to_string c)
  | Checking_struct_against_nonrecord c ->
      fatalf ?severity e "Attempting to check struct against non-record type %s"
        (Constant.to_string c)
  | Checking_constructor_against_nondatatype (c, d) ->
      fatalf ?severity e "Attempting to check constructor %s against non-datatype %s"
        (Constr.to_string c) (Constant.to_string d)
  | No_such_constructor (d, c) ->
      fatalf ?severity e "Datatype %s has no constructor named %s" (Constant.to_string d)
        (Constr.to_string c)
  | Wrong_number_of_arguments_to_constructor ->
      fatal ?severity e "Wrong number of arguments to constructor"
  | No_such_field (d, f) ->
      fatalf ?severity e "%s has no field named %s"
        (match d with
        | Some d -> "Record " ^ Constant.to_string d
        | None -> "Non-record type")
        (Field.to_string f)
  | Missing_instantiation_constructor (exp, got) ->
      fatalf ?severity e
        "Instantiation arguments of datatype must be matching constructors: expected %s, got %s"
        (Constr.to_string exp)
        (match got with
        | None -> "non-constructor"
        | Some c -> Constr.to_string c)
  | Unequal_indices ->
      fatal ?severity e "Indices of constructor application don't match those of datatype instance"
  | Checking_mismatch -> fatal ?severity e "Checking term doesn't check against that type"
  | Unbound_variable c -> fatalf ?severity e "Unbound variable: %s" (Constant.to_string c)
  | Nonsynthesizing_argument_of_degeneracy deg ->
      fatalf ?severity e "Argument of %s must synthesize" deg
  | Low_dimensional_argument_of_degeneracy (deg, dim) ->
      fatalf ?severity e "Argument of %s must be at least %d-dimensional" deg dim
  | Missing_argument_of_degeneracy -> fatal ?severity e "Missing arguments of degeneracy"
  | Applying_nonfunction_nontype ->
      fatal ?severity e "Attempt to apply/instantiate a non-function, non-type"
  | Higher_dimensional_match_not_implemented ->
      fatal ?severity e "Matching on higher-dimensional types is not yet implemented"
  | Matching_datatype_has_degeneracy ->
      fatal ?severity e "Can't match on element of a datatype with degeneracy applied"
  | Index_variables_duplicated ->
      fatal ?severity e "Indices of a match variable must be distinct variables"
  | Non_variable_index_in_match ->
      fatal ?severity e "Indices of a match variable must be free variables"
  | Degenerated_variable_index_in_match ->
      fatal ?severity e "Indices of a match variable must be free variables without degeneracies"
  | Wrong_number_of_arguments_to_pattern c ->
      fatalf ?severity e "Wrong number of arguments to constructor %s in match pattern"
        (Constr.to_string c)
  | No_such_constructor_in_match (d, c) ->
      fatalf ?severity e "Datatype %s being matched against has no constructor %s"
        (Constant.to_string d) (Constr.to_string c)
  | Duplicate_constructor_in_match c ->
      fatalf ?severity e "Constructor %s appears twice in match" (Constr.to_string c)
  | Index_variable_in_index_value ->
      fatal ?severity e "Free index variable occurs in inferred index value"
  | Matching_on_nondatatype -> fatal ?severity e "Can't match on variable belonging to non-datatype"
  | Matching_on_let_bound_variable -> fatal ?severity e "Can't match on a let-bound variable"
  | Dimension_mismatch (op, a, b) ->
      fatalf ?severity e "Dimension mismatch in %s (%d ≠ %d)" op (to_int a) (to_int b)
  | Anomaly -> fatal ?severity e "Anomaly"
