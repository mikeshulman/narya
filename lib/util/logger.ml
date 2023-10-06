module Code = struct
  type t =
    | Parse_error
    | Not_enough_lambdas
    | Not_enough_arguments_to_function
    | Not_enough_arguments_to_instantiation
    | Type_not_fully_instantiated
    | Instantiating_zero_dimensional_type
    | Unequal_synthesized_type
    | Checking_struct_at_degenerated_record
    | Missing_field_in_struct
    | Missing_constructor_in_match
    | Checking_struct_against_nonrecord
    | Checking_constructor_against_nondatatype
    | No_such_constructor
    | Wrong_number_of_arguments_to_constructor
    | No_such_field
    | Missing_instantiation_constructor
    | Unequal_indices
    | Checking_mismatch
    | Unbound_variable
    | Nonsynthesizing_argument_of_degeneracy
    | Low_dimensional_argument_of_degeneracy
    | Missing_argument_of_degeneracy
    | Applying_nonfunction_nontype
    | Dimension_mismatch
    | Anomaly

  (** The default severity of messages with a particular message code. *)
  let default_severity : t -> Asai.Diagnostic.severity = function
    | Parse_error -> Error
    | Not_enough_lambdas -> Error
    | Type_not_fully_instantiated -> Error
    | Unequal_synthesized_type -> Error
    | Checking_struct_at_degenerated_record -> Error
    | Missing_field_in_struct -> Error
    | Missing_constructor_in_match -> Error
    | Checking_struct_against_nonrecord -> Error
    | No_such_constructor -> Error
    | Missing_instantiation_constructor -> Error
    | Unequal_indices -> Error
    | Checking_constructor_against_nondatatype -> Error
    | Checking_mismatch -> Error
    | Unbound_variable -> Error
    | No_such_field -> Error
    | Nonsynthesizing_argument_of_degeneracy -> Error
    | Low_dimensional_argument_of_degeneracy -> Error
    | Missing_argument_of_degeneracy -> Error
    | Not_enough_arguments_to_function -> Error
    | Instantiating_zero_dimensional_type -> Error
    | Not_enough_arguments_to_instantiation -> Error
    | Applying_nonfunction_nontype -> Error
    | Wrong_number_of_arguments_to_constructor -> Error
    | Dimension_mismatch -> Bug
    | Anomaly -> Bug

  (** A short, concise, ideally Google-able string representation for each message code. *)
  let to_string : t -> string = function
    | Parse_error -> "E2530"
    | Not_enough_lambdas -> "E3349"
    | Type_not_fully_instantiated -> "E7375"
    | Unequal_synthesized_type -> "E9298"
    | Checking_struct_at_degenerated_record -> "E8550"
    | Missing_field_in_struct -> "E3907"
    | Missing_constructor_in_match -> "E4524"
    | Checking_struct_against_nonrecord -> "E5951"
    | No_such_constructor -> "E2441"
    | Missing_instantiation_constructor -> "E5012"
    | Unequal_indices -> "E2128"
    | Checking_constructor_against_nondatatype -> "E0980"
    | Checking_mismatch -> "E1639"
    | Unbound_variable -> "E5683"
    | No_such_field -> "E9490"
    | Nonsynthesizing_argument_of_degeneracy -> "E1561"
    | Low_dimensional_argument_of_degeneracy -> "E7321"
    | Missing_argument_of_degeneracy -> "E5827"
    | Not_enough_arguments_to_function -> "E2436"
    | Instantiating_zero_dimensional_type -> "E8486"
    | Not_enough_arguments_to_instantiation -> "E1920"
    | Applying_nonfunction_nontype -> "E0794"
    | Wrong_number_of_arguments_to_constructor -> "E3871"
    | Dimension_mismatch -> "E0367"
    | Anomaly -> "E9499"
end

include Asai.Logger.Make (Code)
