open Dim
open Scope

module Code = struct
  type _ code =
    | Not_enough_lambdas : int code
    | Not_enough_arguments_to_function : unit code
    | Not_enough_arguments_to_instantiation : unit code
    | Type_not_fully_instantiated : string code
    | Instantiating_zero_dimensional_type : unit code
    | Unequal_synthesized_type : unit code
    | Checking_struct_at_degenerated_record : Constant.t code
    | Missing_field_in_struct : Field.t code
    | Duplicate_field_in_struct : Field.t code
    | Missing_constructor_in_match : Constr.t code
    | Checking_struct_against_nonrecord : Constant.t code
    | Checking_constructor_against_nondatatype : (Constr.t * Constant.t) code
    | No_such_constructor : (Constant.t * Constr.t) code
    | Wrong_number_of_arguments_to_constructor : (Constr.t * int) code
    | No_such_field : (Constant.t option * Field.t) code
    | Missing_instantiation_constructor : (Constr.t * Constr.t option) code
    | Unequal_indices : unit code
    | Checking_mismatch : unit code
    | Unbound_variable : string code
    | Undefined_constant : Constant.t code
    | Nonsynthesizing_argument_of_degeneracy : string code
    | Low_dimensional_argument_of_degeneracy : (string * int) code
    | Missing_argument_of_degeneracy : unit code
    | Applying_nonfunction_nontype : unit code
    | Higher_dimensional_match_not_implemented : unit code
    | Matching_datatype_has_degeneracy : unit code
    | Index_variables_duplicated : unit code
    | Non_variable_index_in_match : unit code
    | Degenerated_variable_index_in_match : unit code
    | Wrong_number_of_arguments_to_pattern : (Constr.t * int) code
    | No_such_constructor_in_match : (Constant.t * Constr.t) code
    | Duplicate_constructor_in_match : Constr.t code
    | Index_variable_in_index_value : unit code
    | Matching_on_nondatatype : Constant.t option code
    | Matching_on_let_bound_variable : unit code
    | Dimension_mismatch : (string * 'a D.t * 'b D.t) code
    | Anomaly : string code

  type t = Code : 'a code -> t

  (** The default severity of messages with a particular message code. *)
  let default_severity : t -> Asai.Diagnostic.severity =
   fun (Code code) ->
    match code with
    | Not_enough_lambdas -> Error
    | Type_not_fully_instantiated -> Error
    | Unequal_synthesized_type -> Error
    | Checking_struct_at_degenerated_record -> Error
    | Missing_field_in_struct -> Error
    | Duplicate_field_in_struct -> Error
    | Missing_constructor_in_match -> Error
    | Checking_struct_against_nonrecord -> Error
    | No_such_constructor -> Error
    | Missing_instantiation_constructor -> Error
    | Unequal_indices -> Error
    | Checking_constructor_against_nondatatype -> Error
    | Checking_mismatch -> Error
    | Unbound_variable -> Error
    | Undefined_constant -> Bug
    | No_such_field -> Error
    | Nonsynthesizing_argument_of_degeneracy -> Error
    | Low_dimensional_argument_of_degeneracy -> Error
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
    | Wrong_number_of_arguments_to_pattern -> Error
    | No_such_constructor_in_match -> Error
    | Duplicate_constructor_in_match -> Error
    | Index_variable_in_index_value -> Error
    | Matching_on_nondatatype -> Error
    | Matching_on_let_bound_variable -> Error
    | Dimension_mismatch -> Bug (* Sometimes Error? *)
    | Anomaly -> Bug

  (** A short, concise, ideally Google-able string representation for each message code. *)
  let to_string : t -> string =
   fun (Code code) ->
    match code with
    | Not_enough_lambdas -> "E3349"
    | Type_not_fully_instantiated -> "E7375"
    | Unequal_synthesized_type -> "E9298"
    | Checking_struct_at_degenerated_record -> "E8550"
    | Missing_field_in_struct -> "E3907"
    | Duplicate_field_in_struct -> "E3907"
    | Missing_constructor_in_match -> "E4524"
    | Checking_struct_against_nonrecord -> "E5951"
    | No_such_constructor -> "E2441"
    | Missing_instantiation_constructor -> "E5012"
    | Unequal_indices -> "E2128"
    | Checking_constructor_against_nondatatype -> "E0980"
    | Checking_mismatch -> "E1639"
    | Unbound_variable -> "E5683"
    | Undefined_constant -> "E8902"
    | No_such_field -> "E9490"
    | Nonsynthesizing_argument_of_degeneracy -> "E1561"
    | Low_dimensional_argument_of_degeneracy -> "E7321"
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
    | Wrong_number_of_arguments_to_pattern -> "E8972"
    | No_such_constructor_in_match -> "E8969"
    | Duplicate_constructor_in_match -> "E8969"
    | Index_variable_in_index_value -> "E6437"
    | Matching_on_nondatatype -> "E1270"
    | Matching_on_let_bound_variable -> "E7098"
    | Dimension_mismatch -> "E0367"
    | Anomaly -> "E9499"
end

include Asai.Logger.Make (Code)

let die : type a b. ?severity:Asai.Diagnostic.severity -> a Code.code -> a -> b =
 fun ?severity e arg ->
  match (e, arg) with
  | Not_enough_lambdas, n ->
      fatalf ?severity (Code e)
        "Not enough variables for a higher-dimensional abstraction: need at least %d more" n
  | Not_enough_arguments_to_function, () ->
      fatal ?severity (Code e) "Not enough arguments for a higher-dimensional function application"
  | Not_enough_arguments_to_instantiation, () ->
      fatal ?severity (Code e) "Not enough arguments to instantiate a higher-dimensional type"
  | Type_not_fully_instantiated, str ->
      fatalf ?severity (Code e) "Type not fully instantiated in %s" str
  | Instantiating_zero_dimensional_type, () ->
      fatal ?severity (Code e) "Can't apply/instantiate a zero-dimensional type"
  | Unequal_synthesized_type, () ->
      fatal ?severity (Code e) "Term synthesized a different type than it's being checked against"
  | Checking_struct_at_degenerated_record, r ->
      fatalf ?severity (Code e)
        "Can't check a struct against a record %s with a nonidentity degeneracy applied" (name_of r)
  | Missing_field_in_struct, f ->
      fatalf ?severity (Code e) "Record field %s missing in struct" (Field.to_string f)
  | Duplicate_field_in_struct, f ->
      fatalf ?severity (Code e) "Record field %s appears more than once in struct"
        (Field.to_string f)
  | Missing_constructor_in_match, c ->
      fatalf ?severity (Code e) "Missing match clause for constructor %s" (Constr.to_string c)
  | Checking_struct_against_nonrecord, c ->
      fatalf ?severity (Code e) "Attempting to check struct against non-record type %s" (name_of c)
  | Checking_constructor_against_nondatatype, (c, d) ->
      fatalf ?severity (Code e) "Attempting to check constructor %s against non-datatype %s"
        (Constr.to_string c) (name_of d)
  | No_such_constructor, (d, c) ->
      fatalf ?severity (Code e) "Datatype %s has no constructor named %s" (name_of d)
        (Constr.to_string c)
  | Wrong_number_of_arguments_to_constructor, (c, n) ->
      if n > 0 then
        fatalf ?severity (Code e) "Too many arguments to constructor %s (%d extra)"
          (Constr.to_string c) n
      else
        fatalf ?severity (Code e) "Not enough arguments to constructor %s (need %d more)"
          (Constr.to_string c) (abs n)
  | No_such_field, (d, f) ->
      fatalf ?severity (Code e) "%s has no field named %s"
        (match d with
        | Some d -> "Record " ^ name_of d
        | None -> "Non-record type")
        (Field.to_string f)
  | Missing_instantiation_constructor, (exp, got) ->
      fatalf ?severity (Code e)
        "Instantiation arguments of datatype must be matching constructors: expected %s, got %s"
        (Constr.to_string exp)
        (match got with
        | None -> "non-constructor"
        | Some c -> Constr.to_string c)
  | Unequal_indices, () ->
      fatal ?severity (Code e)
        "Indices of constructor application don't match those of datatype instance"
  | Checking_mismatch, () ->
      fatal ?severity (Code e) "Checking term doesn't check against that type"
  | Unbound_variable, c -> fatalf ?severity (Code e) "Unbound variable: %s" c
  | Undefined_constant, c -> fatalf ?severity (Code e) "Unbound variable: %s" (name_of c)
  | Nonsynthesizing_argument_of_degeneracy, deg ->
      fatalf ?severity (Code e) "Argument of %s must synthesize" deg
  | Low_dimensional_argument_of_degeneracy, (deg, dim) ->
      fatalf ?severity (Code e) "Argument of %s must be at least %d-dimensional" deg dim
  | Missing_argument_of_degeneracy, () -> fatal ?severity (Code e) "Missing arguments of degeneracy"
  | Applying_nonfunction_nontype, () ->
      fatal ?severity (Code e) "Attempt to apply/instantiate a non-function, non-type"
  | Higher_dimensional_match_not_implemented, () ->
      fatal ?severity (Code e) "Matching on higher-dimensional types is not yet implemented"
  | Matching_datatype_has_degeneracy, () ->
      fatal ?severity (Code e) "Can't match on element of a datatype with degeneracy applied"
  | Index_variables_duplicated, () ->
      fatal ?severity (Code e) "Indices of a match variable must be distinct variables"
  | Non_variable_index_in_match, () ->
      fatal ?severity (Code e) "Indices of a match variable must be free variables"
  | Degenerated_variable_index_in_match, () ->
      fatal ?severity (Code e)
        "Indices of a match variable must be free variables without degeneracies"
  | Wrong_number_of_arguments_to_pattern, (c, n) ->
      if n > 0 then
        fatalf ?severity (Code e) "Too many arguments to constructor %s in match pattern (%d extra)"
          (Constr.to_string c) n
      else
        fatalf ?severity (Code e)
          "Not enough arguments to constructor %s in match pattern (need %d more)"
          (Constr.to_string c) (abs n)
  | No_such_constructor_in_match, (d, c) ->
      fatalf ?severity (Code e) "Datatype %s being matched against has no constructor %s"
        (name_of d) (Constr.to_string c)
  | Duplicate_constructor_in_match, c ->
      fatalf ?severity (Code e) "Constructor %s appears twice in match" (Constr.to_string c)
  | Index_variable_in_index_value, () ->
      fatal ?severity (Code e) "Free index variable occurs in inferred index value"
  | Matching_on_nondatatype, c -> (
      match c with
      | Some c ->
          fatalf ?severity (Code e) "Can't match on variable belonging to non-datatype %s"
            (name_of c)
      | None -> fatal ?severity (Code e) "Can't match on variable belonging to non-datatype")
  | Matching_on_let_bound_variable, () ->
      fatal ?severity (Code e) "Can't match on a let-bound variable"
  | Dimension_mismatch, (op, a, b) ->
      fatalf ?severity (Code e) "Dimension mismatch in %s (%d ≠ %d)" op (to_int a) (to_int b)
  | Anomaly, str -> fatal ?severity (Code e) ("Anomaly: " ^ str)
