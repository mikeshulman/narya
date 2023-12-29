open Dim
open Scope
open Hctx
open Asai.Diagnostic
open Format

type printable = ..

let print : (formatter -> printable -> unit) ref = ref (fun _ _ -> raise (Failure "print not set"))
let pp_printable ppf pr = !print ppf pr

module Code = struct
  type t =
    | Parse_error : t
    | Parsing_ambiguity : string -> t
    | No_relative_precedence : string * string -> t
    | Invalid_variable : string list -> t
    | Invalid_numeral : string -> t
    | Invalid_constr : string -> t
    | Invalid_field : string -> t
    | Not_enough_lambdas : int -> t
    | Not_enough_arguments_to_function : t
    | Not_enough_arguments_to_instantiation : t
    | Type_not_fully_instantiated : string -> t
    | Instantiating_zero_dimensional_type : t
    | Unequal_synthesized_type : printable * printable -> t
    | Checking_struct_at_degenerated_record : Constant.t -> t
    | Missing_field_in_struct : Field.t -> t
    | Invalid_field_in_struct : t
    | Duplicate_field_in_struct : Field.t -> t
    | Missing_constructor_in_match : Constr.t -> t
    | Unnamed_variable_in_match : t
    | Checking_lambda_at_nonfunction : t
    | Checking_struct_at_nonrecord : printable -> t
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
    | Applying_nonfunction_nontype : printable * printable -> t
    | Unimplemented : string -> t
    | Matching_datatype_has_degeneracy : t
    | Invalid_match_index : t
    | Wrong_number_of_arguments_to_pattern : Constr.t * int -> t
    | No_such_constructor_in_match : Constant.t * Constr.t -> t
    | Duplicate_constructor_in_match : Constr.t -> t
    | Index_variable_in_index_value : t
    | Matching_on_nondatatype : Constant.t option -> t
    | Matching_on_let_bound_variable : Trie.path -> t
    | Dimension_mismatch : string * 'a D.t * 'b D.t -> t
    | Invalid_variable_face : 'a D.t * ('n, 'm) sface -> t
    | Unsupported_numeral : Q.t -> t
    | Anomaly : string -> t
    | No_such_level : printable * level -> t
    | Constant_already_defined : Trie.path -> t
    | Invalid_constant_name : string -> t
    | Constant_assumed : Trie.path -> t
    | Constant_defined : Trie.path -> t
    | Show : string * printable -> t

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
    | Unequal_synthesized_type _ -> Error
    | Checking_struct_at_degenerated_record _ -> Error
    | Missing_field_in_struct _ -> Error
    | Invalid_field_in_struct -> Error
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
    | Applying_nonfunction_nontype _ -> Error
    | Wrong_number_of_arguments_to_constructor _ -> Error
    | Unimplemented _ -> Error
    | Matching_datatype_has_degeneracy -> Error
    | Invalid_match_index -> Error
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
    | Constant_already_defined _ -> Error
    | Invalid_constant_name _ -> Error
    | Constant_assumed _ -> Info
    | Constant_defined _ -> Info
    | Show _ -> Info

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
    | No_relative_precedence _ -> "E0206"
    | Duplicate_field_in_struct _ -> "E0207"
    | Invalid_field_in_struct -> "E0208"
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
    | Instantiating_zero_dimensional_type -> "E0505"
    | Invalid_variable_face _ -> "E0506"
    (* Degeneracies *)
    | Missing_argument_of_degeneracy _ -> "E0600"
    | Low_dimensional_argument_of_degeneracy _ -> "E0601"
    (* Function-types *)
    | Checking_lambda_at_nonfunction -> "E0700"
    | Applying_nonfunction_nontype _ -> "E0701"
    (* Record fields *)
    | No_such_field _ -> "E0800"
    (* Structs *)
    | Checking_struct_at_nonrecord _ -> "E0900"
    | Checking_struct_at_degenerated_record _ -> "E0901"
    | Missing_field_in_struct _ -> "E0902"
    (* Datatype constructors *)
    | No_such_constructor _ -> "E1000"
    | Wrong_number_of_arguments_to_constructor _ -> "E1001"
    | Missing_instantiation_constructor _ -> "E1002"
    | Unequal_indices -> "E1003"
    (* Matches *)
    (* - Match variable *)
    | Unnamed_variable_in_match -> "E1100"
    | Matching_on_let_bound_variable _ -> "E1101"
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
    (* Commands *)
    | Constant_already_defined _ -> "E1400"
    | Invalid_constant_name _ -> "E1401"
    (* Information *)
    | Constant_assumed _ -> "I0000"
    | Constant_defined _ -> "I0001"
    (* Debugging *)
    | Show _ -> "I9999"

  let default_text : t -> text = function
    | Parse_error -> text "parse error"
    | Parsing_ambiguity str -> textf "potential parsing ambiguity: %s" str
    | Invalid_variable str -> textf "invalid local variable name: %s" (String.concat "." str)
    | Invalid_field str -> textf "invalid field name: %s" str
    | Invalid_constr str -> textf "invalid constructor name: %s" str
    | Invalid_numeral str -> textf "invalid numeral: %s" str
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
    | Instantiating_zero_dimensional_type -> text "can't apply/instantiate a zero-dimensional type"
    | Unequal_synthesized_type (sty, cty) ->
        textf "@[<hv 0>term synthesized type@;<1 2>%a@ but is being checked against type@;<1 2>%a@]"
          pp_printable sty pp_printable cty
    | Checking_struct_at_degenerated_record r ->
        textf "can't check a struct against a record %s with a nonidentity degeneracy applied"
          (name_of r)
    | Missing_field_in_struct f -> textf "record field %s missing in struct" (Field.to_string f)
    | Invalid_field_in_struct -> text "invalid field in struct"
    | Duplicate_field_in_struct f ->
        textf "record field %s appears more than once in struct" (Field.to_string f)
    | Missing_constructor_in_match c ->
        textf "missing match clause for constructor %s" (Constr.to_string c)
    | Unnamed_variable_in_match -> text "unnamed match variable"
    | Checking_lambda_at_nonfunction -> text "checking abstraction against non-function type"
    | Checking_struct_at_nonrecord ty ->
        textf "@[<hov 2>checking struct against non-record type@ %a@]" pp_printable ty
    | No_such_constructor (d, c) -> (
        match d with
        | Some d ->
            textf "canonical type %s has no constructor named %s" (name_of d) (Constr.to_string c)
        | None -> textf "non-datatype has no constructor named %s" (Constr.to_string c))
    | Wrong_number_of_arguments_to_constructor (c, n) ->
        if n > 0 then textf "too many arguments to constructor %s (%d extra)" (Constr.to_string c) n
        else
          textf "not enough arguments to constructor %s (need %d more)" (Constr.to_string c) (abs n)
    | No_such_field (d, f) -> (
        match d with
        | Some d -> textf "record %s has no field named %s" (name_of d) (Field.to_string f)
        | None -> textf "non-record type has no field named %s" (Field.to_string f))
    | Missing_instantiation_constructor (exp, got) ->
        textf
          "instantiation arguments of datatype must be matching constructors: expected %s got %s"
          (Constr.to_string exp)
          (match got with
          | None -> "non-constructor"
          | Some c -> Constr.to_string c)
    | Unequal_indices ->
        text "indices of constructor application don't match those of datatype instance"
    | Unbound_variable c -> textf "unbound variable: %s" c
    | Undefined_constant c -> textf "undefined constant: %s" (name_of c)
    | Nonsynthesizing pos -> textf "non-synthesizing term in synthesizing position (%s)" pos
    | Low_dimensional_argument_of_degeneracy (deg, dim) ->
        textf "argument of %s must be at least %d-dimensional" deg (to_int dim)
    | Missing_argument_of_degeneracy deg -> textf "missing argument for degeneracy %s" deg
    | Applying_nonfunction_nontype (tm, ty) ->
        textf
          "@[<hv 0>attempt to apply/instantiate@;<1 2>%a@ of type@;<1 2>%a@ which is not a function-type or universe@]"
          pp_printable tm pp_printable ty
    | Unimplemented str -> textf "%s not yet implemented" str
    | Matching_datatype_has_degeneracy ->
        text "can't match on element of a datatype with degeneracy applied"
    | Invalid_match_index ->
        text "indices of a match variable must be distinct free variables without degeneracies"
    | Wrong_number_of_arguments_to_pattern (c, n) ->
        if n > 0 then
          textf "too many arguments to constructor %s in match pattern (%d extra)"
            (Constr.to_string c) n
        else
          textf "not enough arguments to constructor %s in match pattern (need %d more)"
            (Constr.to_string c) (abs n)
    | No_such_constructor_in_match (d, c) ->
        textf "datatype %s being matched against has no constructor %s" (name_of d)
          (Constr.to_string c)
    | Duplicate_constructor_in_match c ->
        textf "constructor %s appears twice in match" (Constr.to_string c)
    | Index_variable_in_index_value -> text "free index variable occurs in inferred index value"
    | Matching_on_nondatatype c -> (
        match c with
        | Some c -> textf "can't match on variable belonging to non-datatype %s" (name_of c)
        | None -> text "can't match on variable belonging to non-datatype")
    | Matching_on_let_bound_variable name ->
        textf "can't match on let-bound variable %s" (String.concat "." name)
    | Dimension_mismatch (op, a, b) ->
        textf "dimension mismatch in %s (%d ≠ %d)" op (to_int a) (to_int b)
    | Unsupported_numeral n -> textf "unsupported numeral: %a" Q.pp_print n
    | Anomaly str -> textf "anomaly: %s" str
    | No_such_level (names, i) ->
        textf "@[<hov 2>no level variable@ (%d,%d)@ in context@ %a@]" (fst i) (snd i) pp_printable
          names
    | Constant_already_defined parts ->
        textf "constant already defined: %s" (String.concat "." parts)
    | Invalid_constant_name str -> textf "invalid constant name: %s" str
    | Constant_assumed name -> textf "Axiom %s assumed" (String.concat "." name)
    | Constant_defined name -> textf "Constant %s defined" (String.concat "." name)
    | Show (str, x) -> textf "%s: %a" str pp_printable x
end

include Asai.StructuredReporter.Make (Code)
