type t = {
  wslparen : Whitespace.t list;
  names : (string option * Whitespace.t list) list;
  wscolon : Whitespace.t list;
  ty : Notation.observation;
  wsrparen : Whitespace.t list;
}
