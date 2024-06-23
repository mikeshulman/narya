(* A version of "option" that takes a type parameter determining whether it has an element or not.  This allows, for instance, the return type of a function to vary predictably depending on whether some argument was supplied. *)

type none = private Dummy_none
type some = private Dummy_some

module Perhaps = struct
  type (_, _) t = None : ('a, none) t | Some : 'a -> ('a, some) t
  type (_, _) not = Not_none : 'a -> ('a, none) not | Not_some : ('a, some) not
end
