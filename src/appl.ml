(* This module should not be opened, but used qualified. *)

(* General type-level functions, implemented relationally.  A type 'f (usually a dummy unit) can be declared to "be" a function on types by adding a constructor to Appl.y: an element of ('f, 'a, 'fa) Appl.y asserts that the function 'f applied to the type 'a yields the type 'fa. *)

type (_, _, _) y = ..

(* An element of ('f, 'a) Appl.ied is an element of 'fa, where 'fa is the value of 'f applied to 'a. *)

type (_, _) ied = Applied : ('f, 'a, 'fa) y * 'fa -> ('f, 'a) ied

(* Constant functions.  Each type 'a Appl.icant "is" a function on types that is constant at the type 'a. *)

type 'a icant = Dummy_icant
type (_, _, _) y += Icantf : ('a icant, 'b, 'a) y
