(* This module should not be opened, but used qualified. *)

(* ******************************
   Fixity and associativity
   ****************************** *)

(* There are four possible fixities: infix, prefix, postfix, and outfix ("closed").  There are also three possible associativities: left, right, and non.  A nonassociative notation can have any fixity, but a left-associative one can only be infix or prefix, and a right-associative one can only be infix or postfix.  Using polymorphic variants allows these types of fixities to "overlap" in a certain sense. *)

type non = [ `Infix | `Prefix | `Postfix | `Outfix ]
type left = [ `Infix | `Postfix ]
type right = [ `Infix | `Prefix ]
