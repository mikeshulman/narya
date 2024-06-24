open Bwd
open Util
open Tbwd
open Dim
open Syntax
open Term
open Value

(* When checking a case tree (a "potential" term), we have to retain some information about the definition being checked.  Specifically, we remember:
   1. The name of the top-level constant being defined.
   2. The arguments that it has been applied to so far at this point in the case tree.  These all start out as variables, but after checking matches some of them get substituted by constructor expressions.
   3. A "hypothesizing" callback that allows us to say "if I were to return such-and-such a term from my current typechecking problem, what would the resulting definition of the top-level constant be?"  This is used when typechecking comatches and codata (and, potentially one day, matches and data as well, such as for HITs) whose later branches depend on the *values* of previous ones.  So as we typecheck the branches of such a thing, we collect a partial definition including all the branches that have been typechecked so far, and temporarily bind the constant to that value while typechecking later branches.  And in order that this is correct, whenever we pass *inside* a case tree construct (lambda, match, or comatch) we wrap the outer callback in an inner one that inserts the correct construct to the hypothesized term.  (It's tempting to think of implementing this with algebraic effects rather than an explicit callback, but I found the purely functional version easier to get correct, even if it does involve passing around more arguments.)

   We parametrize this "status" datatype over the energy of the term (kinetic or potential), since only potential terms have any status to remember.  This implies that status also serves the purpose of recording which kind of term we are checking, so we don't need to pass that around separately. *)
type _ potential_head =
  | Constant : Constant.t -> emp potential_head
  | Meta : ('a, potential) Meta.t * (D.zero, 'a) env -> 'a potential_head

let head_of_potential : type a s. a potential_head -> Value.head = function
  | Constant name -> Const { name; ins = ins_zero D.zero }
  | Meta (meta, env) -> Meta { meta; env; ins = ins_zero D.zero }

type (_, _) status =
  | Kinetic : [ `Let | `Nolet ] -> ('b, kinetic) status
  | Potential :
      'a potential_head * app Bwd.t * (('b, potential) term -> ('a, potential) term)
      -> ('b, potential) status

let energy : type b s. (b, s) status -> s energy = function
  | Kinetic _ -> Kinetic
  | Potential _ -> Potential

let realize : type b s. (b, s) status -> (b, kinetic) term -> (b, s) term =
 fun status tm ->
  match status with
  | Potential _ -> Realize tm
  | Kinetic _ -> tm
