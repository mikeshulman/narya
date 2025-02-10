open Util
open Term
open Value
open Reporter

let phead : head -> printable = function
  | Const { name; _ } -> PConstant name
  | Meta { meta; _ } -> PMeta meta
  | _ -> PString "(variable)"

type printable +=
  | PLevel : level -> printable
  | PTerm : ('a, 'b) Ctx.t * ('b, 's) term -> printable
  | PVal : ('a, 'b) Ctx.t * kinetic value -> printable
  | PNormal : ('a, 'b) Ctx.t * normal -> printable
  | PUninst : ('a, 'b) Ctx.t * uninst -> printable
  | (* When printing a hole we use a termctx, since that's what we store anyway, and we would also have to read back a value context anyway in order to unparse it. *)
      PHole :
      (string option, 'a) Bwv.t * ('a, 'b) termctx * ('b, kinetic) term
      -> printable
