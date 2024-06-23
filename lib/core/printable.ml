open Syntax
open Term
open Value
open Reporter

let phead : head -> printable = function
  | Const { name; _ } -> PConstant name
  | Meta { meta; _ } -> PMeta meta
  | _ -> PString "(variable)"

type printable +=
  | PLevel : level -> printable
  | PTerm : ('a, 'b) Ctx.t * ('b, kinetic) term -> printable
  | PVal : ('a, 'b) Ctx.t * kinetic value -> printable
  | PNormal : ('a, 'b) Ctx.t * normal -> printable
  | PUninst : ('a, 'b) Ctx.t * uninst -> printable
