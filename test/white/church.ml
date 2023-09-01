open Core
open Raw

let synth tm = fst (Option.get (Check.synth Ctx.empty tm))
let check tm ty = Option.get (Check.check Ctx.empty tm ty)
let ev tm = Ctx.eval Ctx.empty tm
let app fn arg = Norm.apply fn (Dim.CubeOf.singleton arg)

let equal_at tm1 tm2 ty =
  if Option.is_some (Equal.equal_at Emp tm1 tm2 ty) then () else raise (Failure "Unequal")

let unequal_at tm1 tm2 ty =
  if Option.is_none (Equal.equal_at Emp tm1 tm2 ty) then () else raise (Failure "Equal")

let uu = Synth (Symbol (UU, Zero, Emp))
let raw_nat = Pi (Synth (Pi (uu, uu)), Synth (Pi (uu, uu)))
let nat = ev (synth raw_nat)
let zero = ev (check (Lam (Lam (Synth (Var Top)))) nat)
let one = ev (check (Lam (Lam (Synth (App (Var (Pop Top), Synth (Var Top)))))) nat)

let two =
  ev
    (check
       (Lam (Lam (Synth (App (Var (Pop Top), Synth (App (Var (Pop Top), Synth (Var Top))))))))
       nat)

let three =
  ev
    (check
       (Lam
          (Lam
             (Synth
                (App
                   ( Var (Pop Top),
                     Synth (App (Var (Pop Top), Synth (App (Var (Pop Top), Synth (Var Top))))) )))))
       nat)

let () = equal_at zero zero nat
let () = unequal_at zero one nat
let () = equal_at one one nat
let () = unequal_at one two nat
let () = unequal_at zero two nat
let binop = ev (synth (Pi (Synth raw_nat, Synth (Pi (Synth raw_nat, Synth raw_nat)))))

let plus =
  check
    (Lam
       (Lam
          (Lam
             (Lam
                (Synth
                   (App
                      ( App (Var (Pop (Pop (Pop Top))), Synth (Var (Pop Top))),
                        Synth
                          (App (App (Var (Pop (Pop Top)), Synth (Var (Pop Top))), Synth (Var Top)))
                      )))))))
    binop

let plus = ev plus
let () = equal_at (app (app plus zero) zero) zero nat
let () = equal_at (app (app plus zero) one) one nat
let () = unequal_at (app (app plus zero) zero) one nat
let () = equal_at (app (app plus one) one) two nat
let () = equal_at (app (app plus two) one) three nat
let () = equal_at (app (app plus two) two) (app (app plus one) three) nat
let () = unequal_at (app (app plus two) one) two nat
