open Util
open Dim
open Core
open Parser
open Notations
open Compile
open Raw
open Term

let sigma = Constant.make ()
let fst = Field.intern "fst"
let snd = Field.intern "snd"
let pair = Constant.make ()

open Monad.Ops (Monad.Maybe)

let sigman =
  make ~name:"sig" ~tightness:10. ~left:Closed ~right:Open ~assoc:Right ~tree:(fun n ->
      eop LParen (name (op Colon (term RParen (ops [ (Name "×", Done n); (Op "><", Done n) ])))))

let () =
  add_compiler sigman
    {
      compile =
        (fun ctx obs ->
          let x, obs = get_name obs in
          let tm, obs = get_term obs in
          let ty, obs = get_term obs in
          let () = get_done obs in
          let tm = compile ctx tm in
          let ty = compile (Snoc (ctx, x)) ty in
          Synth (App (App (Const sigma, tm), Lam ty)));
    }

let prodn =
  make ~name:"><" ~tightness:10. ~left:Open ~right:Open ~assoc:Right ~tree:(fun n ->
      eops [ (Name "×", Done n); (Op "><", Done n) ])

let () =
  add_compiler prodn
    {
      compile =
        (fun ctx obs ->
          let tm, obs = get_term obs in
          let ty, obs = get_term obs in
          let () = get_done obs in
          let tm = compile ctx tm in
          let ty = compile (Snoc (ctx, None)) ty in
          Synth (App (App (Const sigma, tm), Lam ty)));
    }

let comma =
  make ~name:"," ~tightness:10. ~left:Open ~right:Open ~assoc:Right ~tree:(fun n ->
      eop (Op ",") (Done n))

let () =
  add_compiler comma
    {
      compile =
        (fun ctx obs ->
          let x, obs = get_term obs in
          let y, obs = get_term obs in
          let () = get_done obs in
          let x = compile ctx x in
          let y = compile ctx y in
          Raw.Struct (Field.Map.of_list [ (fst, [ x ]); (snd, [ y ]) ]));
    }

let install_notations () =
  Builtins.builtins := !Builtins.builtins |> State.add sigman |> State.add prodn |> State.add comma

let install () =
  install_notations ();
  Scope.set "Σ" sigma;
  Scope.set "pair" pair;
  Hashtbl.add Global.types sigma (pi (UU D.zero) (pi (pi (Var Top) (UU D.zero)) (UU D.zero)));
  Hashtbl.add Global.types pair
    (pi (UU D.zero)
       (pi (pi (Var Top) (UU D.zero))
          (pi (Var (Pop Top))
             (pi (app (Var (Pop Top)) (Var Top))
                (app (app (Const sigma) (Var (Pop (Pop (Pop Top))))) (Var (Pop (Pop Top))))))));
  Hashtbl.add Global.constants sigma
    (Record
       {
         eta = true;
         params = N.two;
         dim = D.zero;
         dim_faces = faces_zero;
         params_plus = Suc Zero;
         fields = [ (fst, Var (Pop (Pop Top))); (snd, app (Var (Pop Top)) (Field (Var Top, fst))) ];
       });
  Hashtbl.add Global.constants pair
    (Defined
       (ref
          (Case.Lam
             ( faces_zero,
               Suc Zero,
               ref
                 (Case.Lam
                    ( faces_zero,
                      Suc Zero,
                      ref
                        (Case.Lam
                           ( faces_zero,
                             Suc Zero,
                             ref
                               (Case.Lam
                                  ( faces_zero,
                                    Suc Zero,
                                    ref
                                      (Case.Leaf
                                         (Struct
                                            (Field.Map.empty
                                            |> Field.Map.add fst (Var (Pop Top))
                                            |> Field.Map.add snd (Var Top)))) )) )) )) ))))
