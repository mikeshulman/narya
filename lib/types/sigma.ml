open Util
open Dim
open Core
open Parser
open Notations
open Compile
open Raw
open Term

let ([ sigma; pair ] : (Constant.t, N.two) Vec.t) = Vec.map Constant.intern [ "Σ"; "pair" ]
let ([ fst; snd ] : (Field.t, N.two) Vec.t) = Vec.map Field.intern [ "fst"; "snd" ]

let install () =
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
             (ref
                (Case.Lam
                   (ref
                      (Case.Lam
                         (ref
                            (Case.Lam
                               (ref
                                  (Case.Leaf
                                     (Struct
                                        (Field.Map.empty
                                        |> Field.Map.add fst (Var (Pop Top))
                                        |> Field.Map.add snd (Var Top))))))))))))))

let struc =
  make ~name:"struc" ~tightness:Float.nan ~left:Closed ~right:Closed ~assoc:Non ~tree:(fun n ->
      let rec struc_fields () =
        Inner
          {
            ops = TokMap.singleton RBrace (Done n);
            name =
              Some
                (op Coloneq (terms [ (Op ";", Lazy (lazy (struc_fields ()))); (RBrace, Done n) ]));
            constr = None;
            term = None;
            fail = [];
          } in
      eop LBrace (struc_fields ()))

open Monad.Ops (Monad.Maybe)

let rec compile_struc :
    type n. n check Field.Map.t -> (string option, n) Bwv.t -> observation list -> n check option =
 fun flds ctx obs ->
  match get_next obs with
  | `Done -> return (Raw.Struct flds)
  | `Name (x, obs) ->
      let tm, obs = get_term obs in
      let* tm = compile ctx tm in
      let* x = x in
      compile_struc (flds |> Field.Map.add (Field.intern x) tm) ctx obs
  | `Constr _ | `Term _ -> None

let () = add_compiler struc { compile = (fun ctx obs -> compile_struc Field.Map.empty ctx obs) }

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
          let* tm = compile ctx tm in
          let* ty = compile (Snoc (ctx, x)) ty in
          return (Synth (App (App (Const sigma, tm), Lam ty))));
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
          let* tm = compile ctx tm in
          let* ty = compile (Snoc (ctx, None)) ty in
          return (Synth (App (App (Const sigma, tm), Lam ty))));
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
          let* x = compile ctx x in
          let* y = compile ctx y in
          return (Raw.Struct (Field.Map.of_list [ (fst, x); (snd, y) ])));
    }

let () =
  Builtins.builtins :=
    !Builtins.builtins |> State.add sigman |> State.add prodn |> State.add comma |> State.add struc
