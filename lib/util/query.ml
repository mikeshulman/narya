(* An effect module that allows the caller to ask a specified kind of question and get a specified kind of answer.  *)

module Make (Q : sig
  type question
  type answer
end) =
struct
  type _ Effect.t += Ask : Q.question -> Q.answer Effect.t

  let ask q = Effect.perform (Ask q)

  let run ~(ask : Q.question -> Q.answer) f =
    let open Effect.Deep in
    try_with f ()
      {
        effc =
          (fun (type a) (eff : a Effect.t) ->
            match eff with
            | Ask q -> Option.some @@ fun (k : (a, _) continuation) -> continue k (ask q)
            | _ -> None);
      }

  let register_printer f =
    Printexc.register_printer @@ function
    | Effect.Unhandled (Ask q) -> f (`Ask q)
    | _ -> None

  let () = register_printer @@ fun _ -> Some "Unhandled Query effect"
end
