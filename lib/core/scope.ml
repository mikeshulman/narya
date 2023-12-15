include Yuujinchou

let find_data trie x =
  Seq.find_map (fun (path, (data, _)) -> if data = x then Some path else None) (Trie.to_seq trie)

module P = struct
  type data = Constant.t
  type tag = unit
  type hook = unit
  type context = unit
end

module S = Scope.Make (P)

let lookup name = Option.map fst (S.resolve name)

let name_of c =
  match find_data (S.get_visible ()) c with
  | Some name -> String.concat "." name
  (* TODO: Better to munge the original name. *)
  | None -> "_UNNAMED_CONSTANT"

(* If we already have a Constant.t, set a name to refer to that constant.  (Used for whitebox testing.) *)
let set name c = S.include_singleton (String.split_on_char '.' name, (c, ()))

(* Create a new Constant.t and define a name to equal it. *)
let define name =
  let c = Constant.make () in
  set name c;
  c

let run = S.run
