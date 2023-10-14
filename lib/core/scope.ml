include Yuujinchou

(* To do reverse name lookup for pretty-printing, we hack into Yuujinchou's "hook" mechanism, passing a reference cell to get a return value. *)

let find_data trie x =
  Seq.find_map (fun (path, (data, _)) -> if data = x then Some path else None) (Trie.to_seq trie)

module P = struct
  type data = Constant.t
  type tag = unit
  type hook = GetName of (Constant.t * Trie.path ref)
  type context = unit
end

let hook _context _prefix hook input =
  match hook with
  | P.GetName (x, out) ->
      (match find_data input x with
      | Some name -> out := name
      | None -> ());
      input

module S = Scope.Make (P)

let lookup name = Option.map fst (S.resolve (String.split_on_char '.' name))

let name_of c =
  let name = ref [] in
  S.modify_visible (Language.hook (P.GetName (c, name)));
  String.concat "." !name

(* If we already have a Constant.t, set a name to refer to that constant.  (Used for whitebox testing.) *)
let set name c = S.include_singleton (String.split_on_char '.' name, (c, ()))

(* Create a new Constant.t and define a name to equal it. *)
let define name =
  let c = Constant.make () in
  set name c;
  c

let run = S.run ~hook
