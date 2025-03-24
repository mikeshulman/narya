(lang dune 3.11)
(package
  (name narya)
  (depends
    (ocaml
      (>= 5.2.0))
    dune
    zarith
    bwd
    algaeff
    asai
    yuujinchou
    react
    lwt
    lambda-term
    fmlib
    fileutils
    pprint))
(generate_opam_files)
