(lang dune 3.11)
(package
  (name narya)
  (depends
    (ocaml
      (>= 5.2.1))
    dune
    zarith
    uuseg
    bwd
    algaeff
    asai
    yuujinchou
    react
    lwt
    lambda-term
    fmlib
    fileutils))
(generate_opam_files)
