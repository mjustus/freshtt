(lang dune 1.11)
(name freshtt)
(source (github mjustus/freshtt))
(license BSD-3-clause)

(generate_opam_files true)

(package
 (name freshtt)
 (synopsis "Type checker for MLTT with atomic names")
 (depends
  (sedlex (>= 2.0))
  (menhir (>= 20181113))
  pprint
  cmdliner
  prelude)
)
(using menhir 2.0)

