(lang dune 3.15)
(using menhir 2.1)
(version 0.1)
(generate_opam_files true)

(package 
  (name rabbit)
  (synopsis "Rabbit: A modeling and verification framework for networked systems")
  (description "Rabbit is a domain-specific language and toolchain for modeling networked systems and verifying their security properties using the Tamarin and ProVerif backends.")
  (maintainers "sewon@sewonpark.com")
  (authors "Sewon Park")
  (license "MIT")
  (homepage "https://github.com/zt-iot/rabbit")
  (depends
    (ocaml (>= 5.2.1))
    ocamlgraph
    menhir
    menhirLib
    sedlex
    re
    (ppxlib (>= 0.33.0))
  ))
