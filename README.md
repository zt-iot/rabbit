# Rabbit

Rabbit is a modeling language for verified networked systems.
It features an imperative-style syntax for describing networked systems and an intuitive assertion language for specifying security properties.
This implementation translates Rabbit programs and assertions into Tamarin, a model-checking tool for automatic verification.

## Prerequisites

This OCaml implementation of Rabbit was checked to compile with the OCaml compiler version 5.3.0. 
The following libraries are required:
* the [Dune](https://dune.build) build system
* the [Menhir](http://gallium.inria.fr/~fpottier/menhir/) OCaml parser generator
* the Ocaml libraries `menhirLib`, `sedlex` and `xml-light`

You can follow [these instructions](https://www.ocaml.org/docs/up-and-running) for installing OCaml and the OCaml package manager OPAM. Then, the required libraries can be installed with

    opam install dune
    opam install menhir
    opam install sedlex
    opam install xml-light

To run output Tarmain files `.spthy`, of course Tamarin is required. Rabbit implementation aligns with Tamarin version 1.8 and with the development version 1.9. Follow this [instruction](https://tamarin-prover.com/manual/master/book/002_installation.html) to install Tamarin.

## Compilation

To compile Rabbit, run the following command in this project directory:

    dune build

Dune compiles the program and hides the executable in `_build/default/src/rabbit.exe`, so try running it with

    _build/default/src/rabbit.exe examples/camserver.rab -o _output/camserver.spthy

that outputs a Tamarin file `output/camserver.spthy` that models `examples/camserver.rab`. 

Consider passing the following optional arguments:

-  `--dev` : The output Tamarin file aligns with the development version of Tamarin. 
-  `--post-process` : The output Tamarin file gets optimized. Consecutive transitions get merged, under some conditions.
-  `--tag-transition` : Some _reuse_-lemmas are added. They state each transition happnes at most once, up to loop counters. They must hold assuming the correctness of the implementation and are expected to reduce the search space of the main lemmas.


Running Tamarin is expected to be done separately. An advice is, when a rabbit file becomes a little complicated, verification time of Tamairn tends to vary a lot by the applied [_heuristics_](https://tamarin-prover.com/manual/master/book/011_advanced-features.html). It seems `I` is a good option; E.g. try

    tamarin-prover _output/camserver.spthy --prove=Correspondence --heuristic=I

However, there is also an danger that choosing a heuristic actually increases the run-time.

## Tutorial

**Outdated** Find a tutorial on how to program in Rabbit [here](https://hackmd.io/@VcOgfdUPTgqt1HEQTKaaqw/BkOXorVzkl).
