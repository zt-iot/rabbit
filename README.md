# Rabbit

An implementation of a to-Tamarin translator for the Rabbit programming language for verified IoT systems.

## Prerequisites

The OCaml implementation of Rabbit was checked to compile with the OCaml compiler version 4.10.2. 
The following libraries are required:
* the [Dune](https://dune.build) build system
* the [Menhir](http://gallium.inria.fr/~fpottier/menhir/) OCaml parser generator
* the Ocaml libraries `menhirLib`, `sedlex` and `xml-light`

You can follow [these instructions](https://www.ocaml.org/docs/up-and-running) for installing OCaml and the OCaml package manager OPAM. Then, the required libraries can be installed with

    opam install dune
    opam install menhir
    opam install sedlex
    opam install xml-light

To run output Tarmain files `.spthy`, of course Tamarin is required. Rabbit implementation aligns with Tamarin version 1.8 and with the  development version 1.9. Follow this [instruction](https://tamarin-prover.com/manual/master/book/002_installation.html) to install Tamarin.

## Compilation

To compile Rabbit, run the following command in this project directory:

    dune build

Dune compiles the program and hides the executable in `_build/default/src/rabbit.exe`, so try running it with

    _build/default/src/rabbit.exe examples/camserver.rab -o _output/camserver.spthy

that outputs a Tamarin file `output/camserver.spthy` that models `examples/camserver.rab`. Having `--dev` option, the output Tamarin file aligns with the development version of Tamarin. 

Running Tamarin is expected to be done separately. An advice is, when a rabbit file becomes a little complicated, verification time of Tamairn tends to vary a lot by the applied [_heuristics_](https://tamarin-prover.com/manual/master/book/011_advanced-features.html). It seems `I` is a good option; E.g. try

    tamarin-prover _output/camserver.spthy --prove=Correspondence --heuristic=I
