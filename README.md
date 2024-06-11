# Rabbitm

An implementation of a system programming language for verified IoT systems.

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

## Compilation

To compile Rabbit, run the following command in the Rabbitm directory:

    dune build

Dune compiles the program and hides the executable in `_build/default/src/rabbitm.exe`, so try running it with

    _build/default/src/rabbitm.exe examples/verysimple.rab

It currenlty parse the given .rab file and print the processed system into XML to the terminal.

At this moment of development, only the `verysimple.rab` is the working example. Please ignore other files in `examples/`.