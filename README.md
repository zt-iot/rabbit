# Rabbit
Rabbit is a modeling language for verified networked systems, featuring an imperative-style syntax for describing systems and an intuitive assertion language for specifying security properties. This implementation translates Rabbit programs and assertions into Tamarin, a model-checking tool for automatic verification.

## Installing Rabbit via OPAM

We assume that OPAM is installed and the OCaml compiler version is 5.2.1 (or higher). The tested version is 5.2.1.
You can follow [these instructions](https://www.ocaml.org/docs/up-and-running) for installing the OCaml package manager OPAM.

Rabbit is implemented in OCaml and can be built easily using `opam` command. From the repository root, run:

```bash
rm -rf _opam   # clean an older build if exists
opam switch create -y -w . ocaml-base-compiler.5.2.1
```

This installs most dependencies available in OPAM and your system's package manager, builds Rabbit, and places the executable in `_opam/bin`, which is typically included in your shell environment.

## Tamarin
To run the Rabbit produced tamain files, of course, `tamarin-prover` needs to be installed.
To install, using Homebrew would be the easiest:

```bash
brew install tamarin-prover/tap/tamarin-prover
```

More details and other installation options can be found in: [https://tamarin-prover.com/manual/master/book/002_installation.html](https://tamarin-prover.com/manual/master/book/002_installation.html)

### Notes for Ubuntu users 

You have to install `tamarin-prover` and `maude` manually.  (There may be a package for Maude but you should use the latest version.)

* Maude 3.5 can be downloaded from [https://github.com/maude-lang/Maude/releases/tag/Maude3.5](https://github.com/maude-lang/Maude/releases/tag/Maude3.5).  Extract files form a zip and `maude` is the executable.   The other files should be placed in the same directory as `maude`.
* Tamarin-prover can be downloaded from [https://github.com/tamarin-prover/tamarin-prover/releases](https://github.com/tamarin-prover/tamarin-prover/releases).  `tamarin-prover` is the executable.

## Running Rabbit and Tamarin

To generate a Tamarin file from a Rabbit source:

```bash
rabbit examples/camserver.rab -o camserver.rab.spthy
```

This runs Rabbit to read `examples/camserver.rab` and output a Tamarin file `camserver.rab.spthy`, which can then be fed to Tamarin:

```bash
tamarin-prover camserver.rab.spthy --prove=
```
By default, this tries to prove all assertions. To prove a specific lemma, replace the last argument with `--prove=LemmaName`, where `LemmaName` is the name of the security assertion listed in the Rabbit file.

**Note:** the lemma name may change during the Tamarin translation, so it is recommended to check the end of the generated `.spthy` file to confirm the correct name.

Rabbit also accepts optional arguments. To see them, run:
```bash
rabbit --help
```
One particularly useful option is `--svg`, which renders transition graphs using Graphviz.

When the `--svg` option is given with the `-o xxx.spthy` option, the transition graph
is rendered to an SVG file `xxx.spthy.svg`. (With the `--test-new` option, another
graph `xxx.spthy.2.svg` is generated for the new compilation `xxx.spthy.2`.)


## Resources

* **WIP** https://typst.app/project/rpEh0EsfMZuGaVAWyrgS2J
* The compiler pipeline is `pipeline.md` in this directory.

### Related Papers

* Inaba, T., Ishikawa, Y., Igarashi, A., & Sekiyama, T. (2024). _Rabbit: A Language to Model and Verify Data Flow in Networked Systems_. In 2024 International Symposium on Networks, Computers and Communications (ISNCC) (pp. 1-8). IEEE. https://doi.org/10.1109/ISNCC62547.2024.10758938
* Park, S., & Igarashi, A. (2025). _Making Rabbit Run for Security Verification of Networked Systems with Unbounded Loops_. In A. Irfan & D. Kaufmann (Eds.), Proceedings of the 25th Conference on Formal Methods in Computer-Aided Design – FMCAD 2025 (pp. 178–187). TU Wien Academic Press. https://doi.org/10.34727/2025/isbn.978-3-85448-084-6_24

