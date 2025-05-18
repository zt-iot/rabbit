# Rabbit
Rabbit is a modeling language for verified networked systems, featuring an imperative-style syntax for describing systems and an intuitive assertion language for specifying security properties. This implementation translates Rabbit programs and assertions into Tamarin, a model-checking tool for automatic verification.

## Installing Rabbit via OPAM

We assume that OPAM is installed and the OCaml compiler version is 5.0.0 (or higher). The tested version is 5.0.0.
You can follow [these instructions](https://www.ocaml.org/docs/up-and-running) for installing OCaml and the OCaml package manager OPAM.

Rabbit is implemented in OCaml and can be built easily using its `rabbit.opam` file. From the repository root, run:

```bash
opam pin add . -n
opam install . --deps-only
opam install .
```

This installs most dependencies available in OPAM and your system's package manager, builds Rabbit, and places the executable in `~/.opam/[switch]/bin`, which is typically included in your shell environment.

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
rabbit examples/camserver.rab -o camserver.rab.spthy --post-process --tag-transition
```

Optional flags:

- `--post-process`: enables graph compression, reducing the size of the produced tamarin code significantly 
- `--tag-transition`: introduces sub-lemmas, that will reduce the verification time of main assertions. (The sublemmas are correct up to the correctness of our implementaiton hence do not need to be proved.)

To run Tamarin manually:

```bash
tamarin-prover camserver.rab.spthy --prove=
```
proves all assertions. To prove a specific lemma, replace the last argument to `--prove=LemmaName`.
LemmaName is the name of the security assertion listed in the rabbit file. 
A small caution is that the name may change during the tamarin translation. Hence, it is advised to carefully check the end of the generated `.spthy` file 
to know the correct name. For example:

```tamarin
// Sub-lemmas (with --tag-transition)
lemma AlwaysStarts__[reuse,use_induction]: ...
lemma AlwaysStartsWhenEnds__[reuse,use_induction]: ...
lemma TransitionOnce__[reuse,use_induction]: ...

// Main assertions
lemma Secret_ : ...
```
`_` may have been added to the user-written `Secret`.

## Documentation

**WIP** https://typst.app/project/rpEh0EsfMZuGaVAWyrgS2J
