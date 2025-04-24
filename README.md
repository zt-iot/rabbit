# Rabbit — Artifact Submission

Rabbit is a modeling language for verified networked systems, featuring an imperative-style syntax for describing systems and an intuitive assertion language for specifying security properties. This implementation translates Rabbit programs and assertions into Tamarin, a model-checking software for automatic verification.

This repository contains the source code of Rabbit, along with the examples used in the manuscript, enabling full reproducibility of the results.

We have prepared a Bash script, `evaluate.sh`, which checks for required dependencies, reports any that are missing (with installation instructions), builds Rabbit, and evaluates the example systems.

If the script fails for any reason, we also provide manual instructions below.

## Evaluation Script

To run the script, first make it executable:

```bash
chmod +x evaluate.sh
```

To build Rabbit, run:

```bash
./evaluate.sh build
```

This checks all dependencies and reports any missing ones, including installation instructions. If successful, the Rabbit executable will be placed at `./_build/default/src/rabbit.exe`. 

To evaluate the manuscript's examples, run:

```bash
./evaluate.sh measure all --timeout=n
```

where `n` is a positive integer indicating the timeout in minutes for each verification. The default is `n=60`.

### What the Script Does

The example Rabbit files are:
1. `examples/default.rab` — the default system
2. `examples/parameterized.rab` — the parameterized system

Each is evaluated with the Rabbit executable in three configurations:
1. No optimization
2. With graph compression only
3. With compression and introducing sub-lemmas

The following Tamarin files are generated:
- `output/default.rab.spthy`, `output/parameterized.rab.spthy`
- `output/default.rab.compressed.spthy`, `output/parameterized.rab.compressed.spthy`
- `output/default.rab.compressed.sublemmas.spthy`, `output/parameterized.rab.compressed.sublemmas.spthy`

Each file includes reachability `Reachable` and correspondence `Correspondence` lemmas. The `.sublemmas.spthy` files additionally include _reuse sub-lemmas_.

Tamarin is run on each assertion within the specified timeout. If `n=60`, the process may take up to 14 hours for the 14 assertions in the worst case.

Logs of the script are printed to stdout with timestamps, while detailed logs from the Tamarin prover are saved as:

```
log/[spthyfile].[assertion].log
```

### Comparison with SAPIC+ and ProVerif

The SAPIC+ implementation of the default system is in:

```
examples/default_sapicp.spthy
```

To evaluate it using Tamarin and ProVerif, run:

```bash
./evaluate.sh compare --timeout=n
```

This will:
- Verify each reachability and correspondence assertions using the Tamarin prover
- Translate the file into ProVerif syntax:

```
output/default_sapicp.spthy.[assertion].pv
```

- Run ProVerif on the translated files

Each verification uses the same timeout `n`, so the entire comparison process may take up to 4 hours when `n=60`.

Tamarin and ProVerif's log files will be generated at:
- `log/default_sapicp.spthy.[assertion].log`
- `log/default_sapicp.spthy.[assertion].pv.log`
Abstract logs will be printed to stdout with timestamps.

### Summary

To reproduce the evaluation results from the manuscript, assuming all the dependencies are installed, run:

```bash
chmod +x evaluate.sh
./evaluate.sh build
./evaluate.sh measure all --timeout=60
./evaluate.sh compare --timeout=60
```

This will run **14 + 4 verifications** and may take up to **18 hours** in total.

## Dependencies

We assume a Linux environment with **Homebrew** and **OPAM** installed. See https://brew.sh and https://www.ocaml.org/docs/up-and-running for installation guides. This artifact was tested with OCaml compiler version 5.3.0.

(This can be done by, once installed OPAM:

```bash
opam switch create 5.3.0 ocaml-base-compiler.5.3.0
opam switch set 5.3.0
eval $(opam env)

```
For more details, see https://ocaml.org/docs/install-a-specific-ocaml-compiler-version)

The following OCaml packages are required:
- [Dune](https://dune.build) build system (tested with version 3.16.0)
- [Menhir](http://gallium.inria.fr/~fpottier/menhir/) parser generator (tested with version 20220210)
- OCaml libraries: `menhirLib` (tested with version 20220210), `sedlex` (tested with version 3.1), and ocamlfind

Install them using:

```bash
opam install ocamlfind dune menhir sedlex
```

Rabbit has been tested with Tamarin version 1.10. To install it:

```bash
brew install tamarin-prover/tap/tamarin-prover
```

For more details, see: https://tamarin-prover.com/manual/master/book/002_installation.html

To install ProVerif:

```bash
opam update
opam depext conf-graphviz
opam depext proverif
opam install proverif
```

Our code is tested with ProVerif version 2.05.

See the official instructions: https://bblanche.gitlabpages.inria.fr/proverif/README

The script also requires `timeout`. On Linux, it should be available by default. On macOS, install it via:

```bash
brew install coreutils
```

## Running Rabbit and Tamarin

To compile Rabbit, run:

```bash
dune build
```

This compiles the project and places the executable at `_build/default/src/rabbit.exe`. To run it:

```bash
./_build/default/src/rabbit.exe examples/default.rab -o output/default.rab.spthy
```

This generates a Tamarin file from the Rabbit source.

Optional flags:
- `--post-process` — Enables **Graph Compression**, merging consecutive transitions.
- `--tag-transition` — Enables **Sub-lemma Introduction**, adding reuse lemmas.

Tamarin must be run separately. For example:

```bash
tamarin-prover output/default.rab.spthy --prove=LemmaName
```

Lemma names may be slightly altered during translation. Check the end of the `.spthy` file for the exact lemma names:

For our prepared examples, they are:
```tamarin
// Sub-lemmas (with --tag-transition)
lemma AlwaysStarts__[reuse,use_induction]: ...
lemma AlwaysStartsWhenEnds__[reuse,use_induction]: ...
lemma TransitionOnce__[reuse,use_induction]: ...

// Main assertions
lemma Reachable : ...
lemma Correspondence : ...
```

## Running Tamarin and ProVerif on SAPIC+

SAPIC+ files have the `.spthy` extension and are compatible with `tamarin-prover`:

```bash
tamarin-prover examples/default_sapicp.spthy --prove=Reachable
```

To convert to ProVerif format:

```bash
tamarin-prover examples/default_sapicp.spthy --prove=Reachable -m=proverif > output/default_sapicp.spthy.Reachable.pv
```

Then run:

```bash
proverif output/default_sapicp.spthy.Reachable.pv
```

This attempts to prove all lemmas in the file. In this case, only `Reachable` is present.
