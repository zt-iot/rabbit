# Rabbit — Artifact Submission

Rabbit is a modeling language for verified networked systems, featuring an imperative-style syntax for describing systems and an intuitive assertion language for specifying security properties. This implementation translates Rabbit programs and assertions into Tamarin, a model-checking tool for automatic verification.

This repository contains the source code of Rabbit, along with the examples used in the manuscript, enabling full reproducibility of the results.

We provide a Bash script, `evaluate.sh`, which checks for required external dependencies and evaluates the example systems while measuring execution time.

If you are installing Rabbit from source rather than using the Docker image, please begin with the Installation section below, and then run the script.

If the script fails for any reason, manual instructions are provided below.

## Installation

We assume that OPAM is installed and the OCaml compiler version is 5.0.0 (or higher). The tested version is 5.0.0.

Rabbit is implemented in OCaml and can be built easily using its `rabbit.opam` file. From the repository root, run:

```bash
opam pin add . -n
opam install . --deps-only
opam install .
```

It installs most dependencies available in OPAM and your system's package manager, builds Rabbit, and places the executable in `~/.opam/[switch]/bin`, which is typically included in your shell environment.

To evaluate Rabbit programs and run experiments, additional dependencies are required.

For macOS, run:

```bash
brew install coreutils graphviz
```

to install:

- `coreutils` provides the `timeout` command.
- `graphviz` is required by ProVerif.

For Linux, `timeout` is usually available by default and`graphviz` should be installed automatically via OPAM's external dependency configuration. If not, install it manually.

Since Tamarin is not available via OPAM, it must be installed manually. Using homebrew would be the easiest:

```bash
brew install tamarin-prover/tap/tamarin-prover
```

We have checked that it installs well for macos with apple silicon but observed that it failed on the ubuntu ARM64 installed virtual machine. In the case, consider installing from source. See:  [https://tamarin-prover.com/manual/master/book/002\_installation.html](https://tamarin-prover.com/manual/master/book/002_installation.html)

## Evaluation Script

To run the script, first make it executable:

```bash
chmod +x evaluate.sh
```

Running

```
./evaluate.sh init
```

checks whether Rabbit and all required tools are available, listing any that are missing.

To evaluate the manuscript's examples:

```bash
./evaluate.sh measure all --timeout=n
```

Where `n` is a positive integer (default: `n=60`) specifying the timeout in minutes for each verification.

### What the Script Does

The example Rabbit files are:

1. `examples/default.rab` — the default system
2. `examples/parameterized.rab` — the parameterized system

Each is evaluated in three configurations:

1. No optimization
2. With graph compression only
3. With compression and introducing sub-lemmas

The script then generates the following Tamarin files by running `rabbit`:

- `output/default.rab.spthy`
- `output/parameterized.rab.spthy`
- `output/default.rab.compressed.spthy`
- `output/parameterized.rab.compressed.spthy`
- `output/default.rab.compressed.sublemmas.spthy`
- `output/parameterized.rab.compressed.sublemmas.spthy`

Each file includes `Reachable` and `Correspondence` lemmas. Sub-lemma files also include reuse sub-lemmas.

The script then runs Tamarin prover on each lemma with the given timeout. If `n=60`, the full run may take up to \*\*14 hours\*\* in the worst case.

The script, while running the verifications, prints to stdout with timestamps for high-level progress tracking. Detailed logs for each verification are saved under the `log/` directory, with filenames indicating the corresponding `.spthy` file and lemma.

### Comparison with SAPIC+ and ProVerif

The SAPIC+ version of the default system is in:

```
examples/default_sapicp.spthy
```

To evaluate it with Tamarin and ProVerif:

```bash
./evaluate.sh compare --timeout=n
```

This will:

- Run Tamarin on each lemma
- Translate it into ProVerif:

```bash
output/default_sapicp.spthy.[assertion].pv
```

- Run ProVerif on the translated files

Each assertion runs with timeout `n`, so the full comparison may take up to 4 hours for `n=60`.

Detailed logs are saved at:

- `log/default_sapicp.spthy.[assertion].log`
- `log/default_sapicp.spthy.[assertion].pv.log`

### Summary

To fully reproduce the results:

```bash
chmod +x evaluate.sh
./evaluate.sh init
./evaluate.sh measure all --timeout=60
./evaluate.sh compare --timeout=60
```

This will run **14 + 4 verifications** and may take up to **18 hours**.

## Running Rabbit and Tamarin Manually

To generate a Tamarin file from a Rabbit source:

```bash
rabbit examples/default.rab -o output/default.rab.spthy
```

Optional flags:

- `--post-process`: enables graph compression
- `--tag-transition`: introduces sub-lemmas

To run Tamarin manually:

```bash
tamarin-prover output/default.rab.spthy --prove=LemmaName
```

To find lemma names, check the end of the generated `.spthy` file. For example:

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

SAPIC+ files use `.spthy` and can be run directly with Tamarin:

```bash
tamarin-prover examples/default_sapicp.spthy --prove=Reachable
```

To convert to ProVerif:

```bash
tamarin-prover examples/default_sapicp.spthy --prove=Reachable -m=proverif > output/default_sapicp.spthy.Reachable.pv
proverif output/default_sapicp.spthy.Reachable.pv
```

This attempts to prove all lemmas. In this example, only `Reachable` is present.

