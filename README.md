# Rabbit — Artifact Submission

Rabbit is a modeling language for verified networked systems, featuring an imperative-style syntax for describing systems and an intuitive assertion language for specifying security properties. This implementation translates Rabbit programs and assertions into Tamarin, a model-checking tool for automatic verification.

This repository contains the source code of Rabbit, along with the examples used in the manuscript, enabling full reproducibility of the results.

We provide a Bash script, `evaluate.sh`, which checks for required external dependencies and evaluates the example systems while measuring execution time. The evaluator script store outputs from the tamarin prover in `log/` whose size actually can grow quite huge, to few gigabytes. (We provide a real-time trimmer as well.)

To run our evaluation, Rabbit, the Tamarin prover, and ProVerif need to be installed. See the Installation section if you want to install them manually via OPAM, Homebrew, etc., on your machine.

We have also prepared Docker images for both AMD64 and ARM64 platforms that contain executables for the mentioned software. To install the Docker image, see the Running the Docker Image section.

If the script fails for any reason, manual instructions for running Rabbit and verification are provided below.

## Running the Docker Image

To run our Docker image, Docker must be installed on your machine.  
It can be downloaded from [https://docs.docker.com/get-docker/](https://docs.docker.com/get-docker/).

After installation, check by running:

```bash
docker run hello-world
```

We have prepared two Docker images: one for AMD64 and one for ARM64.  
In the following, we describe usage for AMD64.  
If your machine runs ARM64 architecture, replace `amd64` with `arm64` accordingly.

To load an image, at the directory of this README file, run:

```bash
docker load -i rabbit-artifact-amd64.tar
```

The Docker image provides executables for `rabbit`, `tamarin-prover`, and `proverif`.  
To run them, mount the repository folder (where this README is located) into the container:

```bash
docker run --rm -v $(pwd):/mnt rabbit-artifact:amd64 \
    [command here]
```

Inside the container, `/mnt` corresponds to this repository folder.

For example:

```bash
docker run --rm -v $(pwd):/mnt rabbit-artifact:amd64 \
    rabbit /mnt/examples/default.rab -o /mnt/testout.spthy
```

This reads `./examples/default.rab` and writes `./testout.spthy` into your local folder. 

See the section Running Rabbit and Tamarin Manually to learn more about using Rabbit + Tamarin. To repdocue our evaluation, it is now okay to skip to Evaluation Script section.


## Installation without Docker 

This section is relevant if you decide to install the software without using the Docker images.

We assume that OPAM is installed and the OCaml compiler version is 5.0.0 (or higher). The tested version is 5.0.0.

Rabbit is implemented in OCaml and can be built easily using its `rabbit.opam` file. From the repository root, run:

```bash
opam pin add . -n
opam install . --deps-only
opam install .
```

This installs most dependencies available in OPAM and your system's package manager, builds Rabbit, and places the executable in `~/.opam/[switch]/bin`, which is typically included in your shell environment.

To evaluate Rabbit programs and run experiments, additional dependencies are required.

For macOS, run:

```bash
brew install coreutils graphviz
```

to install:

- `coreutils` provides the `timeout` command.
- `graphviz` is required by ProVerif.

For Linux, `timeout` is usually available by default, and `graphviz` should be installed automatically via OPAM's external dependency configuration. If not, install it manually.

Since Tamarin is not available via OPAM, it must be installed separately. Using Homebrew would be the easiest:

```bash
brew install tamarin-prover/tap/tamarin-prover
```

We have checked that it installs well for macOS with Apple Silicon, but observed that it failed on an Ubuntu ARM64 virtual machine. In that case, consider installing from source. See: [https://tamarin-prover.com/manual/master/book/002_installation.html](https://tamarin-prover.com/manual/master/book/002_installation.html)

## Evaluation Script

To run the script, first make it executable:

```bash
chmod +x evaluate.sh
```

Running:

```bash
./evaluate.sh init
```

checks whether Rabbit and all required tools are available, listing any that are missing. If a Docker image is used, this `init` step can be skipped.

To evaluate the manuscript's examples:

```bash
./evaluate.sh measure all --timeout=n --docker=x
```

where `n` is a positive integer (default: `n=60`) specifying the timeout in minutes for each verification,  
and `x` can be either `none` (for native installation), `amd64` (for the Docker image for AMD64), or `arm64` (for the Docker image for ARM64).  
Its default value is `none`.

The evaluater saves log files in `log/` and it can grow quite huge. Consider running in a separate terminal our trimmer:
```bash
./evaluate.sh trim --size=n --interval=t
```
which watches all files with the `.log` extension in the `log/` directory and trims each log file to `n` megabytes (default: 10) every `t` seconds (default: 60).


### What the Script Does

The example Rabbit files are:

1. `examples/default.rab` — the default system
2. `examples/parameterized.rab` — the parameterized system

Each is evaluated in three configurations:

1. No optimization
2. With graph compression only
3. With compression and introducing sub-lemmas

The script generates the following Tamarin files:

- `output/default.rab.spthy`
- `output/parameterized.rab.spthy`
- `output/default.rab.compressed.spthy`
- `output/parameterized.rab.compressed.spthy`
- `output/default.rab.compressed.sublemmas.spthy`
- `output/parameterized.rab.compressed.sublemmas.spthy`

Each file includes `Reachable` and `Correspondence` lemmas. Sub-lemma files also include reuse sub-lemmas.

The script then runs Tamarin prover on each lemma with the given timeout.  
If `n=60`, the full run may take up to **14 hours** in the worst case.

While running the verifications, the script prints to stdout with timestamps for high-level progress tracking.  
Detailed logs are saved under the `log/` directory, with filenames indicating the corresponding `.spthy` file and lemma.

### Comparison with SAPIC+ and ProVerif

The SAPIC+ version of the default system is located at:

```
examples/default_sapicp.spthy
```

To evaluate it with Tamarin and ProVerif:

```bash
./evaluate.sh compare --timeout=n --docker=x
```

This will:

- Run Tamarin on each lemma.
- Translate it into ProVerif:

```bash
output/default_sapicp.spthy.[assertion].pv
```

- Run ProVerif on the translated files.

Each assertion runs with timeout `n`, so the full comparison may take up to 4 hours for `n=60`.

Detailed logs are saved at:

- `log/default_sapicp.spthy.[assertion].log`
- `log/default_sapicp.spthy.[assertion].pv.log`

### Summary

To fully reproduce the results:

```bash
chmod +x evaluate.sh
./evaluate.sh init
./evaluate.sh measure all --timeout=60 --docker=x
./evaluate.sh compare --timeout=60 --docker=x
```

with `x` being `none`, `amd64`, or `arm64`.

This will run **14 + 4 verifications** and may take up to **18 hours**.

## Running Rabbit and Tamarin Manually

To generate a Tamarin file from a Rabbit source:

```bash
rabbit examples/default.rab -o output/default.rab.spthy

# or:
# docker run --rm -v $(pwd):/mnt rabbit-artifact:amd64 rabbit /mnt/examples/default.rab -o /mnt/output/default.rab.spthy
```

Optional flags:

- `--post-process`: enables graph compression
- `--tag-transition`: introduces sub-lemmas

To run Tamarin manually:

```bash
tamarin-prover output/default.rab.spthy --prove=LemmaName

# or:
# docker run --rm -v $(pwd):/mnt rabbit-artifact:amd64 tamarin-prover /mnt/output/default.rab.spthy --prove=LemmaName
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

# or:
# docker run --rm -v $(pwd):/mnt rabbit-artifact:amd64 tamarin-prover /mnt/examples/default_sapicp.spthy --prove=Reachable
```

To convert to ProVerif:

```bash
tamarin-prover examples/default_sapicp.spthy --prove=Reachable -m=proverif > output/default_sapicp.spthy.Reachable.pv
proverif output/default_sapicp.spthy.Reachable.pv

# or:
# docker run --rm -v $(pwd):/mnt rabbit-artifact:amd64 tamarin-prover /mnt/examples/default_sapicp.spthy --prove=Reachable -m=proverif > /mnt/output/default_sapicp.spthy.Reachable.pv
# docker run --rm -v $(pwd):/mnt rabbit-artifact:amd64 proverif /mnt/output/default_sapicp.spthy.Reachable.pv
```

This attempts to prove all lemmas. In this example, only `Reachable` is present.

