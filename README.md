# Rabbit — Artifact Submission

Rabbit is a modeling language for verified networked systems, featuring an imperative-style syntax for describing systems and an intuitive assertion language for specifying security properties. This implementation translates Rabbit programs and assertions into Tamarin, a model-checking tool for automatic verification.

This repository contains the source code of Rabbit, along with the examples used in the manuscript, enabling full reproducibility of the results.

We provide a Bash script, `evaluate.sh`, which checks for required external dependencies and evaluates the example systems while measuring execution time. The evaluator script store outputs from the tamarin prover in `log/` whose size actually can grow quite huge, to few gigabytes. (We provide a real-time trimmer as well.)

To run our evaluation, Rabbit, the Tamarin prover, and ProVerif need to be installed. See the Installation section.

If the script fails for any reason, manual instructions for running Rabbit and verification are provided below.

For reference, the evaluation results of the script are provided at the end of this document.

## Installation

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
./evaluate.sh measure all --timeout=n 
```

where `n` is a positive integer (default: `n=60`) specifying the timeout in minutes for each verification,  

The evaluator saves log files in log/, which can grow quite large as they store all output from the Tamarin prover, while usually only the last part contains the verification results. Consider running our trimmer in a separate terminal:
```bash
./evaluate.sh trim 
```
It will watch all log files in `log/` and trim the last 10 Megabytes.


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
./evaluate.sh compare --timeout=n
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


## Evaluation Results

We ran the evaluations on both an Apple Silicon Mac running macOS and an Intel-based Linux machine.

### On MacOS

We used a 16-inch MacBook Pro (2021) with an Apple M1 Pro chip and 16GB of memory, running macOS Sequoia 15.4.1. Tamarin 1.10.0 and Maude 2.7.1 were installed. The evaluation script produced the following terminal log:
```
[2025-04-29 23:28] [*] Checking for timeout command...
[2025-04-29 23:28] [*] Checking required runtime dependencies...
[2025-04-29 23:28] [*]  - Checking for rabbit executable...
[2025-04-29 23:28] [*]  - Checking for timeout command...
[2025-04-29 23:28] [*]  - Checking for tamarin-prover...
[2025-04-29 23:28] [*]  - Checking for proverif...
[2025-04-29 23:28] [✓] Dependency check completed.
[2025-04-29 23:28] [✓] All required tools are installed.
=== Measuring default.rab with compress:false sub-lemmas:false timeout:60m ===
[2025-04-29 23:28] [*] Running: rabbit examples/default.rab -o output/default.spthy
[2025-04-29 23:28] [*] Verifying Reachable Lemma for (timeout: 60m)
[2025-04-29 23:28] [*] Running: timeout 3600 tamarin-prover output/default.spthy --prove=Reachable &> log/default.spthy.Reachable.log
[2025-04-30 00:28] [✗] Tamarin did not finish within timeout. Process was killed.
[2025-04-30 00:28] [*] Double check the Tamarin output in log/default.spthy.Reachable.log
[2025-04-30 00:28] [*] Verifying Correspondence Lemma for (timeout: 60m)
[2025-04-30 00:28] [*] Running: timeout 3600 tamarin-prover output/default.spthy --prove=Correspondence &> log/default.spthy.Correspondence.log
[2025-04-30 01:28] [✗] Tamarin did not finish within timeout. Process was killed.
[2025-04-30 01:28] [*] Double check the Tamarin output in log/default.spthy.Correspondence.log
=== Measuring default.rab with compress:true sub-lemmas:false timeout:60m ===
[2025-04-30 01:28] [*] Running: rabbit examples/default.rab --post-process -o output/default.compressed.spthy
[2025-04-30 01:28] [*] Verifying Reachable Lemma for (timeout: 60m)
[2025-04-30 01:28] [*] Running: timeout 3600 tamarin-prover output/default.compressed.spthy --prove=Reachable &> log/default.compressed.spthy.Reachable.log
[2025-04-30 01:36] [✓] Tamarin terminated within timeout.
[2025-04-30 01:36] [*] Double check the Tamarin output in log/default.compressed.spthy.Reachable.log
[2025-04-30 01:36] [*] Verifying Correspondence Lemma for (timeout: 60m)
[2025-04-30 01:36] [*] Running: timeout 3600 tamarin-prover output/default.compressed.spthy --prove=Correspondence &> log/default.compressed.spthy.Correspondence.log
./evaluate.sh: line 107: 56304 Killed: 9        $TIMEOUT_CMD “$timeout_seconds” tamarin-prover “${spthy_file}” “--prove=Correspondence” “--quiet” >&“$LOG_FILE2”
[2025-04-30 02:32] [✗] Tamarin did not finish within timeout. Process was killed.
[2025-04-30 02:32] [*] Double check the Tamarin output in log/default.compressed.spthy.Correspondence.log
=== Measuring default.rab with compress:true sub-lemmas:true timeout:60m ===
[2025-04-30 02:32] [*] Running: rabbit examples/default.rab --post-process --tag-transition -o output/default.compressed.sublemmas.spthy
[2025-04-30 02:32] [*] Verifying Reachable Lemma for (timeout: 60m)
[2025-04-30 02:32] [*] Running: timeout 3600 tamarin-prover output/default.compressed.sublemmas.spthy --prove=Reachable &> log/default.compressed.sublemmas.spthy.Reachable.log
[2025-04-30 02:35] [✓] Tamarin terminated within timeout.
[2025-04-30 02:35] [*] Double check the Tamarin output in log/default.compressed.sublemmas.spthy.Reachable.log
[2025-04-30 02:35] [*] Verifying Correspondence Lemma for (timeout: 60m)
[2025-04-30 02:35] [*] Running: timeout 3600 tamarin-prover output/default.compressed.sublemmas.spthy --prove=Correspondence &> log/default.compressed.sublemmas.spthy.Correspondence.log
[2025-04-30 02:46] [✓] Tamarin terminated within timeout.
[2025-04-30 02:46] [*] Double check the Tamarin output in log/default.compressed.sublemmas.spthy.Correspondence.log
[2025-04-30 02:46] [*] Verifying Sub-Lemmas for (timeout: 60m)
[2025-04-30 02:46] [*] Running: timeout 3600 tamarin-prover output/default.compressed.sublemmas.spthy --prove=AlwaysStarts__ --prove=AlwaysStartsWhenEnds__ --prove=TransitionOnce__ &> log/default.compressed.sublemmas.spthy.SubLemmas.log
[2025-04-30 03:09] [✓] Tamarin terminated within timeout.
[2025-04-30 03:09] [*] Double check the Tamarin output in log/default.compressed.sublemmas.spthy.SubLemmas.log
=== Measuring parameterized.rab with compress:false sub-lemmas:false timeout:60m ===
[2025-04-30 03:09] [*] Running: rabbit examples/parameterized.rab -o output/parameterized.spthy
[2025-04-30 03:09] [*] Verifying Reachable Lemma for (timeout: 60m)
[2025-04-30 03:09] [*] Running: timeout 3600 tamarin-prover output/parameterized.spthy --prove=Reachable &> log/parameterized.spthy.Reachable.log
[2025-04-30 04:09] [✗] Tamarin did not finish within timeout. Process was killed.
[2025-04-30 04:09] [*] Double check the Tamarin output in log/parameterized.spthy.Reachable.log
[2025-04-30 04:09] [*] Verifying Correspondence Lemma for (timeout: 60m)
[2025-04-30 04:09] [*] Running: timeout 3600 tamarin-prover output/parameterized.spthy --prove=Correspondence &> log/parameterized.spthy.Correspondence.log
[2025-04-30 05:09] [✗] Tamarin did not finish within timeout. Process was killed.
[2025-04-30 05:09] [*] Double check the Tamarin output in log/parameterized.spthy.Correspondence.log
=== Measuring parameterized.rab with compress:true sub-lemmas:false timeout:60m ===
[2025-04-30 05:09] [*] Running: rabbit examples/parameterized.rab --post-process -o output/parameterized.compressed.spthy
[2025-04-30 05:09] [*] Verifying Reachable Lemma for (timeout: 60m)
[2025-04-30 05:09] [*] Running: timeout 3600 tamarin-prover output/parameterized.compressed.spthy --prove=Reachable &> log/parameterized.compressed.spthy.Reachable.log
./evaluate.sh: line 107: 60889 Killed: 9        $TIMEOUT_CMD “$timeout_seconds” tamarin-prover “${spthy_file}” “--prove=Reachable” “--quiet” >&“$LOG_FILE1"
[2025-04-30 05:44] [✗] Tamarin did not finish within timeout. Process was killed.
[2025-04-30 05:44] [*] Double check the Tamarin output in log/parameterized.compressed.spthy.Reachable.log
[2025-04-30 05:44] [*] Verifying Correspondence Lemma for (timeout: 60m)
[2025-04-30 05:44] [*] Running: timeout 3600 tamarin-prover output/parameterized.compressed.spthy --prove=Correspondence &> log/parameterized.compressed.spthy.Correspondence.log
./evaluate.sh: line 107: 61855 Killed: 9        $TIMEOUT_CMD “$timeout_seconds” tamarin-prover “${spthy_file}” “--prove=Correspondence” “--quiet” >&“$LOG_FILE2”
[2025-04-30 06:12] [✗] Tamarin did not finish within timeout. Process was killed.
[2025-04-30 06:12] [*] Double check the Tamarin output in log/parameterized.compressed.spthy.Correspondence.log
=== Measuring parameterized.rab with compress:true sub-lemmas:true timeout:60m ===
[2025-04-30 06:12] [*] Running: rabbit examples/parameterized.rab --post-process --tag-transition -o output/parameterized.compressed.sublemmas.spthy
[2025-04-30 06:12] [*] Verifying Reachable Lemma for (timeout: 60m)
[2025-04-30 06:12] [*] Running: timeout 3600 tamarin-prover output/parameterized.compressed.sublemmas.spthy --prove=Reachable &> log/parameterized.compressed.sublemmas.spthy.Reachable.log
[2025-04-30 06:13] [✓] Tamarin terminated within timeout.
[2025-04-30 06:13] [*] Double check the Tamarin output in log/parameterized.compressed.sublemmas.spthy.Reachable.log
[2025-04-30 06:13] [*] Verifying Correspondence Lemma for (timeout: 60m)
[2025-04-30 06:13] [*] Running: timeout 3600 tamarin-prover output/parameterized.compressed.sublemmas.spthy --prove=Correspondence &> log/parameterized.compressed.sublemmas.spthy.Correspondence.log
[2025-04-30 07:02] [✓] Tamarin terminated within timeout.
[2025-04-30 07:02] [*] Double check the Tamarin output in log/parameterized.compressed.sublemmas.spthy.Correspondence.log
[2025-04-30 07:02] [*] Verifying Sub-Lemmas for (timeout: 60m)
[2025-04-30 07:02] [*] Running: timeout 3600 tamarin-prover output/parameterized.compressed.sublemmas.spthy --prove=AlwaysStarts__ --prove=AlwaysStartsWhenEnds__ --prove=TransitionOnce__ &> log/parameterized.compressed.sublemmas.spthy.SubLemmas.log
[2025-04-30 07:29] [✓] Tamarin terminated within timeout.
[2025-04-30 07:29] [*] Double check the Tamarin output in log/parameterized.compressed.sublemmas.spthy.SubLemmas.log
```



### On Linux

Although the paper presents results from the MacBook, for reference we also include results obtained from an Intel-based Linux machine.
Since one hour was not enough for some assertions, we ran the tests with `--timeout=120` (2 hours). The results, meaning which assertions were verified and which were not, remained the same.

On a machine with an Intel(R) Core(TM) i9-14900K (24-core CPU, 6GHz) and 64GB of memory, running Ubuntu 24.04.1, with Tamarin 1.10.0 and Maude 3.2 installed, the evaluation script produced the following terminal log:

```
[2025-04-30 12:22] [*] Checking required runtime dependencies...
[2025-04-30 12:22] [*]   - Checking for rabbit executable...
[2025-04-30 12:22] [*]   - Checking for timeout command...
[2025-04-30 12:22] [*]   - Checking for tamarin-prover...
[2025-04-30 12:22] [*]   - Checking for proverif...
[2025-04-30 12:22] [✓] Dependency check completed.
[2025-04-30 12:22] [✓] All required tools are installed.
=== Measuring default.rab with compress:false sub-lemmas:false timeout:120m ===
[2025-04-30 12:22] [*] Running: rabbit examples/default.rab -o output/default.spthy
[2025-04-30 12:22] [*] Verifying Reachable Lemma for (timeout: 120m)
[2025-04-30 12:22] [*] Running: timeout 7200 tamarin-prover output/default.spthy --prove=Reachable &> log/default.spthy.Reachable.log
./evaluate.sh: 106 行: 789745 強制終了            $TIMEOUT_CMD "$timeout_seconds" tamarin-prover "${spthy_file}" "--prove=Reachable" "--quiet" &> "$LOG_FILE1"
[2025-04-30 13:05] [✗] Tamarin did not finish within timeout. Process was killed.
[2025-04-30 13:05] [*] Double check the Tamarin output in log/default.spthy.Reachable.log
[2025-04-30 13:05] [*] Verifying Correspondence Lemma for (timeout: 120m)
[2025-04-30 13:05] [*] Running: timeout 7200 tamarin-prover output/default.spthy --prove=Correspondence &> log/default.spthy.Correspondence.log
./evaluate.sh: 106 行: 792133 強制終了            $TIMEOUT_CMD "$timeout_seconds" tamarin-prover "${spthy_file}" "--prove=Correspondence" "--quiet" &> "$LOG_FILE2"
[2025-04-30 13:50] [✗] Tamarin did not finish within timeout. Process was killed.
[2025-04-30 13:50] [*] Double check the Tamarin output in log/default.spthy.Correspondence.log

=== Measuring default.rab with compress:true sub-lemmas:false timeout:120m ===
[2025-04-30 13:50] [*] Running: rabbit examples/default.rab --post-process -o output/default.compressed.spthy
[2025-04-30 13:50] [*] Verifying Reachable Lemma for (timeout: 120m)
[2025-04-30 13:50] [*] Running: timeout 7200 tamarin-prover output/default.compressed.spthy --prove=Reachable &> log/default.compressed.spthy.Reachable.log
[2025-04-30 13:54] [✓] Tamarin terminated within timeout.
[2025-04-30 13:54] [*] Double check the Tamarin output in log/default.compressed.spthy.Reachable.log
[2025-04-30 13:54] [*] Verifying Correspondence Lemma for (timeout: 120m)
[2025-04-30 13:54] [*] Running: timeout 7200 tamarin-prover output/default.compressed.spthy --prove=Correspondence &> log/default.compressed.spthy.Correspondence.log
./evaluate.sh: 106 行: 793429 強制終了            $TIMEOUT_CMD "$timeout_seconds" tamarin-prover "${spthy_file}" "--prove=Correspondence" "--quiet" &> "$LOG_FILE2"
[2025-04-30 14:05] [✗] Tamarin did not finish within timeout. Process was killed.
[2025-04-30 14:05] [*] Double check the Tamarin output in log/default.compressed.spthy.Correspondence.log

=== Measuring default.rab with compress:true sub-lemmas:true timeout:120m ===
[2025-04-30 14:05] [*] Running: rabbit examples/default.rab --post-process --tag-transition -o output/default.compressed.sublemmas.spthy
[2025-04-30 14:05] [*] Verifying Reachable Lemma for (timeout: 120m)
[2025-04-30 14:05] [*] Running: timeout 7200 tamarin-prover output/default.compressed.sublemmas.spthy --prove=Reachable &> log/default.compressed.sublemmas.spthy.Reachable.log
[2025-04-30 14:14] [✓] Tamarin terminated within timeout.
[2025-04-30 14:14] [*] Double check the Tamarin output in log/default.compressed.sublemmas.spthy.Reachable.log
[2025-04-30 14:14] [*] Verifying Correspondence Lemma for (timeout: 120m)
[2025-04-30 14:14] [*] Running: timeout 7200 tamarin-prover output/default.compressed.sublemmas.spthy --prove=Correspondence &> log/default.compressed.sublemmas.spthy.Correspondence.log
[2025-04-30 14:40] [✓] Tamarin terminated within timeout.
[2025-04-30 14:40] [*] Double check the Tamarin output in log/default.compressed.sublemmas.spthy.Correspondence.log
[2025-04-30 14:40] [*] Verifying Sub-Lemmas for (timeout: 120m)
[2025-04-30 14:40] [*] Running: timeout 7200 tamarin-prover output/default.compressed.sublemmas.spthy --prove=AlwaysStarts__ --prove=AlwaysStartsWhenEnds__ --prove=TransitionOnce__ &> log/default.compressed.sublemmas.spthy.SubLemmas.log
[2025-04-30 15:43] [✓] Tamarin terminated within timeout.
[2025-04-30 15:43] [*] Double check the Tamarin output in log/default.compressed.sublemmas.spthy.SubLemmas.log

=== Measuring parameterized.rab with compress:false sub-lemmas:false timeout:120m ===
[2025-04-30 15:43] [*] Running: rabbit examples/parameterized.rab -o output/parameterized.spthy
[2025-04-30 15:43] [*] Verifying Reachable Lemma for (timeout: 120m)
[2025-04-30 15:43] [*] Running: timeout 7200 tamarin-prover output/parameterized.spthy --prove=Reachable &> log/parameterized.spthy.Reachable.log
./evaluate.sh: 106 行: 795929 強制終了            $TIMEOUT_CMD "$timeout_seconds" tamarin-prover "${spthy_file}" "--prove=Reachable" "--quiet" &> "$LOG_FILE1"
[2025-04-30 16:15] [✗] Tamarin did not finish within timeout. Process was killed.
[2025-04-30 16:15] [*] Double check the Tamarin output in log/parameterized.spthy.Reachable.log
[2025-04-30 16:15] [*] Verifying Correspondence Lemma for (timeout: 120m)
[2025-04-30 16:15] [*] Running: timeout 7200 tamarin-prover output/parameterized.spthy --prove=Correspondence &> log/parameterized.spthy.Correspondence.log
./evaluate.sh: 106 行: 796583 強制終了            $TIMEOUT_CMD "$timeout_seconds" tamarin-prover "${spthy_file}" "--prove=Correspondence" "--quiet" &> "$LOG_FILE2"
[2025-04-30 17:26] [✗] Tamarin did not finish within timeout. Process was killed.
[2025-04-30 17:26] [*] Double check the Tamarin output in log/parameterized.spthy.Correspondence.log

=== Measuring parameterized.rab with compress:true sub-lemmas:false timeout:120m ===
[2025-04-30 17:26] [*] Running: rabbit examples/parameterized.rab --post-process -o output/parameterized.compressed.spthy
[2025-04-30 17:26] [*] Verifying Reachable Lemma for (timeout: 120m)
[2025-04-30 17:26] [*] Running: timeout 7200 tamarin-prover output/parameterized.compressed.spthy --prove=Reachable &> log/parameterized.compressed.spthy.Reachable.log
./evaluate.sh: 106 行: 797803 強制終了            $TIMEOUT_CMD "$timeout_seconds" tamarin-prover "${spthy_file}" "--prove=Reachable" "--quiet" &> "$LOG_FILE1"
[2025-04-30 17:29] [✗] Tamarin did not finish within timeout. Process was killed.
[2025-04-30 17:29] [*] Double check the Tamarin output in log/parameterized.compressed.spthy.Reachable.log
[2025-04-30 17:29] [*] Verifying Correspondence Lemma for (timeout: 120m)
[2025-04-30 17:29] [*] Running: timeout 7200 tamarin-prover output/parameterized.compressed.spthy --prove=Correspondence &> log/parameterized.compressed.spthy.Correspondence.log
./evaluate.sh: 106 行: 797902 強制終了            $TIMEOUT_CMD "$timeout_seconds" tamarin-prover "${spthy_file}" "--prove=Correspondence" "--quiet" &> "$LOG_FILE2"
[2025-04-30 17:32] [✗] Tamarin did not finish within timeout. Process was killed.
[2025-04-30 17:32] [*] Double check the Tamarin output in log/parameterized.compressed.spthy.Correspondence.log

=== Measuring parameterized.rab with compress:true sub-lemmas:true timeout:120m ===
[2025-04-30 17:32] [*] Running: rabbit examples/parameterized.rab --post-process --tag-transition -o output/parameterized.compressed.sublemmas.spthy
[2025-04-30 17:32] [*] Verifying Reachable Lemma for (timeout: 120m)
[2025-04-30 17:32] [*] Running: timeout 7200 tamarin-prover output/parameterized.compressed.sublemmas.spthy --prove=Reachable &> log/parameterized.compressed.sublemmas.spthy.Reachable.log
[2025-04-30 17:33] [✓] Tamarin terminated within timeout.
[2025-04-30 17:33] [*] Double check the Tamarin output in log/parameterized.compressed.sublemmas.spthy.Reachable.log
[2025-04-30 17:33] [*] Verifying Correspondence Lemma for (timeout: 120m)
[2025-04-30 17:33] [*] Running: timeout 7200 tamarin-prover output/parameterized.compressed.sublemmas.spthy --prove=Correspondence &> log/parameterized.compressed.sublemmas.spthy.Correspondence.log
[2025-04-30 18:39] [✓] Tamarin terminated within timeout.
[2025-04-30 18:39] [*] Double check the Tamarin output in log/parameterized.compressed.sublemmas.spthy.Correspondence.log
[2025-04-30 18:39] [*] Verifying Sub-Lemmas for (timeout: 120m)
[2025-04-30 18:39] [*] Running: timeout 7200 tamarin-prover output/parameterized.compressed.sublemmas.spthy --prove=AlwaysStarts__ --prove=AlwaysStartsWhenEnds__ --prove=TransitionOnce__ &> log/parameterized.compressed.sublemmas.spthy.SubLemmas.log
[2025-04-30 20:02] [✓] Tamarin terminated within timeout.
[2025-04-30 20:02] [*] Double check the Tamarin output in log/parameterized.compressed.sublemmas.spthy.SubLemmas.log
```




