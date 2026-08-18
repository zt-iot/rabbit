# ProVerif verification tests

These tests compile each Rabbit input to a temporary ProVerif program, run the
vendored ProVerif implementation, and compare the normalized query results
with the `(* PROVERIF EXPECTED ... *)` block immediately before each Rabbit
lemma.

The suite currently contains 52 verification inputs and 22 expected
rejection inputs. Files named `*_unsupported.rab` document language features
that the parser, typer, compiler, or ProVerif backend does not yet support;
their `.error` files assert the diagnostic instead of silently skipping them.

Each Rabbit file focuses on one language feature. Each lemma has one adjacent
expected-result block containing `true`, `false`, or `unknown`; the runner
collects those blocks in source order. These values consistently describe the
Rabbit lemma: `true` means that it holds, and `false` means that it does not.
ProVerif reports the raw result of a reachability query with the opposite
polarity, so the runner reverses `true` and `false` for `reachable` lemmas.
`unknown` remains unchanged.

Run the tests with:

```sh
opam exec -- dune runtest examples/proverif_verification
```
