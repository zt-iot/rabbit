# ProVerif verification tests

These tests compile each Rabbit input to a temporary ProVerif program, run the
vendored ProVerif implementation, and compare the normalized query results
with the `(* PROVERIF EXPECTED ... *)` block immediately before each Rabbit
lemma.

The suite includes verification inputs and expected rejection inputs. Files named `*_unsupported.rab` document language features
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

Global fact regressions include shared state across replicated processes,
patterns, mixed guards, loops, and syscalls.
`test_global_fact_shape` additionally checks the shared private declaration,
parallel output continuations, and exact output/input counts without replication
in `global_facts_linear.rab`. The corresponding single-use query remains
`unknown` under ProVerif's Horn approximation; this is not a proof of reuse.

Local fact regressions reproduce #31 and check isolation between process
instances, inherited storage across nested local functions and syscalls,
`assume`, mixed guards, patterns, and loops. `test_local_fact_shape` checks
process-entry channel restrictions and exact occurrence counts. The single-use query in
`local_facts_linear.rab` records ProVerif's `unknown` approximation result.

Persistent fact regressions follow the [table translation](../../proverif_persistent_facts.md):

- `global_persistent_{put,guard}.rab` and `local_persistent_{put,guard}.rab`
  check continuations, repeated reads, fresh bindings, missing values, and
  global sharing versus local isolation. These replace the old unsupported tests.
- `persistent_matching.rab` and `test_persistent_matching` check fixed values,
  repeated variables, tuples, and references to later arguments. AST checks
  ensure constraints are evaluated inside `get`, before choosing a row.
- `persistent_channel_put.rab`, `persistent_channel_put_no_access.rab`, and
  `persistent_channel_get.rab` check access control, channel/index isolation,
  repeated reads, parameter binding, wildcards, and loops.
- `test_persistent_local_scope` uses `persistent_local_scope/scope.rab` to check
  fresh process-entry identities and their sharing across nested calls/syscalls.

Equality and inequality comparisons are allowed only in guards. The
`equality_query.rab`, `inequality_query.rab`, and `equational_fact_events.rab`
regressions use guard comparisons followed by ordinary event tags to check
reachability, correspondence, and continuation behavior. The separate
`equality_*_unsupported.rab` and `inequality_*_unsupported.rab` fixtures check
that comparisons outside guards are rejected during type checking.

Reduction regressions cover explicit `reduc` declarations, multiple rules across
loaded files, tuple and constructor results, total rules, and unchanged
`equation` semantics. `reduc_failure.rab` verifies that failed computations do
not continue through unused bindings, discarded values, inlined calls, guards,
asynchronous fact outputs, or process initialization. Conflicting rules and
destructors in queries have expected diagnostic fixtures. AST and invalid-rule
checks are in `test/reduc`.

Loop continuation regressions are described in
[Loop continuations](../../proverif_loop_continuations.md). `camserver_sid.rab`
checks the previously unknown reachability and correspondence queries;
`loop_tail_state.rab` and `test_loop_tail_shape` check state propagation,
exclusive branch selection, access denial, and preserved non-tail ordering.
