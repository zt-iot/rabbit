# Persistent fact translation

Status: implemented for global, process-local, and channel persistent fact
production and guards. This document specifies the table encoding proposed
in [#28](https://github.com/zt-iot/rabbit/issues/28#issuecomment-5710564933).
Fact storage is separate from tags/events and attacker `In`/`Out` operations.

## Store and scope

All persistent facts use one initially empty table:

```proverif
table persistent_fact_table(bitstring).
fun persistent_local_fact(bitstring, bitstring): bitstring [data].
fun persistent_channel_fact(channel, bitstring): bitstring [data].
```

Each fact declaration also has a distinct `data` constructor for its payload:
`F__global_fact`, `F__local_fact`, or `F__chan`, with the translated argument
types. Nullary facts use nullary constructors. Wrappers distinguish scopes;
declaration constructors distinguish facts. Tables are internal process
storage, not attacker-accessible communication channels.

| Rabbit fact | Stored value |
| --- | --- |
| `!::F(v)` | `F__global_fact(V)` |
| `!F(v)` | `persistent_local_fact(local_id, F__local_fact(V))` |
| `!ch::F(v)` | `persistent_channel_fact(Ch, F__chan(V))` |

Global entries are shared by all process instances. Local entries use a fresh
`bitstring` identity restricted inside each process definition, fresh on each
invocation (including replicated invocations). The identity is allocated only
when needed and shared across derived environments for local functions,
inlined syscalls, branches, and loops. A process type or user-supplied process
parameter is not an ownership key.

Channel entries use the actual channel identity, including the index of a
channel-family instance. Their lifetime is independent of the producing
process. Two distinct channels or family indices do not share entries.

## Production and access control

Translate a persistent `put` to `insert persistent_fact_table(entry); Continuation`.
Insertions do not wait for a reader and preserve the Rabbit continuation.
Entries remain available after reads. Repeated identical insertions do not
provide a count of consumable occurrences; this agrees with persistent usage.

For channel facts, wrap the insertion and its continuation in the same
`channel_table` and `access_control_table` lookups used for ordinary channel
facts. Access depends on the current process type, target channel type, and
current syscall. Failed access takes the existing failure continuation (`0`
for `put`). Indexed channels use the family for the access check and the
specific instance for the stored key. Global/local facts need no channel
access check.

Multiple insertions are sequential, not an atomic transaction. Earlier
insertions are not rolled back if a later operation fails.

## Lookup and matching

Translate guards to `get persistent_fact_table(pattern) suchthat condition in
Success else Failure`. A successful lookup does not consume an entry, so the
same entry can satisfy repeated guards, including within the same guard list.
Failure uses the surrounding control-flow failure continuation; bindings from
a failed lookup do not escape.

For example, with an already bound `image`:

```proverif
get persistent_fact_table(Signed__global_fact(value:bitstring))
  suchthat value = image in
  Success
else
  Failure
```

The equality is part of row selection, equivalent for this purpose to the
proposal's `Signed__global_fact(=image)` pattern. Do not select an arbitrary
row first and test its fixed arguments in a subsequent process `if`.

Unbound argument variables bind values in the successful branch; wildcards
bind independent unused variables. Tuple structure is matched directly in
the table pattern. Fixed leaves, repeated variables, and function expressions
whose operands are available become equality conditions joined by `&&` in
`suchthat`. Bind all arguments before compiling these conditions so that
patterns such as `F(f(x), x)` can reference a later argument. Use actual
translated types, not universally `bitstring`. Arbitrary function inversion
and existing unsupported wildcard/function patterns are not added.

Local lookup equality-matches the invocation identity in the wrapper.
Channel lookup equality-matches the channel and is surrounded by the same
access checks as channel production. For a family with an unbound or wildcard
index, lookup binds a candidate channel, checks its family using the generated
projection in `suchthat`, and makes its index projection available to the
successful branch when the index has a name.

`case`, `assume`, `repeat`, and `until` use these lookups. Persistent channel
guards must not enter the ordinary consuming-channel input optimization.

## Boundaries and analysis assumptions

This is a storage encoding, not a new event encoding. Persistent uses in
`event` commands are not supported by this translation.

Multiple facts and mixed guards still use sequential guard compilation.
Conditions depending on bindings from later facts remain deferred until
those bindings exist. Separate explicit comparison facts also follow the
existing guard scheduler. This implementation does not combine the whole
guard into one atomic table join or backtrack across all previously chosen
rows. Linear facts in mixed guards can still be consumed before a later
condition fails. The existing [guard](proverif_guard_compilation.md),
[global](proverif_global_facts.md), and [local](proverif_local_facts.md)
analysis assumptions remain applicable; tests do not constitute a proof of
semantic equivalence or preservation of deadlock freedom.

## Validation

See the [verification test guide](examples/proverif_verification/README.md)
for regression filenames. Query tests check repeated reads, sharing and
isolation, access denial, argument binding, channel families, and loops.
Generated-AST tests additionally check local identity scope and constraints
inside table selection, which existential reachability tests alone cannot
establish.
