# Global fact translation

Status: implemented for ordinary non-persistent global fact output and
guards. This document defines the translation and its analysis assumptions.

The scope is non-persistent facts declared with `fact global`, represented
by `Typed.Global`. Global tags used in events and queries remain separate:
producing a fact does not emit an event, and an event does not populate the
fact store. Persistent facts are outside this specification.

## Shared state and representation

Use one initially empty multiset of ordinary global facts per Rabbit system.
All process instances share it, including replicated instances and instances
with different process types or parameters. Declarations do not create fact
occurrences. Two identical outputs create two independently consumable
occurrences.

Represent this multiset by pending messages on one private ProVerif channel
`global_fact_ch`. Declare it once at top level, outside all process-instance
replications. Process definitions refer to this shared private name. Schematically:

```proverif
free global_fact_ch: channel [private].
(* Process definitions refer to global_fact_ch. *)
process (!Producer | !Consumer)
```

Do not allocate a separate channel inside each process instance: that would
implement local facts. Calls, branches, loops, and inlined syscalls retain
the same shared channel. It is distinct from attacker, user, file, local-fact,
and control-flow channels. Never expose it to the attacker or register it in
public channel/access tables. Ordinary global facts need no channel access
policy check.

For each fact declaration `F` with argument types `t1, ..., tn`, generate a
distinct data constructor `F__global_fact(t1, ..., tn): bitstring`, using
the existing value-type translation. A nullary fact uses a nullary constructor. Generated
names must not collide with other declarations, events, or channel messages.
These constructors have no equations or reductions; channel privacy, rather
than constructor secrecy, protects the store.

## Production

Translate `put [::F(v1, ..., vn)]; continuation` schematically as:

```proverif
out(global_fact_ch, F__global_fact(V1, ..., Vn)) | Continuation
```

Each `Vi` is evaluated using the environment at the output command. The
output process terminates after sending; the Rabbit continuation runs in
parallel so it need not wait for a receiver. Do not replicate the output or
use a reusable table entry for an ordinary fact.

A multi-fact `put` produces one parallel output per occurrence alongside
the continuation. Compose these with other supported output translations,
preserving their existing restrictions and access checks. This is not an
atomic transaction across the shared store; other processes may consume
messages while the producer continues.

## Consumption and control flow

A guard `::F(patterns)` consumes one message matching the declaration's
constructor. For example, `case [::F(x, _)] -> body end` becomes:

```proverif
in(global_fact_ch, F__global_fact(x:bitstring, ignored:bitstring));
Body
```

Use the translated argument types rather than always using `bitstring`.
Matching choices and competition between consumers are nondeterministic.
Each successful input removes one occurrence: one output cannot satisfy
two inputs. An input blocks if no matching occurrence is available.

Reuse the existing guard binding, pattern, comparison, and scheduling rules
in the [guard guide](proverif_guard_compilation.md). Wildcards are distinct
unused variables; repeated variables and fixed expressions introduce the
required tests. This adds no support for arbitrary function inversion.
Run tests only after their dependencies are bound and execute the branch
body only after the complete guard succeeds.

Multiple fact guards use sequential inputs. For example:

```proverif
in(global_fact_ch, A__global_fact(x:bitstring));
in(global_fact_ch, B__global_fact(y:bitstring));
if x = y then Body else Failure
```

Consumed facts need not be restored when a later test fails or input blocks.
Failure uses the existing control-flow failure continuation, executes no
failed branch body, and exports no fresh bindings from that attempt.

Apply this translation in `case`, `assume`, `repeat`, and `until`, using
the existing nondeterministic branch-selection and loop machinery. Process
control tokens remain separate from the shared fact channel; this design
introduces no system-wide lock. Preserve all successful branch and matching
choices rather than imposing source-order priority. Mixed guards with other
supported fact kinds and comparisons use the same machinery and retain
their access checks and independent restrictions.

## Built-ins and persistence

- `::Out(v)` and `::In(pattern)` keep their existing attacker communication
  translation on the public attacker channel. They do not use this store.
- `::True()` and `::False()` keep their existing special guard behavior.
- Global tags in `event` commands and queries keep their event translation.
- Persistent global fact uses are unsupported and must produce a
  source-located diagnostic, not an assertion failure. Consuming a message
  does not implement persistence.

## Atomicity assumption

Rabbit consumes a complete guard atomically. Sequential inputs can consume
some occurrences before a later input blocks or a test fails. With a global
store, this can also affect competing processes. Multiple parallel outputs
likewise do not implement an atomic shared-store update.

Following the agreed channel/local-fact translation policy, this specification
assumes these atomicity differences do not affect existential reachability
or past-event correspondence. This is an explicit analysis assumption, not
a proof of preservation, including for competing global consumers. Deadlock
freedom is not required. Multiple facts, mixed guards, and alternatives are
therefore not rejected solely because the translation is non-atomic.

## Implementation acceptance checks

Regression examples under `examples/proverif_verification/` cover ordinary
global facts and persistent-use diagnostics. Implementation obligations include:

- A producer's fact reaches a consumer in a different process instance,
  including replicated instances and different process types/parameters.
- Fact declarations create no occurrences; different declarations cannot
  match, and arguments and nullary facts are represented correctly.
- One output cannot satisfy two consumers or successive inputs, while two
  identical outputs supply two occurrences.
- A producer continues even when nobody receives its output.
- The attacker cannot inject or consume ordinary global facts; attacker
  `In`/`Out`, special boolean guards, and global tags retain their behavior.
- Multiple facts, comparisons, repeated variables, wildcards, supported tuple
  patterns, alternatives, loops, and inlined calls retain successful paths.
  Failed attempts execute no branch-body event or leak fresh bindings.
- Mixed outputs and guards preserve existing access checks and restrictions.
- Persistent uses produce diagnostics rather than assertion failures.

Use generated-process inspection as well as query checks, especially for
channel scope, multiplicity, privacy, and blocking behavior that ProVerif's
approximation may not establish. These checks do not prove the atomicity
assumption. In particular, `global_facts_linear.rab` records `unknown` for
the query attempting to consume one occurrence twice; the AST regression
checks that the compiler emits one output and two consuming inputs without
replication. The shared and control-flow fixtures cover cross-instance
communication, declaration separation, patterns, correspondence, mixed
channel/global guards, syscalls, alternatives, and loops.
