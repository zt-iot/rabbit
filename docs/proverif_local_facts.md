# Process-local fact translation

This specification addresses [#31](https://github.com/zt-iot/rabbit/issues/31).
It defines a translation for ordinary, non-persistent named facts declared
with `fact local`, represented by `Typed.Plain`. Guards use sequential
consumption, following the channel/file fact approach. The contract preserves
existential reachability and past-event correspondence under the assumption
below; it does not require preservation of deadlock freedom or atomic stores.

Status: implemented for ordinary local fact output and guards, including
`examples/issue20.rab`. Regression tests cover the translation described below.
Local tags (`tag local`, events and queries), global facts, and persistent
facts are outside this ordinary-fact specification. Persistent facts are
implemented as described in the [persistent fact guide](proverif_persistent_facts.md)
for [#28](https://github.com/zt-iot/rabbit/issues/28).

## State and ownership

Each running Rabbit process instance owns an initially empty multiset of
local facts. A fact occurrence consists of its declaration identity and
argument values. Two outputs of `F(v)` create two occurrences, even when
their argument values are equal. A successful guard removes one occurrence;
declarations alone do not create occurrences.

Allocate one fresh private ProVerif channel `local_ch` at the start of each
process instance. Pending outputs on this channel represent its multiset.
The channel is distinct from file channels, user channels, and control-flow
channels. It is never exposed to the attacker or registered in a public
channel/access table. No Rabbit access-policy check is needed to access the
owning process's local facts.

For each local fact declaration `F` with argument types `t1, ..., tn`, emit
a fresh data constructor `F__local_fact(t1, ..., tn): bitstring`. Its name must be
distinct from constructors for other declarations, channel messages and
events. Use the existing value-type translation for arguments. A nullary
fact uses a nullary constructor, written `TEST__local_fact()` below. These
constructors have no equations or reductions. The channel, rather than
constructor secrecy, enforces ownership.

Allocate the channel only in process definitions that use local facts, including
through inlined calls. Put its restriction at process entry, so each invocation
allocates a new channel, including two invocations with identical arguments
or process types. For replicated instances the scope is schematically:

```proverif
!(new local_ch: channel; InstanceBody)
```

It must not be `new local_ch: channel; !InstanceBody`, which would share
facts between instances. A process parameter or process type is not an
ownership key. Conversely, replication introduced solely to implement a
loop does not create a Rabbit process instance and must retain its channel.

Inlined system calls and local function calls inherit the caller's channel.
Returning, branching, looping, and entering a lexical block preserve it.
An independently instantiated Rabbit process always gets a fresh channel.
The channel must remain in the compiler's process environment across these
translations, including calls nested inside calls.

## Production

For ordinary local facts, translate:

```rabbit
put [F(v1, ..., vn)];
continuation
```

as:

```proverif
out(local_ch, F__local_fact(V1, ..., Vn)) | Continuation
```

Here `Vi` is the translated value of `vi` at the output command, and each
output has a terminated continuation. Parallel output allows subsequent
code to execute without waiting for a receiver. Do not use a sequential
output that blocks the continuation, replication of the output, or a
ProVerif table that would make the fact reusable.

A `put` containing several ordinary local facts produces one parallel output
per occurrence alongside the continuation. The owning process has no
concurrent Rabbit command consuming this store, and other instances cannot
access it, so the continuation sees all these outputs as available. When a
command also contains supported channel/file outputs, compose their existing
output translations with these local outputs. Preserve their access checks
and existing restrictions. Ordinary global outputs use the separate shared
store described in the [global fact guide](proverif_global_facts.md); persistent
facts use the [table translation](proverif_persistent_facts.md). Local facts impose no additional
single-fact restriction on `put`.

## Consumption, comparisons, and control flow

For each ordinary local fact in a guard, input one constructor-tagged
message from the owning process's channel. For example:

```rabbit
case [F(x, _)] -> body end
```

has the following schematic translation:

```proverif
in(local_ch, F__local_fact(x:bitstring, ignored:bitstring));
Body
```

Use the actual translated argument types in place of `bitstring`. The
constructor pattern selects the declaration. Each input consumes exactly
one occurrence; two occurrences of `A()` in a guard require two messages.
Selecting among matching messages is nondeterministic. If a required message
is unavailable, the input blocks, possibly after earlier inputs consumed
other facts.

Reuse the existing guard binding and comparison machinery for argument
patterns: distinct variables bind values, wildcards introduce separate unused
variables, and repeated variables or fixed expressions introduce tests.
Tuple decomposition and function expressions follow the supported forms in
[the guard guide](proverif_guard_compilation.md); this specification does not
introduce arbitrary function inversion. Schedule tests after their variables
are bound, and execute the branch body only after every fact and test succeeds.

For example, the guard `[A(x), B(y), x = y]` can be lowered schematically as:

```proverif
in(local_ch, A__local_fact(x:bitstring));
in(local_ch, B__local_fact(y:bitstring));
if x = y then Body else Failure
```

On failure, consumed occurrences need not be restored. `Failure` is the
surrounding control-flow failure continuation: termination for a single case,
or release of the unchanged control state for another guard attempt where
applicable. It must not execute the failed branch body or export its fresh
bindings. Blocking on an input can retain the control token indefinitely.
These are accepted additional stopping paths, under the atomicity assumption
below.

Apply these rules to `case`, `assume`, `repeat`, and `until`. Alternative
branches use nondeterministic selection, with the existing private control
token serializing guard attempts and branch execution for the owning
process. At most one branch body executes for a case selection or loop step.
A successful step passes the resulting state to the continuation; a loop
retains the same local channel. Do not impose source-order priority or select
one branch permanently at compile time: every enabled Rabbit branch and
matching choice must still have a corresponding successful execution.

Local facts may also occur alongside otherwise supported channel/file facts,
comparisons, and access checks. Apply the same sequential guard machinery and
atomicity assumption to the whole guard. Existing independent restrictions
on those forms remain; atomicity alone is not a reason to reject the mixture.

The motivating fragment from `examples/issue20.rab` therefore translates to:

```proverif
new local_ch: channel;
(out(local_ch, TEST__local_fact()) |
 (in(local_ch, TEST__local_fact()); Continuation))
```

This is schematic: declarations and the rest of the process are omitted.
One occurrence is produced and consumed before `Continuation` executes.

## Atomicity assumption

Sequential consumption is not atomic: it may consume some facts before a
later input blocks or a comparison fails, adding deadlock paths. Based on
past discussions, we assume that this atomicity issue does not affect
reachability or correspondence, and apply the same assumption to local facts.
This is an assumption of this specification, not a proof of preservation;
deadlock freedom is not required. Multiple facts, comparisons, and alternative
branches are therefore not rejected solely because consumption is non-atomic.

Persistent local facts use a table keyed by a fresh process-instance identity,
not this consumable store. Their ownership and matching rules are documented
in the [persistent fact guide](proverif_persistent_facts.md).

## Implementation acceptance checks

Regression examples under `examples/proverif_verification/` cover these
implementation obligations:

- The `issue20.rab` production/consumption path reaches its final event.
- A fact's arguments reach the branch body; different declarations do not
  match, and wildcard arguments do not introduce equality constraints.
- One output cannot satisfy two successive guards; two equal outputs can.
- Separate invocations, including replicated instances, cannot consume
  each other's facts. Also inspect the generated restriction scope.
- Local functions and inlined system calls can consume facts produced by
  their caller and leave new facts for it after return.
- Multiple facts, comparisons, repeated variables, and supported tuple
  patterns preserve successful reachability and correspondence examples.
- Alternatives and loops retain valid successful choices even when another
  choice blocks or fails after partial consumption. Failed attempts execute
  no branch-body event and do not leak bindings or duplicate the control token.
- Supported mixed local/channel/file guards and outputs preserve their access
  checks and successful paths, including inside inlined calls.
- Persistent local uses retain their separate non-consuming table translation.
  Unsupported patterns retain the existing guard diagnostics.

Use query checks together with generated-process inspection where the
analyzer's approximation cannot establish exact multiplicity or isolation.
`local_fact_issue31.rab` reproduces the original issue. The isolation, calls,
control-flow, and linear fixtures test the ownership and consumption rules.
`test_local_fact_shape` checks that each used local store is restricted at
process entry, including outside loop replication and around inlined calls.
It also checks exact output/input counts for equal occurrences. The
single-occurrence double-consumption query remains `unknown` under ProVerif
approximation; neither that query nor AST inspection proves the atomicity
assumption.
