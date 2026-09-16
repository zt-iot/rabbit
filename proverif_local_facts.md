# Process-local fact translation

This specification addresses [#31](https://github.com/zt-iot/rabbit/issues/31).
It defines an initial translation for ordinary, non-persistent named facts
declared with `fact local`, represented by `Typed.Plain`. It deliberately
limits accepted guards to those for which one input implements the complete
fact-consuming transition. Extending this subset requires an atomic guard
encoding; sequential inputs alone are not such an extension.

Status: specification for subsequent implementation. The current compiler
rejects local fact output and guards, including `examples/issue20.rab`.
The rules below do not describe features already available in the compiler.
Local tags (`tag local`, events and queries), global facts, and persistent
facts are outside this specification. Persistence is tracked in
[#28](https://github.com/zt-iot/rabbit/issues/28).

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
a fresh constructor `local_F(t1, ..., tn): bitstring`. Its name must be
distinct from constructors for other declarations, channel messages and
events. Use the existing value-type translation for arguments. A nullary
fact uses a nullary constructor, written `local_TEST()` below. These
constructors have no equations or reductions. The channel, rather than
constructor secrecy, enforces ownership.

Put channel allocation inside the process definition, so each invocation
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
out(local_ch, local_F(V1, ..., Vn)) | Continuation
```

Here `Vi` is the translated value of `vi` at the output command, and each
output has a terminated continuation. Parallel output allows subsequent
code to execute without waiting for a receiver. Do not use a sequential
output that blocks the continuation, replication of the output, or a
ProVerif table that would make the fact reusable.

A `put` containing only ordinary local facts produces one parallel output
per occurrence alongside the continuation. The owning process has no
concurrent Rabbit command consuming this store, and other instances cannot
access it, so the continuation sees all these outputs as available. This
rule does not authorize mixed local/channel/file/global outputs in one
command; reject such commands until their combined translation is specified.

## Consumption and the initial supported subset

An accepted guard contains exactly one ordinary local fact. Its arguments
must consist only of distinct, previously unbound variables and anonymous
wildcards. Tuple patterns, fixed values, repeated variables, function
patterns, comparisons, and any additional facts are excluded initially.
Each wildcard is translated to a separate unused input variable.

For example:

```rabbit
case [F(x, _)] -> body end
```

has the following schematic translation:

```proverif
in(local_ch, local_F(x:bitstring, ignored:bitstring));
Body
```

Use the actual translated argument types in place of `bitstring`. The
constructor pattern selects the fact declaration without receiving and
discarding messages belonging to other declarations. The input binds the
arguments and consumes exactly one occurrence. No fallible test follows
receipt before entering the branch body. If no matching occurrence exists,
the process blocks and consumes nothing. Selecting among multiple matching
occurrences is nondeterministic.

Initially this rule applies only to a single-branch `case` and a single
`assume` guard with the same supported shape. Reject local facts in
multi-branch `case`, `repeat`, or `until` guards until their choice and loop
encoding is validated with local fact consumption. Local fact production
inside an otherwise supported loop retains the owning instance's channel.

The motivating fragment from `examples/issue20.rab` therefore translates to:

```proverif
new local_ch: channel;
(out(local_ch, local_TEST()) |
 (in(local_ch, local_TEST()); Continuation))
```

This is schematic: declarations and the rest of the process are omitted.
One occurrence is produced and consumed before `Continuation` executes.

## Atomicity and required rejection

Rabbit evaluates a complete guard against the available facts and consumes
its ordinary facts only when the whole guard succeeds. A failed guard
leaves the multiset unchanged. Alternative branches choose one enabled
branch, without consuming facts for losing branches.

The initial subset preserves this property because its sole input is the
complete guard. A conforming implementation must reject the following
forms with a source-located unsupported-feature diagnostic before emitting
a model; it must not silently fall back to general sequential lowering.

| Guard shape | Reason for rejection |
| --- | --- |
| `[A(), B()]` or `[A(), A()]` | Two inputs can consume the first occurrence while the complete guard is disabled. |
| `[F(x), x = a]`, `[F(x), x != a]` | A failed comparison must leave the selected occurrence available. |
| `[F(x, x)]`, `[F(a)]`, or structured arguments | Outside the initial pattern subset; do not implement by consuming then testing. |
| Local facts combined with channel/file/global facts or access checks | The complete transition needs atomic consumption across stores. |
| Multiple alternative branches involving local facts | A blocked or losing branch must not reserve or consume facts needed by another branch. |
| Persistent local facts | Consuming input does not implement persistence. |

Reordering comparisons can simplify some cases, but does not authorize
these forms in the initial subset. A lock only prevents concurrent guard
evaluation; it does not make several inputs atomic or detect that a later
input cannot proceed. Restoring facts after a failed comparison also fails
to address a blocked input or competition between alternatives.

The existing channel/file guard atomicity limitation is therefore not
inherited as an implicit approximation for local facts. Broader support
requires a separate specification of selection, commit, failure and
blocking that preserves all enabled Rabbit transitions. Such support must
also address ProVerif's analysis approximations; the operational encoding
alone does not guarantee that ProVerif proves a query.

## Implementation acceptance checks

The implementation PR must add focused regression examples under
`examples/proverif_verification/`, covering these obligations:

- The `issue20.rab` production/consumption path reaches its final event.
- A fact's arguments reach the branch body; different declarations do not
  match, and wildcard arguments do not introduce equality constraints.
- One output cannot satisfy two successive guards; two equal outputs can.
- Separate invocations, including replicated instances, cannot consume
  each other's facts. Also inspect the generated restriction scope.
- Local functions and inlined system calls can consume facts produced by
  their caller and leave new facts for it after return.
- Every rejected shape above produces a diagnostic, including when hidden
  in a called function or system call. Persistent uses must not assert.

Use query checks together with generated-process inspection where the
analyzer's approximation cannot establish exact multiplicity or isolation.
This specification PR does not change the compiler or claim these checks
already pass.
