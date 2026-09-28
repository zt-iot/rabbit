# Loop continuations in ProVerif compilation

The Rabbit-to-ProVerif compiler carries an explicit loop continuation while
compiling the tail of each `repeat` and `until` branch. It builds the final PV
AST directly; there is no text rewrite or post-processing based on generated
channel names.

## Final asynchronous output

An ordinary fact output and its continuation are compiled in parallel:

```text
out(ch, message) | continuation
```

When the continuation is the enclosing loop's internal state output, the
compiler instead emits:

```text
out(loop_ch, (done, result, state));
out(ch, message)
```

`done` is false for a repeat branch and true for an until branch. The first
output hands off the state token; it does not wait for the next iteration to
finish. Channel, file, global and local fact outputs already compiled in
parallel are eligible. Public attacker output `::Out` keeps its sequential
encoding. For a multi-fact `put`, only its last fact is adjacent to the loop
continuation; earlier outputs retain their parallel composition.

When explicit `reduc` declarations are present, payload and call-argument
expressions are evaluated before the handoff. A failed reduction blocks both
the pending output or call body and the loop continuation. Argument evaluation
also applies when the callee discards the argument.

Access checks still enclose the state handoff and the pending output. A denied
output must not release the loop token. The payload retains the current
branch's lexical bindings even if another iteration receives the token.

## Tail cases and calls

A case in loop-tail position keeps its private choice token and guard-failure
retry paths. On success, each selected branch invokes the enclosing loop
continuation with its own final environment. It does not emit a completed-case
token and then receive it again at a shared join. This applies both to ordinary
cases and to cases sharing a channel input.

The continuation propagates through scoped bodies and tail assignments calling
inlined syscalls or local functions. Argument scopes and the current syscall
are restored, and return-value assignments are applied, before the loop state
is emitted. Normal/attack call selection remains exclusive; tail calls do not
need a separate return join.

In a sequence, only the final command receives this continuation. Initializer
calls and non-tail cases keep their shared joins and subsequent commands. An
inner loop retains its own exit receiver before invoking its enclosing
continuation. This is deliberately syntactic tail lowering: a trailing `skip`
or pure expression is not erased to expose an earlier asynchronous output.

## Scope of the equivalence argument

The transformation targets compiler-owned private state channels, with a
waiting exit receiver or replicated loop input. Branch selection consumes one
token, successful branches return it once, and retries preserve the original
state. No user event, access check, or state-changing operation is moved across
the continuation. Only an already-parallel final fact output is placed after
the internal handoff.

These conditions motivate the lowering and are covered by regression checks;
they are not a formal proof of equivalence with Rabbit. In particular, this
change does not resolve existing differences in atomic multi-fact consumption
or ProVerif's Horn approximation. It is not a general `P | Q` to `Q; P` rule.

## Verification

`examples/proverif_verification/camserver_sid.rab` reproduces the camserver
path using fresh RPC request IDs. With the previous compiler, both queries
return unknown. The new compiler produces a reachable trace and a
correspondence counterexample. This standalone fixture uses the protocol
without the auxiliary persistent `Signed` fact: the base branch
`proverif-dev-fact-decl` does not support persistent-fact compilation.

`loop_tail_state.rab` covers branch-local value/channel state, return values,
normal/attack calls, non-tail sequencing, nested loops, and denied outputs.
`test_loop_tail_shape` checks direct handoffs, one loop release per successful
case branch, completion flags, retained choice mechanisms and non-tail joins.
The reverse-order reachability conjunction regressions now return true.

`loop_tail_reduc.rab` checks failed arguments, failed repeat/until outputs,
failed tail-case return values, and successful reduced payloads across loop
handoffs. It covers the interaction with explicit reduction lowering.
