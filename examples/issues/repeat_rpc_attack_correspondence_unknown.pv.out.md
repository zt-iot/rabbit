# Why `repeat_rpc_attack_correspondence_unknown.pv` Is Unknown

## Files

- [Rabbit source](repeat_rpc_attack_correspondence_unknown.rab)
- [Generated ProVerif model](repeat_rpc_attack_correspondence_unknown.pv)
- [Verbose ProVerif output](repeat_rpc_attack_correspondence_unknown.pv.out)

## Expected and observed results

The correspondence is:

```text
A(value) ==> P(value)
```

Unlike `repeat_horn_over_approx`, this property is actually falsified in the
Rabbit model. The allowed `substitute` attack consumes a transport message but
returns an attacker-supplied value. The receiver can therefore execute `A(y)`
for a value `y` for which the producer did not execute `P(y)`.

ProVerif still does not report a reconstructed attack. It reports:

```text
Could not find a trace corresponding to this derivation.
RESULT event(A__event_global(x__18)) ==> event(P__event_global(x__18)) cannot be proved.
```

Thus the result is `unknown`, even though a real counterexample exists.

## Relevant Horn clauses

There are three independent repeat control channels:

```text
Clause 47: producer loop seed  mess(loop_ch__19[], (false, ()))
Clause 55: signer loop seed    mess(loop_ch__36[], (false, ()))
Clause 62: receiver loop seed  mess(loop_ch__43[], (false, ()))
```

The producer-side path is represented by Clauses 48--52:

```text
Clause 48: producer_loop(false)[sid] -> Sign(x[sid])
Clauses 49--50: receive Signed(proof) and finish the private case
Clause 51: event P(client_fresh); send M(client_fresh)
Clause 52: return a false producer-loop token
```

The signer replies with the received value in Clause 56:

```text
Clause 56: signer_loop(false) && Sign(v) -> Signed(v)
```

The attack branch is captured by Clauses 67--70:

```text
Clause 67: consume M(original) and start the attack-side private case
Clause 68: attacker(y) -> return y from the attacked receive
Clause 69: forward y through the syscall join channel
Clause 70: event A(y)
```

The abbreviated clauses omit table and occurrence-event premises, all of which
are displayed and discharged in the verbose output.

## The candidate derivation selected by ProVerif

The derivation uses multiple replication sessions. The two producer sessions
that matter here are:

```text
x_    = producer fresh value in @sid_1
x__1  = producer fresh value in @sid_2
```

The relevant steps are:

1. Step 5 derives the one initial false producer-loop token.
2. Step 10 uses it in producer session `@sid_2` to send `Sign(x__1)`.
3. Step 11 lets the signer return `Signed(x__1)`.
4. Step 12 reuses the same Step 5 loop-token fact in producer session `@sid_1`.
   That session's local fresh value is `x_`, but it consumes
   `Signed(x__1)`.
5. Steps 13 and 15 complete session `@sid_1`, execute `P(x_)`, and send
   `M(x_)`.
6. Steps 16--20 take the substitute branch, assume attacker knowledge of
   `x__18`, return that value from `receive`, and execute `A(x__18)`.

The Horn goal therefore contains `P(x_)` but concludes `A(x__18)`, with no
requirement that `x_ = x__18`.

## Why that Horn derivation is not a concrete trace

Steps 10 and 12 both consume the same producer-loop seed in the process
calculus, but a private channel message can be consumed only once. The producer
cannot start session `@sid_2`, block waiting for its signature, and then start
session `@sid_1` from the same token. In a concrete run, the active producer
iteration must receive its own progress-enabling reply before it can return the
token and start another iteration.

The Horn abstraction treats the loop seed as a reusable `mess` premise. It can
therefore combine the signature generated for one producer session with the
continuation state of another. This cross-session prefix is the non-executable
part of the displayed derivation. ProVerif's trace reconstruction detects that
the required linear scheduling cannot be realized and fails.

## Why a real attack does not yield `false` here

The substitute branch is not itself spurious: Clauses 67--70 accurately expose
an attacker-controlled return value, and the Rabbit property is falsified. The
problem is that the Horn search reaches the correspondence goal through a
derivation whose earlier producer prefix already duplicated a loop token.

The verbose output demonstrates that this selected Horn derivation cannot be
reconstructed. It does not demonstrate that no concrete attack exists. Since
ProVerif has neither proved the correspondence nor produced a concrete attack
trace from the derivation it found, its final answer is `cannot be proved`,
i.e. `unknown`, rather than `false`.

## Root cause

The attack and syscall lowering make this example closer to the original
camserver scenario, but the loss of precision still begins at repeat lowering.
Each private loop-control message is linear in the generated process and
non-consuming in the Horn abstraction. The attacker branch supplies the real
correspondence violation; reuse of the producer loop seed prevents the
displayed Horn witness from becoming an executable trace.
