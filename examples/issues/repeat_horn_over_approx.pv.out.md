# Why `repeat_horn_over_approx.pv` Is Unknown

## Files

- [Rabbit source](repeat_horn_over_approx.rab)
- [Generated ProVerif model](repeat_horn_over_approx.pv)
- [Verbose ProVerif output](repeat_horn_over_approx.pv.out)

## Expected and observed results

The intended correspondence is:

```text
A(value) ==> P(value)
```

In a concrete execution, one client iteration creates a fresh value `x`, sends
`Req(x)`, receives the server's `Rep(x)`, executes `P(x)`, and then executes
`A(x)`. The server returns exactly the value from its request. The fixture
therefore records the correspondence as verified.

ProVerif reports:

```text
Could not find a trace corresponding to this derivation.
RESULT event(A__event_global(x__6)) ==> event(P__event_global(x__6)) cannot be proved.
```

## Relevant Horn clauses

Clause 30 introduces the client's initial repeat token:

```text
Clause 30:
mess(loop_ch__7[], (false__bool, ()))
```

Clause 31 starts a client iteration and sends its fresh value:

```text
Clause 31: loop(false, r)[sid] -> mess(ch, Req(x[sid]))
```

Clauses 38 and 39 implement the one-shot server and preserve the request value:

```text
Clause 38: mess(ch, Req(v)) -> server_case(false, ())
Clause 39: server_case(false, ()) && mess(ch, Req(v)) -> mess(ch, Rep(v))
```

Clause 32 allows a client iteration to receive a reply while retaining that
iteration's own fresh value in its private case state. Clause 33 then emits:

```text
P(client_fresh);
A(reply_value)
```

The full Clause 33 includes the access-control, loop-token, private case-channel,
and occurrence-event premises shown in the verbose output.

## The spurious cross-iteration derivation

The derivation explicitly assigns different replication sessions to the two
fresh values:

```text
x_    = x__2[..., !1 = @sid]
x__1  = x__2[..., !1 = @sid_1]
```

It then proceeds as follows:

1. Step 1 derives the single initial false token on `loop_ch__7`.
2. Step 4 uses that token in session `@sid` to send `Req(x_)`.
3. Steps 5 and 6 let the server return `Rep(x_)`.
4. Step 7 reuses the same initial loop-token fact in a different client
   session, `@sid_1`. That client session has its own fresh value `x__1`, but it
   receives `Rep(x_)`.
5. Step 8 consequently derives `P(x__1)` followed by `A(x_)`.

This abstract execution appears to violate the correspondence because the
available preceding event is `P(x__1)`, not `P(x_)`.

## Why no concrete trace corresponds to it

The concrete client loop has one linear false token. While one iteration is
waiting for its reply, another iteration cannot consume that same token and
start concurrently. Therefore the reply produced for `Req(x_)` must return to
the active iteration whose local fresh value is also `x_`.

The Horn abstraction does not consume `mess(loop_ch__7[], (false, ()))` when it
uses it. It can therefore instantiate Clause 31 and Clause 32 under different
replication session identifiers while reusing the same control premise. This
separates the request/reply value from the client's stored fresh value, a state
that the concrete sequential loop cannot reach.

ProVerif finds this abstract counterexample to the correspondence, fails to
reconstruct it as an applied-pi trace, and returns `unknown`.

## Root cause

The request/reply channel itself preserves the value correctly. The loss of
precision occurs at the repeat control channel: a single-use loop token is
represented by a persistent Horn premise. Session identifiers identify fresh
names but do not prevent the same token fact from enabling multiple sessions.
