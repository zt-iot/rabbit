# Why `repeat_conjunctive_reachability_unknown.pv` Is Unknown

## Files

- [Rabbit source](repeat_conjunctive_reachability_unknown.rab)
- [Generated ProVerif model](repeat_conjunctive_reachability_unknown.pv)
- [Verbose ProVerif output](repeat_conjunctive_reachability_unknown.pv.out)

## Expected and observed results

The Rabbit process executes `A`, emits `Exit`, consumes `Exit` in the `until`
branch, leaves the loop, and then executes `B`; therefore, a concrete trace
containing both `A` and `B` exists. The fixture records this property as
verified.

ProVerif nevertheless reports:

```text
Could not find a trace corresponding to this derivation.
RESULT not (event(B__event_global) && event(A__event_global)) cannot be proved.
```

This is an `unknown` result: ProVerif neither proves that the two events cannot
coexist nor reconstructs a concrete trace containing both events.

## Relevant Horn clauses

The generated loop is controlled by the private channel `loop_ch__2`. Its
initial token becomes the following Horn fact:

```text
Clause 23:
mess(loop_ch__2[], (false__bool, ()))
```

The repeat branch consumes a false token in the process calculus. Its Horn
clauses can derive all of the following from the same `mess` premise:

```text
Clause 24: loop(false, r) -> event(A)
Clause 25: loop(false, r) -> mess(ch, Exit)
Clause 26: loop(false, r) -> loop(false, ())
```

The `until` branch is represented by Clause 27:

```text
Clause 27: mess(ch, Exit) && loop(false, r) -> loop(true, ())
```

Finally, Clause 30 derives `B` from the true token:

```text
Clause 30: loop(true, r) -> event(B)
```

Here `loop(false, r)` and `loop(true, r)` abbreviate the corresponding
`mess(loop_ch__2[], ...)` facts. The access-control and occurrence-event
premises have been omitted from the abbreviated display above; they are
present in the verbose output and are satisfiable in the displayed derivation.

## The spurious derivation

The decisive detail is visible in derivation steps 1, 2, and 6:

1. Step 1 derives the single initial fact
   `mess(loop_ch__2[], (false__bool, ()))`.
2. Step 2 uses that fact at the repeat input (`@occ8`, session `@sid`) and
   derives `A`.
3. Step 5 uses the same repeat input to derive `Exit`.
4. Step 6 reuses the original Step 1 fact at the `until` input (`@occ14`, a
   distinct replicated session `@sid_1`) and combines it with `Exit` to derive
   the true token.
5. Step 7 consumes the abstract true token and derives `B`.

The Horn derivation therefore uses the one initial false token twice. It does
not use the false token returned by Clause 26 to enable the `until` branch.

## Why no concrete trace corresponds to it

An input on a private channel consumes its message in the applied pi calculus.
The concrete process has only one initial false loop token, so that exact token
cannot simultaneously start the repeat branch and the `until` branch.

Horn facts are monotone: using `mess(loop_ch__2[], ...)` as a premise does not
remove it. Consequently, the Horn abstraction admits the double use even
though the concrete process does not. The `@sid` annotations distinguish the
two replicated instances but do not restore linear ownership of the token.

There is a real trace containing `A` and `B`, but the particular short Horn
derivation selected by ProVerif is not that trace. Trace reconstruction fails
on the duplicated loop token, and ProVerif returns `unknown` instead of the
expected positive reachability result.

## Root cause

The root cause is loss of linearity when the repeat control message is
translated to a reusable Horn fact. `[precise]` inputs and occurrence events
record instantiations, but they do not make Horn premises consumable.
