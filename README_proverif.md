# Rabbit ProVerif compiler

## Compiler documentation

- [Guard compilation](proverif_guard_compilation.md): supported forms, variable bindings, inputs, and the known atomicity limitation.
- [Process-local facts](proverif_local_facts.md): private storage per process instance, including inlined calls, with sequential consumption and an explicit atomicity assumption.
- [Global facts](proverif_global_facts.md): shared private-channel translation for ordinary global facts, with sequential consumption and an explicit atomicity assumption.

## Channel fact events and queries

`event [ch::Observed(x)]` records an event with the channel as its first
argument, followed by the fact arguments. It does not send a channel message;
conversely, `put [ch::Observed(x)]` does not emit an event.

Queries can use channel variables:

```text
reachable ch::Observed(x)
corresponds ch::Received(x) ~> ch::Sent(x)
```

The correspondence requires a preceding `Sent` event on the same channel
with the same value. Parameterized channel instances retain their identity.
Rabbit's typing rules are unchanged: a bare global channel name cannot be
referenced directly in a lemma expression. File fact events and queries remain
unsupported, and multiple facts in one `event [...]` are still emitted
sequentially.

## How to compile

```
dune exec src/rabbit_proverif.exe -- x.rab -o x.pv
```

- `-o` option is omittable.

## How to verify with ProVerif

```
proverif x.pv
```

or

```
proverif \
  -set verboseClauses explained \
  -set removeUselessClausesBeforeDisplay true \
  x.pv
```
