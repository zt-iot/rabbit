# Rabbit ProVerif compiler

## Compiler documentation

- [Persistent facts](proverif_persistent_facts.md): shared table translation for global, process-local, and channel facts, including scope, matching, access control, and analysis limits.
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

## Equality and inequality facts

`=` and `!=` facts are allowed only in `case`/`while` guards. Rabbit rejects
these facts in `put`, `event`, `reachable`, and either side of `corresponds`
during type checking, for both backends. Equational theory declarations are
unaffected.

To observe a successful comparison, declare a normal tag and emit it from a
guard, then query that tag:

```text
tag global [Equal:2]
(* Inside a process: *)
case [x = y] -> event [::Equal(x, y)] end
(* In a lemma: *)
reachable ::Equal(x, y)
```

## How to compile

### Explicit reduction declarations

```text
function enc:2
function dec:2
reduc dec(enc(message, key), key) = message
```

`reduc` defines a directed computation for the function at its left-hand head.
The ProVerif backend emits that function as a destructor, without a separate
`fun` declaration. Rules with the same head are grouped into one `reduc`
declaration, including rules from loaded files. Constructor declarations are
emitted before reduction groups and process definitions.

The head must be a declared function application. Its arguments and result
must contain only variables, constructors (including `constant` declarations
and tuples), and supported literals. Destructors cannot occur inside these
terms, and every result variable must occur in the arguments. Ordinary type
and arity checks also apply. ProVerif checks whether overlapping rules are
deterministic, taking constructor equations into account.

If no rule matches, evaluation fails: a command evaluating that expression
does not continue, even when the result is discarded or unused. A failing
guard does not select its branch. Existing `equation` declarations keep their
previous meaning; they are never inferred to be reductions. Destructors are
rejected in equations and query terms. To query a result, first evaluate it in
the process and record its value in an event.

`reduc` is not supported by the Tamarin backend.

### Command

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
