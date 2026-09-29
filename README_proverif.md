# Rabbit ProVerif compiler

The Rabbit ProVerif compiler translates Rabbit source files (`.rab`) into
ProVerif models (`.pv`).

## Usage

### ProVerif version

ProVerif 2.05. Install it separately and make `proverif` available on the
`PATH`. Verification tests use this executable as well.

```
% opam exec proverif -- --help
Proverif 2.05. Cryptographic protocol verifier, by Bruno Blanchet, Vincent Cheval, and Marc Sylvestre
  -test 		display a bit more information for debugging
  -in <format> 		choose the input format (horn, horntype, spass, pi, pitype)
  ...
...
```

### Compilation to ProVerif

```sh
dune exec src/rabbit_proverif.exe -- x.rab -o x.pv
```

The `-o` option is optional; by default, the output filename is derived from
the input filename. Run these commands from the repository root.

### Verification with ProVerif

If `proverif` is installed and available on your `PATH`:

```sh
proverif x.pv
```

For more detailed verification output:

```sh
proverif \
  -set verboseClauses explained \
  -set removeUselessClausesBeforeDisplay true \
  x.pv
```

## Tests

```sh
dune runtest
```

At commit `aa7f9e0`, 11 ProVerif verification tests fail because the actual
result is `unknown` where `true` or `false` is expected. See
[Limitations](#limitations) and the [test status report](examples/proverif_test_status.md).

## Rabbit language updates

This branch extends the Rabbit language relative to `main` at commit `3c8598ef`.

### Explicit declaration of facts and tags

Origin: `hasegawa/fact-decl` branch.

Local, global, and channel facts and event tags must be declared before use
with `fact` and `tag`, respectively:

```
fact global [X:0, Y:1]
tag local [PlainEvent:0]
fact local persist [Stored:1]
```

Declare a persistent fact with `persist` and prefix each use with `!`.
For example, with the `Stored` declaration above, a process can execute:

```text
put [!Stored(1)];
case [!Stored(x)] ->
  case [!Stored(x)] -> skip end
end
```

Both guards can match the same stored fact: reading a persistent fact does
not consume it. In contrast, an ordinary fact is consumed when its guard
succeeds. The `persist` declaration and the `!` at each use must agree.

### Assume

Origin: `feat/assumption` branch.

`assume [facts] in body` is shorthand for a single-branch case:

```text
case [facts] -> body end
```

For example, given already bound values `ciphertext` and `key1`:

```text
assume [ciphertext = (_, key1)] in
  skip
```

This continues only if `ciphertext` is a pair whose second component equals
`key1`. The wildcard `_` ignores the first component.

### Reduc declaration

```
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

### Restrictions on facts and tags

- Facts declared by `fact` can only appear in `put` and guards.
- Tags declared by `tag` can only appear in `event` and queries.
- Equality and inequality facts can only appear in guards.
- File facts are only allowed in `put` and guards.

### Static typing for ProVerif compilation

A simple type system provides information needed for ProVerif compilation.
It distinguishes ordinary values, channels, and process/channel-family
parameters. Strings, integers, booleans, tuples, and structures are all ordinary
values; this type system does not distinguish them further.

- The type system is monomorphic.
- No additional type annotations are required.
- The shared type checker also applies these checks to Tamarin compilation.

### Wildcards in guards

The wildcard `_` matches a value without binding a name:

- `case [p = (_, y)] -> ... end`
- `assume [ciphertext = (_, key1)] in ...`

Wildcards inside function applications, such as `pair(_, y)`, are not
supported by the ProVerif backend. Tuple patterns such as `(_, y)` are supported.

## Limitations

The ProVerif translation does not preserve all details of Rabbit execution,
and ProVerif cannot always decide the generated queries.

### Atomicity of facts

The ProVerif translation consumes multiple facts in a guard sequentially,
rather than atomically. Partial consumption can introduce deadlocks that do
not exist in the original Rabbit semantics. The translation assumes that these
differences do not affect reachability or past-event correspondence. This is
an analysis assumption, not a proof of semantic preservation.

### Atomicity of events

Multiple event tags in one `event` command are emitted sequentially:
`event [A(), B()]` emits `A()` first and then `B()`. Their simultaneous
occurrence is not preserved, and the compiler warns about this translation.

### Provability

ProVerif may return `unknown` for properties that Tamarin can prove or
falsify. Its over-approximation can lose information needed to decide a query;
the translation can also affect provability. An `unknown` result alone does
not establish whether a property holds.

[Loop-tail continuation lowering](https://github.com/zt-iot/rabbit/pull/40)
improves trace reconstruction for some examples. At the tested revision above,
11 examples still have queries with `unknown` results.

## Code derived from ProVerif

Rabbit includes parts of the [ProVerif source code](https://gitlab.inria.fr/bblanche/proverif)
in `src/proverif_pv/parse/`. These provide the ProVerif AST, lexer, parser,
and parsing utilities used by Rabbit's ProVerif backend and its parser/printer
tests.

The following files were copied from ProVerif's repository, commit
`a138c1ea33bdf8d621035a51c973a4ceef4095be`:

- `src/proverif_pv/parse/parsing_helper.ml` and `.mli`
- `src/proverif_pv/parse/pitlexer.mll`
- `src/proverif_pv/parse/pitparser.mly`
- `src/proverif_pv/parse/pitptree.mli`
- `src/proverif_pv/parse/ptree.mli`

These files are covered by GPL-2.0-or-later. ProVerif is copyright INRIA-CNRS,
by Bruno Blanchet, Vincent Cheval, and Marc Sylvestre. Rabbit as a whole is
distributed under GPL-2.0-or-later; see the [license notice](README.md#license).

Rabbit modifications to the copied files:

- 2026-08-02 (`00f802c`): in `pitparser.mly` and `pitptree.mli`, added AST
  comment fields and declaration comments,
  and adapted parser actions to the extended AST.
- 2026-08-03 (`c3b4a21`): changed AST comments to string lists and updated
  parser actions accordingly.
- 2026-09-30: added provenance and license notices to the six copied files.

The other four copied files retain their upstream implementation.

A copy of the upstream GPL text is retained in [src/proverif_pv/parse/LICENSE](src/proverif_pv/parse/LICENSE).

## Compiler documentation

See the [compiler pipeline](docs/pipeline.md),
[guard compilation](docs/proverif_guard_compilation.md),
[persistent facts](docs/proverif_persistent_facts.md), and
[loop continuations](docs/proverif_loop_continuations.md) guides for details.
