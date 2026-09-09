# Rabbit ProVerif compiler

## Compiler documentation

- [Guard compilation](proverif_guard_compilation.md): supported forms, variable bindings, inputs, and the known atomicity limitation.

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
