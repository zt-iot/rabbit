# Rabbit ProVerif compiler

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
