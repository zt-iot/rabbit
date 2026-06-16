# Issues

## ProVerif `equivalence` concrete syntax is not compositional

`equivalence` is parsed by the rule:

```ocaml
EQUIVALENCE tprocess tprocess
```

That is, the two processes are written back-to-back with no explicit separator.
This makes the concrete syntax hard to pretty-print safely: adding outer
parentheses around the second process can make an otherwise valid AST print to
an unparsable `.pv` program.

### Minimal reproducer

This parses:

```pv
equivalence
  x8
  x4 | x4.
```

This also parses:

```pv
equivalence
  (x8)
  (x4 | x4).
```

This does **not** parse:

```pv
equivalence
  x8
  (x4 | x4).
```

### Additional confirmed examples

This parses:

```pv
equivalence
  x8
  in(x3, y:bitstring); x4.
```

These do **not** parse:

```pv
equivalence
  x8
  (in(x3, _); x4) | x4.
```

```pv
equivalence
  x8
  (in(x3, x0); x4) | x4.
```

```pv
equivalence
  x8
  (in(x3, y:bitstring); x4) | x4.
```

```pv
equivalence
  x8
  (new x1:bitstring; x4) | x4.
```

### Conclusion

The problem is not `_`, nor typed patterns, nor `in` specifically. The problem
is that the second process of an `equivalence` cannot always be printed with an
outermost `(` `)` wrapper, even when the ordinary process printer would
naturally do so.

More precisely, the ambiguity depends on how the **first** process ends.

- `equivalence x8 (P).` can fail because the parser can try to read `x8(` as
  `IDENT LPAREN ...`
- `equivalence (x8) (P).` parses, because the end of the first process is made
  explicit by the closing `)`

In particular, the current pretty-printer strategy

- print the first process
- print the second process with the ordinary process printer

is not sufficient for `equivalence`.

We likely need an `equivalence`-specific printer rule for the second process,
which avoids outermost parentheses in cases such as:

- parallel composition `P | Q`
- restricted process `new x:T; P`
- input process `in(M, pat); P`

and probably any construct whose standard printed form starts with `(`.

### Temporary workaround

As a temporary workaround, when printing

```pv
equivalence P Q.
```

it seems safer to force both sides into an explicitly delimited form, for
example:

```pv
equivalence
  (P)
  (Q).
```

At least for the confirmed examples above, wrapping the **first** process is
enough to remove the `x8(` ambiguity, and then a parenthesized second process is
accepted.
