# Test command

`dune exec ./test.exe xxx.rab`

This command compiles `xxx.rab` to:

- `_xxx.spthy` using the original compilation
- `_xxx.spthy.2` using the new compilation

## Prevent unexpected compilation change

If `xxx.spthy` exists, it is compared with `_xxx.spthy`. 
If they are different the test exits to prevent unexpected compilation changes.
If `xxx.spthy` does not exist, `_xxx.spthy` is copied to `xxx.spthy`.

Remove `xxx.spthy` beforehand if you are sure that you changed compilation.

## Verification test

`_xxx.spthy` and `_xxx.spthy.2` are verified by `tamarin-prover`.

You can tag lemmas in the source code `xxx.rab`. For example:

```
  lemma Invalid: (* falsified *)
    reachable ::Invalid() ;

  lemma Correspondence : (* verified *)
    corresponds ::Valid(msg, n) ~> ::Sent(msg, n)
```

- If a lemma is tagged with `(* verified *)` or not tagged, it is expected to be verified.
- If a lemma is tagged with `(* falsified *)`, it is expected to be falsified.

If the verification result of the lemmas are different from the expectations, they are reported.
