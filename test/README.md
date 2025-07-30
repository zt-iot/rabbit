# Unit tests

These tests to detect unexpected behavior changes by code modifications as soon as possible.

## How to execute

```
dune exec ./test.exe test.rab
```

## Test file `test.rab`

File `test.rab` contains *multiple* tests separated with a comment with 3 starts:

```
(*** specs separated by commas *)
```

Each test is name-checked by the original Rabbit loader and the new typer, 
then their results are matched with the specs in the comment. If any unexpected
result is given the test fails.

### Spec

- `Success`: The original loader accepts the test.
- `Fail regex`: The original loader rejects the test with an error message matches with the regex.
- `TyperSuccess`: The new typer accepts the rest.
- `TyperFail regex`: The new typer rejects the test with an error message matches with the regex.
- `Verified`: The lemmas are verified by Tamarin prover.
- `Falsified`: The lemmas are falsified by Tamarin prover.
