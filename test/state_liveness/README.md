# State argument reduction

The default compiler output is unchanged. Enable the pass with:

```sh
opam exec -- dune exec src/rabbit.exe -- input.rab --state-liveness true -o output.spthy
```

The option is independent of `--compress` and `--tag-transition`. It applies to
`Spthy`, the default compiler, rather than the `--legacy` backend.

## Preservation argument

The pass runs after expression compilation has collected all constant
dependencies, and before structured facts are lowered to printed facts. Only
State mappings are projected. Rule identities, roles, comments, non-State
premises and conclusions, actions, restrictions and lemmas are preserved.
Parameters, transition counters and the linear State token are also preserved.

Each State symbol has one ordered slot schema, shared by every producer and
consumer, including initialization. Slot zero represents the return register;
its identifier may differ between edges. Other slots are identified using the
full stamped identifiers, rather than their source names. Inconsistent schemas,
non-variable or repeated State premise slots, State actions, and multiple State
premises are rejected rather than optimized unsafely.

Starting from empty live sets, the pass repeatedly retains source slots whose
values occur in a non-State fact, a protected State parameter, or a retained State
slot expression. The finite monotone iteration includes every branch and loop
back edge. It computes the least fixed point of these syntactic dependencies;
it does not attempt minimization using the equational theory.

Let P project each ground State fact onto its retained slots, leaving all other
facts unchanged. For a generated rule:

- Any original application projects to the reduced application with the same
  rule identity and actions.
- Conversely, an application of the reduced rule can be lifted from any
  corresponding original reachable configuration. Extend its substitution with
  the erased source values. State premise slots are distinct variables, and
  the erased values occur in no retained condition, action, parameter or output
  expression, so this extension imposes no additional matching condition.
  Instantiating the original conclusion projects to the reduced conclusion.

Starting from the empty configuration and including the initialization rules,
these directions give the same rule/action traces under P. Restrictions and
lemmas are unchanged and see the same action traces. In particular, a dead
assignment's constant dependency must remain: removing that premise could
introduce executions that were previously blocked.

Internal State displays change by design. Proof-search order, the particular
counterexample displayed by Tamarin, runtime, and whether a bounded proof search
finishes are not guaranteed to be identical.

## Regression tests

Run the tests without requiring Tamarin:

```sh
opam exec -- dune runtest test/state_liveness
```

They cover initialization, overwrites, terminal States, branch unions, loop fixed
points, register propagation across edge-local identifiers, shadowing,
premise-only bindings, inequalities, constant dependencies, parameters, counters,
and invalid State schemas. An independent checker checks the local preservation
obligation for the synthetic rules. An independent bounded multiset interpreter
compares all rule/action trace prefixes through six steps, including blocked
constant accesses. These bounded tests are regression checks, not a formal proof
for arbitrary programs.

Full compiler output comparisons use nine existing examples, each with graph
compression and transition tagging both enabled and disabled. They erase only
State argument lists and compare everything else up to auxiliary alpha-renaming.
