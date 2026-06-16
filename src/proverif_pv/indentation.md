# ProVerif Example Indentation Notes

Source surveyed: `vendor/proverif/proverif/examples/**/*.pv`

## Corpus summary

- Surveyed files: 107
- Non-empty lines: 11894
- Lines with no leading indentation: 5565
- Lines indented with spaces only: 3586
- Lines indented with tabs only: 2278
- Lines with mixed tabs and spaces: 465

This means the examples are **not** formatted with one rigid house style. There is visible variation between older protocol examples, newer lemma examples, and `.m4.pv` template files.

## Strongest recurring patterns

### 1. Top-level declarations are usually flush left

Common top-level forms start in column 0:

- `type`
- `fun`
- `reduc`
- `query`
- `process`
- `let processA(...) =`
- `const`

This is the clearest stable convention across the corpus.

### 2. Process bodies are often indented by one level

Inside `process` or `let process... =`, the next commands are usually indented by one level.

Two common realizations of that one level appear:

- `1 tab`
- `2 spaces`

Examples:

- Older protocol files such as `examples/pitype/choice/NeedhamSchroederPK-corr1.pv` often use `1 tab` for process commands.
- Simpler or newer files such as `examples/pitype/lemma/toy-one-dec.pv` often use `2 spaces`.

### 3. Continuation/alignment lines often use spaces

Even in files whose main process indentation uses tabs, continuation lines are frequently aligned using spaces.

Typical cases:

- comment bodies under `(* ... *)`
- continued `const` lists
- wrapped explanatory comments
- some lines following `let`, `if`, or message-label comments

Example:

- `examples/pitype/choice/NeedhamSchroederPK-corr1.pv` uses tabs for several process steps, but some neighboring comment and continuation lines are aligned with spaces.

### 4. Comment indentation is freer than code indentation

Multi-line comments are often visually aligned for readability rather than mechanically indented to a fixed width.

Common shapes:

- block comments starting at column 0
- comment interiors indented by 3 or 4 spaces
- comment bullets aligned under earlier text

Example:

- `examples/pitype/certified-mail-AbadiGlewHornePinkas/onefile/protocol.m4.pv` has comments whose wrapped lines are aligned with spaces under the opening line, not with a fixed code indent unit.

## Indentation widths observed

Most common leading indentation counts in the corpus:

- no indentation: 5565 lines
- `1 tab`: 2262 lines
- `8 spaces`: 861 lines
- `2 spaces`: 846 lines
- `4 spaces`: 696 lines
- `6 spaces`: 387 lines
- `10 spaces`: 275 lines

Interpretation:

- `8 spaces` is probably often a visual consequence of tab display width or manual alignment.
- `2 spaces` and `4 spaces` both appear often enough that neither can be called the unique canonical space indent.
- indentation is frequently used for visual alignment, not just block depth.

## Mixed indentation

Mixed tab/space indentation exists in the examples, so the corpus does **not** enforce a pure-tabs or pure-spaces rule.

Still, mixed indentation does not look like the dominant intended style. It more often appears when:

- a file uses tabs for process steps
- but spaces for alignment inside comments or wrapped continuations

So it is better understood as historical/editorial variation than as a recommended formatting rule.

## Construct-by-construct examples

This section records which constructs are commonly followed by indented lines in the examples.

### `process`

The line `process` itself is flush left, and the commands inside are indented by one level.

Example with `2 spaces`:

```pv
process
  new k:bitstring;
  new k1:bitstring;
  new k2:bitstring;
  out(c,enc(k1,k));
```

Observed in:

- `vendor/proverif/proverif/examples/pitype/lemma/toy-one-dec.pv`

### `let process... =`

Named process definitions are also flush left, with the body indented by one level.

Example with `1 tab`:

```pv
let processA(...) =
	(* Choose the other host *)
	in(c,hostX:host);
	out(c, (hostA, hostX));
```

Observed in:

- `vendor/proverif/proverif/examples/pitype/choice/NeedhamSchroederPK-corr1.pv`

### Sequential process commands

Commands such as `new`, `in`, `out`, `event`, `insert` are usually printed one per line inside a process body, each at the same indentation level.

Example:

```pv
  new k:bitstring;
  out(c,enc(k1,k));
  in(c,y:bitstring) [precise];
  out(c,dec(y,k))
```

Observed in:

- `vendor/proverif/proverif/examples/pitype/lemma/toy-one-dec.pv`

### `let ... in`

Inside processes, `let ... in` is typically on one indented line. The body after `in` is often kept on the same line when short.

Example:

```pv
	let (pkX:pkey, =hostX) = checksign(ms,pkS) in
```

and later:

```pv
	let (NY:nonce, hostY:host) = decrypt(m, skB) in
```

Observed in:

- `vendor/proverif/proverif/examples/pitype/choice/NeedhamSchroederPK-corr1.pv`

### `if ... then`

The condition line itself is indented like any other process instruction. The following action is sometimes indented at the same level rather than one extra level, especially in older examples.

Example:

```pv
	if hostX = hostB then
	out(c, sencrypt(secretANa, Na));
	out(c, sencrypt(secretANb, NX2)).
```

This is important: the examples do **not** consistently add another indentation level under `then`.

Observed in:

- `vendor/proverif/proverif/examples/pitype/choice/NeedhamSchroederPK-corr1.pv`

### `get`

`get` tends to behave like other process commands: the whole construct sits at one process indentation level. In the example corpus, many `get` constructs are kept on one logical line unless they are long.

Practical takeaway:

- if a printer wraps `get`, it should probably indent its continuation lines by one extra visual level
- but the corpus does not give a single dominant wrapped style

### `equivalence`

`equivalence` itself is flush left, and the two compared processes are usually written on the following lines, each indented by one level.

Short example:

```pv
equivalence
	new c_k:channel;(!reader(c_k) | !new ke:bitstring; new km:bitstring; passportUK(c_k,ke,km))
	
	new c_k:channel;(!reader(c_k) | !new ke:bitstring; new km:bitstring; !passportUK(c_k,ke,km))
```

Observed in:

- `vendor/proverif/proverif/examples/pitype/choice/epassportUK_processes.pv`

Longer example with wrapped substructure:

```pv
equivalence
	new sk_b:bitstring; new sk_a:bitstring; out(c,pk(sk_b)); out(c,pk(sk_a));
	  (
	    (! new sk_c:bitstring;! system(sk_c,sk_b))
	  |
	    (! new sk_c:bitstring;! system(sk_c,sk_b))
	  )
```

Observed in:

- `vendor/proverif/proverif/examples/pitype/choice/private_authentication_unbound.pv`

What this suggests:

- `equivalence` behaves like a top-level header, similar to `process`
- each side of the equivalence is typically indented one level
- if one side wraps across multiple lines, continuation lines often get extra space indentation for visual grouping
- blank lines between the two sides are common

### `query`, `not`, `reduc`, `fun`, `type`

These top-level specification declarations are usually flush left and usually remain on one line unless long.

Examples:

```pv
query attacker(s).
not attacker(new skA).
reduc forall y: key, x: bitstring; decE(y, E(y,x)) = x.
```

Observed in:

- `vendor/proverif/proverif/examples/pitype/lemma/toy-one-dec.pv`
- `vendor/proverif/proverif/examples/pitype/choice/NeedhamSchroederPK-corr1.pv`
- `vendor/proverif/proverif/examples/pitype/certified-mail-AbadiGlewHornePinkas/onefile/protocol.m4.pv`

### `const` lists

When a `const` declaration spans multiple lines, the first line starts flush left and the following items are aligned with spaces.

Example:

```pv
const Give,      (* Message 1 *)
      Wants,     (* Message 2 *)
      Try,       (* Message 3 *)
      Released,  (* Message 4 *)
      Received: tag [data].
```

Observed in:

- `vendor/proverif/proverif/examples/pitype/certified-mail-AbadiGlewHornePinkas/onefile/protocol.m4.pv`

### Multi-line comments

Multi-line comments frequently use visual alignment with spaces rather than block indentation tied to syntax depth.

Example:

```pv
(* Constant authentication modes 
   We encode the authentication modes as pairs:
     BothAuth in the paper is coded (Auth,Auth) 
     SAuth in the paper is coded (Auth,NoAuth)
```

Observed in:

- `vendor/proverif/proverif/examples/pitype/certified-mail-AbadiGlewHornePinkas/onefile/protocol.m4.pv`

Typical pattern:

- opening `(*` line at current indentation
- wrapped body lines indented by 3 or more spaces for readability
- deeper bullets/comments may add another 2 spaces

### Preprocessor-like template constructs in `.m4.pv`

In `.m4.pv` files, directives like `ifdef(...)` are generally flush left like top-level declarations. The text inside is not always indented as a structured block.

Example:

```pv
ifdef(`PROP4',`

(* It is assumed that an attacker cannot relate q and r = Reply(h,q) 
   except for the hosts h it creates itself *)
```

Observed in:

- `vendor/proverif/proverif/examples/pitype/certified-mail-AbadiGlewHornePinkas/onefile/protocol.m4.pv`

So for `.m4.pv`, indentation often reflects macro editing convenience more than ProVerif block structure.

## Practical conclusion for our printer

If we want output that looks consistent with the examples, the safest summary is:

1. Keep top-level declarations flush left.
2. Indent nested process or block content by exactly one logical level.
3. Prefer one consistent indentation unit in generated output instead of reproducing corpus inconsistency.
4. Use spaces for continuation alignment if we introduce multiline pretty-printing.

## Suggested generated style

For generated `.pv`, a reasonable stable style would be:

- top-level: no indentation
- nested code under `process`, `let ... =`, `if`, `get`, `event`, and similar constructs: `2 spaces`
- wrapped continuations: align with spaces, not tabs
- avoid mixed tab/space indentation in generated output

This suggested style matches part of the corpus, is easy to print, and avoids inheriting historical inconsistency from the example set.
