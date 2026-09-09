# Guard Compilation Examples

These examples apply to `case`, `assume`, `repeat`, and `until`.
ProVerif fragments are schematic: declarations, access checks, and surrounding
branch/loop machinery are omitted. `Success(...)` denotes the branch body;
`else 0` stands for the failure continuation.

Naming convention: `x`, `y`, and `z` are initially unbound Rabbit pattern
variables; `a`, `b`, and `c` are constants. `_` is an anonymous wildcard.
`f` and `g` are function symbols. Names such as `first`, `second`, and
`payload` are generated ProVerif temporaries, not Rabbit pattern variables.

## 1. Compare constants

Rabbit:

```rabbit
case [f(a) = g(b)] -> ... end
```

ProVerif:

```proverif
if f(a) = g(b) then Success else 0
```

```rabbit
case [f(a) != g(b)] -> ... end
```

```proverif
if f(a) = g(b) then 0 else Success
```

## 2. Bind a variable to a known value

Rabbit:

```rabbit
case [x = 1] -> event [::Matched(x)] end
```

ProVerif:

```proverif
event Matched(one)
```

The compiler records `x ↦ one`; no runtime comparison is needed.
Here `one` represents Rabbit's integer constant `1`.

## 3. Bind tuple components

Rabbit:

```rabbit
case [a = (x, y)] -> event [::Matched(x, y)] end
```

ProVerif:

```proverif
let (x:bitstring, y:bitstring) = a in
  event Matched(x, y)
else 0
```

Nested tuples are decomposed recursively.

XXX A compilation example of nested tuples

## 4. Check a repeated variable or fixed component

Rabbit:

```rabbit
case [a = (x, x)] -> event [::Matched(x)] end
```

ProVerif:

```proverif
let (x:bitstring, y:bitstring) = a in
  if x = y then event Matched(x) else 0
else 0
```

For `a = (x, b)`, where `b` is a constant, the test is `y = b`.

## 5. Bind before comparing

Rabbit:

```rabbit
case [x != y, a = (x, y)] -> event [::Matched(x, y)] end
```

ProVerif:

```proverif
let (x:bitstring, y:bitstring) = a in
  if x = y then 0 else event Matched(x, y)
else 0
```

The compiler postpones comparisons whose variables are not yet bound.

## 6. Bind from both sides of a tuple equality

Rabbit:

```rabbit
case [(x, 2) = (1, y)] -> event [::Matched(x, y)] end
```

ProVerif:

```proverif
event Matched(one, two)
```

The equality becomes `x = 1` and `2 = y`, both compile-time bindings.
Likewise, `[x = y, y = 1]` binds both variables to `one`.

## 7. Match a tuple wildcard

Rabbit:

```rabbit
case [a = (_, b)] -> ... end
```

ProVerif:

```proverif
let (ignored:bitstring, second:bitstring) = a in
  if second = b then Success else 0
else 0
```

The wildcard is an unused tuple component; equality needs no private matcher.
Wildcard inequality still uses a matcher to test that the pattern does not match.

For wildcards on both sides, `(_, a) = (b, _)` always matches:
each component has a wildcard on one side.

## 8. Compare a function after binding its argument

Rabbit:

```rabbit
case [a = (f(x), x)] -> event [::Matched(x)] end
```

ProVerif:

```proverif
let (first:bitstring, x:bitstring) = a in
  if first = f(x) then event Matched(x) else 0
else 0
```

This obtains `x` from the tuple, not by inverting `f`.

## 9. Receive a channel fact

Rabbit:

```rabbit
case [c::Msg(x, x)] -> event [::Matched(x)] end
```

ProVerif:

```proverif
in(c, Msg(x:bitstring, second:bitstring));
if second = x then event Matched(x) else 0
```

Payloads may also contain tuple patterns. All payloads are bound before
checking fixed expressions, so `c::Msg(f(x), x)` works like example 8.

If the channel itself is initially unbound, as in
`[x::Msg(y), a = (x, _)]`, the tuple binding precedes the input.

## 10. Receive a file fact

Rabbit, with a known path:

```rabbit
case [a.x] -> event [::Matched(x)] end
```

ProVerif:

```proverif
(* Check access to a first. *)
in(file_ch, (=a, x:bitstring)) [precise];
event Matched(x)
```

Rabbit, with an unbound path variable:

```rabbit
case [x.y] -> event [::Matched(x, y)] end
```

ProVerif:

```proverif
in(file_ch, (x:bitstring, y:bitstring)) [precise];
(* Check access to the received path x. *)
event Matched(x, y)
```

The second form selects an existing file fact. It does not restore a
consumed fact if access or a later test fails.

## 11. Receive attacker input

Rabbit:

```rabbit
case [::In((x, x))] -> event [::Matched(x)] end
```

ProVerif:

```proverif
in(attacker, payload:bitstring);
let (x:bitstring, second:bitstring) = payload in
  if second = x then event Matched(x) else 0
else 0
```

## Unsupported forms

- `a = f(x)` when no other guard binds `x`: no function argument extraction.
- `a = f(_)` or `f(_, a) = f(b, _)`: no wildcards inside function applications.
- `a != (x, y)` with unbound `x, y`: no bindings through inequality.
- `(x, 2) = (y, 2)` without another value source: no arbitrary-value search.
- General global/plain fact guards, apart from `::In`, `::True()`, and `::False()`.

Function restrictions apply regardless of equations. Bound function
applications remain ordinary comparisons; declarations still translate to
ProVerif `fun`.

## Known limitation: consumption is not atomic

In example 9, `Msg(a,b)` is consumed even if `a != b`.
Rabbit would consume the fact only when the complete guard succeeds.
File inputs have the same limitation.

The generated model may therefore omit Rabbit executions, affecting both
reachability and correspondence results. This remains unresolved.
