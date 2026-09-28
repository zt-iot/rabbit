# ProVerif Compiler Name Mapping

| Description | Representation in Rabbit | Name in ProVerif |
|---|---|---|
| Identifier | `Ident.t (base, stamp)` | `base__<stamp>` |
| Global fact as event | `::E(...)` in `event [..]`, etc| `E__event_global` |
| Plain fact as event | `E(...)` in `event [..]`, etc| `E__event_plain` |
| Channel fact | `ch :: E(...)` | `E__chan` |
| Structure constructor | `E(...)` | `E__struct` |
| Structure address accessor | — | `E__struct_addr` |
| Structure argument accessor | — | `E__struct_par_<n>` |
| String | `"hello world"` | `hello_world__str` |
| Empty string | `""` | `empty__str` |
| Non-negative integer | `42` | `int__pos_42` |
| Negative integer | `-3` | `int__neg_3` |
| Concrete parameter | `indexed_value<0>` | `indexed_value_0__param` |
| Concrete parameter beginning with a digit | `1` | `value_1__param` |
| System call | `syscall send(...)` | `send__0__syscall` |
| Access outside a system call | `allow ... [.]` | `none__syscall` |
| Boolean true | `true` | `true__bool` |
| Boolean false | `false` | `false__bool` |
| Sanitized name collision | — | `<base>_1`, `<base>_2`, ... |
