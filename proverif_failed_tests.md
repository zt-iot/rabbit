# Test failures with ProVerif compiler

This inventory includes the constructor-pattern support merged into proverif in PR #42.

## Unknown verification results

These tests fail because ProVerif returns unknown instead of the expected result.

| Files | Expected results | Actual results |
| --- | --- | --- |
| `proverif_verification/channel.rab` | `true; false` | `true; unknown` |
| `proverif_verification/delete.rab` | `true; false` | `true; unknown` |
| `proverif_verification/fetch_after_delete.rab` | `false` | `unknown` |
| `proverif_verification/file_write.rab` | `true; true; true` | `true; true; unknown` |
| `proverif_verification/file_write_without_ac.rab` | `true; true; true` | `true; true; unknown` |
| `proverif_verification/global_facts_linear.rab` | `true; true; false` | `true; true; unknown` |
| `proverif_verification/local_facts_linear.rab` | `true; true; false` | `true; true; unknown` |
| `proverif_verification/repeat_horn_over_approx.rab` | `true` | `unknown` |
| `033_nonce_handshake_loop_single_channel.rab` | `true; true; false` | `true; unknown; unknown` |
| `142_structure_fetch_after_delete.rab` | `true; false; true` | `true; unknown; true` |
| `camserver.rab` | `true; false` | `true; unknown` |
| `camserver_assume.rab` | `true; false` | `true; unknown` |
| `camserver_param_assume.rab` | `true; false` | `true; unknown` |

## Unsupported language features

They are valid Rabbit code but are not supported in the current ProVerif compilation:

| Files | Failure stage / reason |
| --- | --- |
| `043_asym_commu_param2.rab` | The current simple type system does not allow compound (tuple) parameters. |
| `proverif_verification/float_unsupported.rab` | Float terms are not implemented. |
| `066_allow_bounded_multi_chans.rab` | Compound process parameters such as `alice<(p,p)>` are unsupported. |
| `proverif_verification/parameterized_channel_expression_unsupported.rab` | Translation of compound parameters is limited. |
| `proverif_verification/parameterized_process_expression_unsupported.rab` | Translation of compound parameters is limited. |
| `digital_signature.rab` | ProVerif wont support raw Tamarin trace formula in lemmas. |
| `proverif_verification/plain_lemma_unsupported.rab` | Raw Tamarin-specific lemma strings are unsupported. Consider using a structured query. |
| `proverif_verification/channel_family_expression_unsupported.rab` | Translation of compound parameters is limited. |
| `proverif_verification/guard_destructor_wildcard_unsupported.rab` | Destructor patterns containing wildcards are not supported |
| `proverif_verification/guard_equational_function_unsupported.rab` | Guard variables cannot be bound by supported equality or input patterns |
| `proverif_verification/guard_equational_wildcard_both_unsupported.rab` | Wildcard equality between different or equational constructor patterns is not supported |
| `proverif_verification/guard_persistent_function_named_unsupported.rab` | Unbound function patterns in persistent fact selection are not supported |
| `proverif_verification/guard_persistent_function_wildcard_unsupported.rab` | Function wildcard patterns in persistent fact selection are not supported |
| `proverif_verification/reduc_query_unsupported.rab` | Functions with `reduc` cannot be used in queries |

## Rejected code examples

| Files | Cause / error |
| --- | --- |
| `proverif_verification/operator_unsupported.rab` | No way to declare operators as functions |
| `proverif_verification/process_fact_unsupported.rab` | Process facts are not supported |
| `proverif_verification/process_fact_guard_unsupported.rab` | Process facts are not supported |
| `proverif_verification/builtin_global_guard_unsupported.rab` | `::Out(x)` cannot be used in an input guard. |
| `proverif_verification/builtin_global_put_unsupported.rab` | `::In(x)` cannot be used in `put`. |
| `proverif_verification/equality_conclusion_unsupported.rab` | Equality facts are only allowed in case/while guards |
| `proverif_verification/equality_event_unsupported.rab` | Equality facts are only allowed in case/while guards |
| `proverif_verification/equality_premise_unsupported.rab` | Equality facts are only allowed in case/while guards |
| `proverif_verification/equality_put_unsupported.rab` | Equality facts are only allowed in case/while guards |
| `proverif_verification/equality_reachable_unsupported.rab` | Equality facts are only allowed in case/while guards |
| `proverif_verification/file_correspondence_conclusion_unsupported.rab` | File facts are not allowed in events or queries |
| `proverif_verification/file_correspondence_premise_unsupported.rab` | File facts are not allowed in events or queries |
| `proverif_verification/file_fact_event_unsupported.rab` | File facts are not allowed in events or queries |
| `proverif_verification/file_lemma_unsupported.rab` | File facts are not allowed in events or queries |
| `proverif_verification/global_channel_query_unsupported.rab` | Tests the restriction on directly referencing a global channel in a query, not channel queries in general. |
| `proverif_verification/guard_constructor_unbound_unsupported.rab` | Variables or input channels have no supported binding source. |
| `proverif_verification/guard_tuple_inequality_unsupported.rab` | Variables or input channels have no supported binding source. |
| `proverif_verification/guard_tuple_no_value_unsupported.rab` | Variables or input channels have no supported binding source. |
| `proverif_verification/guard_unbound_channel_unsupported.rab` | Variables or input channels have no supported binding source. |
| `proverif_verification/inequality_conclusion_unsupported.rab` | Comparison facts are allowed only in guards; file facts cannot be used in events or queries. |
| `proverif_verification/inequality_event_unsupported.rab` | Comparison facts are allowed only in guards; file facts cannot be used in events or queries. |
| `proverif_verification/inequality_premise_unsupported.rab` | Comparison facts are allowed only in guards; file facts cannot be used in events or queries. |
| `proverif_verification/inequality_put_unsupported.rab` | Comparison facts are allowed only in guards; file facts cannot be used in events or queries. |
| `proverif_verification/inequality_reachable_unsupported.rab` | Comparison facts are allowed only in guards; file facts cannot be used in events or queries. |
| `proverif_verification/reduc_conflict_unsupported.rab` | Nondeterministic destructor is not allowed. |
| `proverif_verification/type_mismatch_unsupported.rab` | Invalid declarations, types, or operator usage. |
| `proverif_verification/undeclared_fact_unsupported.rab` | Invalid declarations, types, or operator usage. |
| `proverif_verification/undeclared_tag_unsupported.rab` | Invalid declarations, types, or operator usage. |
