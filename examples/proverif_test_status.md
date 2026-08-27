# ProVerif compiler test status

Checked on: 2026-08-28

Tested commit: `cde2360b9da2568d03cac6f51e33d878f27e6800` plus the current tracked working-tree changes

## Evaluation method

`examples/proverif/` is omitted because all of its tests pass.

`Tamarin verification` lists the Rabbit lemma results recorded as
`(* verified *)` and `(* falsified *)`. `ProVerif verification` lists the
results for the same properties as `true`, `false`, or `unknown`. For
comparison, Tamarin's `verified` corresponds to ProVerif's `true`, and
`falsified` corresponds to `false`.

`Status` is `Pass` only when both verifiers complete and all lemma results
match in source order. A result mismatch, `unknown`, verification error, or
unexecuted verification is `Fail`.

| Suite | Inputs | Pass | Fail |
|---|---:|---:|---:|
| `examples/*.rab` | 58 | 43 | 15 |
| `examples/proverif_verification/*.rab` | 87 | 56 | 31 |

## `examples/*.rab`

| Input | Compilation | Tamarin verification | ProVerif verification | Status | Comments |
|---|---|---|---|---|---|
| `000_simplest.rab` | Pass | `verified`, `verified` | `true`, `true` | Pass | — |
| `010_self_communication.rab` | Pass | `verified`, `verified` | `true`, `true` | Pass | — |
| `011_self_commu_no_check.rab` | Pass | `verified`, `verified` | `true`, `true` | Pass | — |
| `015_multi_communication.rab` | Pass | `verified`, `verified` | `true`, `true` | Pass | — |
| `020_pingpong.rab` | Pass | `verified`, `verified` | `true`, `true` | Pass | — |
| `021_pingpong_loop.rab` | Pass | `verified`, `verified`, `verified` | `true`, `true`, `true` | Pass | — |
| `030_nonce_handshake.rab` | Pass | `verified`, `falsified`, `verified` | `true`, `false`, `true` | Pass | — |
| `031_nonce_handshake_loop.rab` | Pass | `verified`, `verified` | `true`, `true` | Pass | — |
| `032_nonce_handshake_loop_dest.rab` | Pass | `verified`, `verified` | `true`, `true` | Pass | — |
| `033_nonce_handshake_loop_single_channel.rab` | Pass | `verified`, `verified`, `falsified` | `true`, `true`, `false` | Pass | — |
| `034_nonce_handshake_simplified.rab` | Pass | `verified`, `falsified`, `verified` | `true`, `false`, `true` | Pass | — |
| `035_nonce_handshake_no_crypto.rab` | Pass | `verified`, `falsified`, `verified` | `true`, `false`, `true` | Pass | — |
| `036_nonce_handshake_simpler.rab` | Pass | `verified`, `falsified`, `verified` | `true`, `false`, `true` | Pass | — |
| `037_nonce_handshake_loop_alice.rab` | Pass | `verified` | `true` | Pass | — |
| `038_nonce_handshake_loop_alice.rab` | Pass | `verified` | `true` | Pass | — |
| `040_asym.rab` | Pass | `verified`, `falsified` | `true`, `false` | Pass | — |
| `041_asym_commu.rab` | Pass | `verified`, `falsified`, `verified`, `verified` | `true`, `false`, `true`, `true` | Pass | — |
| `042_asym_commu_param.rab` | Rejected (expected) | `verified`, `falsified`, `verified`, `verified` | Not run | **Fail** | ProVerif verification was not run. |
| `043_asym_commu_param2.rab` | Rejected (expected) | `verified`, `falsified`, `verified`, `verified` | Not run | **Fail** | ProVerif verification was not run. |
| `044_asym_commu_param_simpler.rab` | Rejected (expected) | `verified`, `falsified`, `verified`, `verified` | Not run | **Fail** | ProVerif verification was not run. |
| `050_attack.rab` | Pass | `verified`, `verified`, `verified` | `true`, `true`, `true` | Pass | — |
| `051_attack_ch.rab` | Pass | `verified`, `verified`, `verified` | `true`, `true`, `true` | Pass | — |
| `060_allow.rab` | Pass | `verified` | `true` | Pass | — |
| `061_allow_no_syscall.rab` | Pass | `verified` | `true` | Pass | — |
| `062_allow_param.rab` | Rejected (expected) | `verified` | Not run | **Fail** | ProVerif verification was not run. |
| `063_allow.rab` | Pass | `verified` | `true` | Pass | — |
| `064_allow_with_param.rab` | Pass | `verified` | `true` | Pass | — |
| `065_allow_bounded.rab` | Pass | `verified` | `true` | Pass | — |
| `066_allow_bounded_multi_chans.rab` | Rejected (expected) | `verified` | Not run | **Fail** | ProVerif verification was not run. |
| `070_file.rab` | Pass | `verified` | `true` | Pass | — |
| `080_state.rab` | Pass | `falsified` | `false` | Pass | — |
| `081_state_param.rab` | Pass | `falsified` | `false` | Pass | — |
| `082_state_param_return.rab` | Pass | `falsified` | `false` | Pass | — |
| `090_const.rab` | Pass | `verified` | `true` | Pass | Tamarin reports wellformedness warnings for parametrized constants. |
| `091_param.rab` | Pass | `verified` | `true` | Pass | Tamarin reports wellformedness warnings for parametrized constants. |
| `092_nullary.rab` | Pass | `verified` | `true` | Pass | — |
| `100_syscall.rab` | Pass | `verified` | `true` | Pass | — |
| `110_case.rab` | Pass | `verified`, `falsified` | `true`, `false` | Pass | — |
| `120_channel.rab` | Rejected (expected) | `verified`, `falsified` | Not run | **Fail** | ProVerif verification was not run. |
| `130_var.rab` | Rejected (expected) | `verified` | Not run | **Fail** | ProVerif verification was not run. |
| `140_structure.rab` | Pass | `verified`, `verified` | `true`, `true` | Pass | — |
| `141_structure_fetch.rab` | Pass | `verified`, `verified` | `true`, `true` | Pass | — |
| `142_structure_fetch_after_delete.rab` | Pass | `verified`, `falsified`, `verified` | `true`, `unknown`, `true` | **Fail** | The verification results differ. |
| `143_structure_fetch_compression.rab` | Pass | `verified`, `verified` | `true`, `true` | Pass | — |
| `150_loop.rab` | Rejected (expected) | Error | Not run | **Fail** | ProVerif verification was not run. No Tamarin result is available. |
| `160_structure.rab` | Pass | `verified`, `falsified` | `true`, `false` | Pass | — |
| `161_structure_param.rab` | Pass | `verified`, `falsified` | `true`, `false` | Pass | — |
| `162_structure_param.rab` | Pass | `verified`, `falsified` | `true`, `false` | Pass | — |
| `200_camserver_param.rab` | Rejected (expected) | Error | Not run | **Fail** | ProVerif verification was not run. No Tamarin result is available. |
| `210_dec_failure.rab` | Pass | `verified`, `verified` | `true`, `true` | Pass | — |
| `camserver.rab` | Pass | `verified`, `falsified` | Error | **Fail** | ProVerif rejects a bitstring pattern where a channel is required. |
| `camserver_assume.rab` | Rejected (expected) | `verified`, `falsified` | Not run | **Fail** | ProVerif verification was not run. |
| `camserver_param.rab` | Rejected (expected) | Error | Not run | **Fail** | ProVerif verification was not run. No Tamarin result is available. |
| `camserver_param_assume.rab` | Rejected (expected) | Error | Not run | **Fail** | ProVerif verification was not run. No Tamarin result is available. |
| `digital_signature.rab` | Rejected (expected) | Error | Not run | **Fail** | ProVerif verification was not run. No Tamarin result is available. |
| `dns.rab` | Pass | `falsified`, `verified`, `falsified` | `false`, `true`, `false` | Pass | — |
| `secure_dns.rab` | Pass | `verified`, `verified`, `verified` | `true`, `true`, `true` | Pass | — |
| `udp_rpc.rab` | Pass | None | None | Pass | Neither backend has a lemma to verify. |

## `examples/proverif_verification/*.rab`

| Input | Compilation | Tamarin verification | ProVerif verification | Status | Comments |
|---|---|---|---|---|---|
| `access_denied.rab` | Pass | `falsified` | `false` | Pass | — |
| `access_granted.rab` | Pass | `verified` | `true` | Pass | — |
| `assignment.rab` | Pass | `verified`, `falsified` | `true`, `false` | Pass | — |
| `assumption.rab` | Pass | `verified`, `falsified` | `true`, `false` | Pass | — |
| `assumption_wildcard_unsupported.rab` | Rejected (expected) | `verified` | Not run | **Fail** | ProVerif verification was not run. |
| `attack.rab` | Pass | `verified`, `verified` | `true`, `true` | Pass | — |
| `attack_not_allowed.rab` | Pass | `verified`, `falsified` | `true`, `false` | Pass | — |
| `attack_return.rab` | Pass | `verified`, `verified` | `true`, `true` | Pass | — |
| `attack_target_filtering.rab` | Pass | `verified`, `verified` | `true`, `true` | Pass | — |
| `attacker_io.rab` | Pass | `verified` | `true` | Pass | — |
| `boolean.rab` | Pass | `verified`, `falsified` | `true`, `false` | Pass | — |
| `bounded_replication.rab` | Pass | `verified`, `verified` | `true`, `true` | Pass | — |
| `case.rab` | Pass | `verified`, `falsified` | `true`, `false` | Pass | — |
| `case_channel_state_type.rab` | Pass | `verified` | Error | **Fail** | ProVerif receives a channel-valued case state as `bitstring`. |
| `case_mutable_channel_state.rab` | Pass | `verified` | Error | **Fail** | ProVerif receives an updated channel-valued case state as `bitstring`. |
| `case_nondeterministic.rab` | Pass | `verified`, `verified`, `verified`, `verified` | `true`, `true`, `true`, `true` | Pass | — |
| `case_single_branch.rab` | Pass | `verified`, `falsified`, `falsified` | `true`, `false`, `false` | Pass | — |
| `channel.rab` | Pass | `verified`, `falsified` | `true`, `unknown` | **Fail** | The verification results differ. |
| `channel_fact_event_unsupported.rab` | Rejected (expected) | `falsified` | Not run | **Fail** | ProVerif verification was not run. |
| `channel_lemma_unsupported.rab` | Rejected (expected) | Error | Not run | **Fail** | The Tamarin backend rejects a global channel in a lemma expression. ProVerif verification was not run. |
| `channel_nondeterministic.rab` | Pass | `verified`, `verified`, `verified`, `verified` | `true`, `true`, `true`, `true` | Pass | — |
| `channel_pattern.rab` | Pass | `verified`, `falsified` | `true`, `false` | Pass | — |
| `channel_private.rab` | Pass | `falsified` | `false` | Pass | — |
| `channel_syscall.rab` | Pass | `verified` | `true` | Pass | — |
| `constants.rab` | Pass | `verified` | `true` | Pass | — |
| `correspondence.rab` | Pass | `verified`, `falsified` | `true`, `false` | Pass | — |
| `delete.rab` | Pass | `verified`, `falsified` | `true`, `unknown` | **Fail** | The verification results differ. |
| `equality_query.rab` | Pass | Error | `true`, `true`, `true` | **Fail** | The Tamarin backend fails while printing equation-fact lemmas. The verification results differ. |
| `equation.rab` | Pass | `verified` | `true` | Pass | — |
| `equational_fact_events.rab` | Pass | Error | `true`, `true`, `true`, `true`, `false`, `false`, `false`, `false`, `false`, `false` | **Fail** | The Tamarin backend fails while printing equation-fact lemmas. The verification results differ. |
| `events.rab` | Pass | `verified`, `falsified` | `true`, `false` | Pass | — |
| `external_constant.rab` | Pass | `verified` | `true` | Pass | — |
| `fetch_after_delete.rab` | Pass | `falsified` | `unknown` | **Fail** | The verification results differ. |
| `file_fact_event_unsupported.rab` | Rejected (expected) | `falsified` | Not run | **Fail** | ProVerif verification was not run. |
| `file_lemma_unsupported.rab` | Rejected (expected) | Error | Not run | **Fail** | The Tamarin backend does not support file facts in lemmas. ProVerif verification was not run. |
| `file_read.rab` | Pass | `verified` | `true` | Pass | — |
| `file_write.rab` | Pass | `verified`, `verified`, `verified` | `true`, `true`, `unknown` | **Fail** | The verification results differ. |
| `file_write_without_ac.rab` | Pass | `falsified`, `falsified`, `verified` | `true`, `true`, `unknown` | **Fail** | The verification results differ. |
| `float_unsupported.rab` | Rejected (expected) | Error | Not run | **Fail** | The Tamarin backend does not support float expressions. ProVerif verification was not run. |
| `fresh_constant_private.rab` | Pass | `falsified` | `false` | Pass | — |
| `global_fact_guard_unsupported.rab` | Rejected (expected) | `falsified` | Not run | **Fail** | ProVerif verification was not run. |
| `global_put_unsupported.rab` | Rejected (expected) | `falsified` | Not run | **Fail** | ProVerif verification was not run. |
| `inequality_query.rab` | Pass | Error | `true`, `true`, `true` | **Fail** | The Tamarin backend fails while printing inequality-fact lemmas. The verification results differ. |
| `integer_event.rab` | Pass | `verified`, `falsified`, `verified`, `falsified` | `true`, `false`, `true`, `false` | Pass | — |
| `load.rab` | Pass | `verified` | `true` | Pass | — |
| `load_library.rab` | Pass | None | None | Pass | Library input; neither backend has a lemma to verify. |
| `local_function.rab` | Pass | `verified`, `verified` | `true`, `true` | Pass | — |
| `local_function_assignment.rab` | Pass | `verified`, `verified`, `verified` | `true`, `true`, `true` | Pass | — |
| `local_function_branch_return.rab` | Pass | `verified` | `true` | Pass | — |
| `local_function_fallthrough.rab` | Pass | `verified`, `verified` | `true`, `true` | Pass | — |
| `local_function_return_in_middle.rab` | Pass | `verified` | `true` | Pass | — |
| `main_return.rab` | Pass | `verified` | `true` | Pass | — |
| `mixed_case_unsupported.rab` | Rejected (expected) | `verified` | Not run | **Fail** | ProVerif verification was not run. |
| `multiple_case_facts.rab` | Pass | `verified`, `falsified` | `true`, `false` | Pass | — |
| `multiple_channel_guards_unsupported.rab` | Rejected (expected) | `falsified` | Not run | **Fail** | ProVerif verification was not run. |
| `multiple_event_facts.rab` | Pass | `falsified`, `falsified` | `true`, `false` | **Fail** | The verification results differ. |
| `multiple_put_facts.rab` | Pass | `verified`, `verified` | `true`, `true` | Pass | — |
| `multiple_query_facts.rab` | Pass | `verified`, `verified`, `falsified` | `true`, `true`, `false` | Pass | — |
| `new.rab` | Pass | `verified` | `true` | Pass | — |
| `operator_unsupported.rab` | Rejected (expected) | Error | Not run | **Fail** | Rabbit rejects the undeclared `+` operator before Tamarin generation. ProVerif verification was not run. |
| `parameterized_channel_unsupported.rab` | Rejected (expected) | `verified` | Not run | **Fail** | ProVerif verification was not run. |
| `parameterized_constant.rab` | Pass | `verified`, `falsified` | `true`, `false` | Pass | Tamarin results were checked with the legacy backend. |
| `parameterized_process.rab` | Pass | `verified` | `true` | Pass | — |
| `parameterized_process_expression_unsupported.rab` | Rejected (expected) | `verified` | Not run | **Fail** | Compound process parameter expressions have no `param_data` encoding. |
| `passive_attack.rab` | Pass | `verified` | `true` | Pass | — |
| `plain_event.rab` | Pass | Error | `true`, `true` | **Fail** | The Tamarin backend does not support plain facts in lemmas. The verification results differ. |
| `plain_guard_unsupported.rab` | Rejected (expected) | `falsified` | Not run | **Fail** | ProVerif verification was not run. |
| `plain_lemma_unsupported.rab` | Rejected (expected) | `verified` | Not run | **Fail** | ProVerif verification was not run. |
| `plain_put_unsupported.rab` | Rejected (expected) | `falsified` | Not run | **Fail** | ProVerif verification was not run. |
| `process_fact_unsupported.rab` | Rejected (expected) | Error | Not run | **Fail** | Rabbit typing fails before Tamarin generation. ProVerif verification was not run. |
| `process_variable.rab` | Pass | `verified` | `true` | Pass | — |
| `repeat.rab` | Pass | `verified`, `verified`, `verified`, `verified`, `falsified`, `falsified` | `true`, `true`, `true`, `true`, `false`, `false` | Pass | — |
| `repeat_channel_multiple_state.rab` | Pass | `verified`, `verified`, `verified` | `true`, `true`, `true` | Pass | — |
| `scoped_assignment.rab` | Pass | `verified`, `verified`, `falsified` | `true`, `true`, `false` | Pass | — |
| `skip.rab` | Pass | `verified` | `true` | Pass | — |
| `special_guards.rab` | Pass | `falsified`, `falsified` | `true`, `false` | **Fail** | The verification results differ. |
| `string.rab` | Pass | `verified`, `falsified` | `true`, `false` | Pass | — |
| `string_public.rab` | Pass | `verified` | `true` | Pass | — |
| `structure.rab` | Pass | `verified` | `true` | Pass | — |
| `structure_identity.rab` | Pass | `falsified`, `verified` | `false`, `true` | Pass | — |
| `syscall_assignment.rab` | Pass | `verified`, `falsified` | `true`, `false` | Pass | — |
| `syscall_discard.rab` | Pass | `verified`, `verified` | `true`, `true` | Pass | — |
| `syscall_fallthrough.rab` | Pass | `verified`, `verified` | `true`, `true` | Pass | — |
| `syscall_let.rab` | Pass | `verified` | `true` | Pass | — |
| `system_parallel.rab` | Pass | `verified` | `true` | Pass | — |
| `tuple.rab` | Pass | `verified`, `falsified` | `true`, `false` | Pass | — |
| `unit_unsupported.rab` | Rejected (expected) | `verified` | Not run | **Fail** | The Tamarin result was checked with the legacy backend. ProVerif verification was not run. |
