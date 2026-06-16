(** Module dealing with Lemmas and Axioms *)

open Types
open Pitypes

(* [simplify_lemma state] takes the lemmas that have been proved already and
   simplify them so that they can be transformed into clauses. Note that
   when the function is called, [state] should only contains the lemmas that
   have been proved (as well as the axioms). Moreover, the lemmas should have
   already been encoded.
   [simplify_lemma state] also records in state.pi_original_axioms the axioms
   provided by the axioms (without simplifications) *)
val simplify_lemmas : t_pi_state -> t_pi_state

val verify_conditions_query : query_e -> unit

val transl_lemmas : t_horn_state -> t_pi_state -> t_horn_state

(* [check_axioms] should be called before encoding of axioms*)
val check_axioms : 'a reduc_state -> (realquery_e * bool) list -> bool

val no_bound_name_t_lemmas : t_lemmas -> bool

val simplify_queries_for_induction : t_pi_state -> t_pi_state

(* [encode_lemmas state public_vars ror_opt] encodes the lemmas in [state.pi_lemma].
   More specifically, [state.pi_lemma] should already be translated and any single lemma
   of type [t_one_lemma] should be of the form :
    { ql_query = q; ql_original_query = None; ql_real_or_random = r_opt; ql_index_query_for_induction = None }
   with
    - [q] being a correspondance query possibly with public variables.
    - [r_opt = Some vl] being the query secret vl [real_or_random] associated to this lemma; or None otherwise.
   When the public variables of [q] differ from [public_vars] or when the associated
   query secret real_or_random [r_opt] differ from [ror_opt], the lemma is ignored.
   Invariant: Lemmas that contain [choice] should be associated with query secret real_or_random.
   Other lemmas are transformed into:
    { ql_query = q'; ql_original_query = Some q; ql_real_or_random = r_opt; ql_index_query_for_induction = None }
   where [q'] is the query [q] without public variables. *)
val encode_lemmas : t_pi_state -> term list -> term list option -> t_pi_state

(* [encode_lemmas_for_equivalence_queries state] keeps the lemmas in [state.pi_lemma]
   that are not specified with public variables or for a query secret real_or_random. *)
val encode_lemmas_for_equivalence_queries : t_pi_state -> t_pi_state

(* [translate_to_bi_lemma state] transforms the lemmas into
   bi-lemmas (lemmas using attacker2, mess2, table2 when needed),
   for use with biprocesses. *)
val translate_to_bi_lemma : t_pi_state -> t_pi_state

(* [convert_lemma_for_monoprocess lem] checks whether the bilemma corresponds in fact to
   a lemma on one side of the biprocess. If it is the case, it returns the lemma for the
   corresponding side of the biprocess (ql_application_side is set to LeftSide or RightSide).
   When it is not the case, [lem] is returned.

   Note that technically, a lemma could correspond to both sides of the biprocess.
    ex : lemma event(A(x,y)) ==> event(B(x',y'))
   But in this case, it is sufficient to prove only one side of the lemma. In the case
   the lemma would be proved on one side but not on the other, it means the biprocess
   diverges before the premises are triggered and so the lemma would not help anyway in the
   proof of equivalence. *)
val convert_lemma_for_monoprocess : t_one_lemma -> t_one_lemma
