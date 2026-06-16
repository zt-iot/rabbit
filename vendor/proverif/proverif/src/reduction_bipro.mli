open Types

val do_reduction : ?bad_reached_in_lemmas:bool -> Pitypes.realquery option -> (Pitypes.realquery_e * bool) list -> Types.fact_tree -> bool

exception FailOnlyOnSide of int
val bi_action: (int -> 'a) -> 'a * 'a
val term_evaluation_fail : term -> int -> term
val term_evaluation_to_true : term -> int -> term
val is_in_public: (term * (term * term)) list ->
                  term * term -> term option
val decompose_term : term * (term * term) -> (term * (term * term)) list
val decompose_term_rev : binder * (term * term) -> (binder * (term * term)) list
val add_public:
  (term * term) Pitypes.reduc_state ->
  term * term -> term * (term * term) Pitypes.reduc_state
val match_pattern: pattern -> int -> term -> unit
val equal_bi_terms_modulo: term * term -> term * term -> bool
val noninterftest_to_string: 'a Pitypes.noninterf_test -> string
