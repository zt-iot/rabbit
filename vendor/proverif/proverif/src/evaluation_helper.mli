open Types

val term_evaluation : term -> term
val equal_terms_modulo_eval : term -> term -> bool
val term_evaluation_fail : term -> term
val match_pattern : pattern -> term -> unit
val decompose_term : term * term -> (term * term) list
val decompose_list : (term * term) list -> (term * term) list
val decompose_term_rev : binder * term -> (binder * term) list
val decompose_list_rev : (binder * term) list -> (binder * term) list
val term_evaluation_letfilter :
    Pitypes.term_occ -> term list -> (arg_meaning * term * when_include) list ->
      term list * (arg_meaning * term * when_include) list
val is_in_public : (term * term) list -> term -> term option
val is_in_public_list : (term * term) list -> term list -> term list option
val decompose_tuple : term -> term list
val can_be_built : (term * term) list -> term -> term option
val remove_first_in_public :
  (term * term) list -> (binder * term) list -> (binder * term) list
val update_term_list : (term * term) list ->
  (term * term) list -> (binder * term) list -> (binder * term) list
val add_public_and_close :
    term Pitypes.reduc_state -> (term * term) list -> term Pitypes.reduc_state
val add_public_with_recipe :
    term Pitypes.reduc_state -> term * term -> term Pitypes.reduc_state
val add_public :
    term Pitypes.reduc_state -> term -> term * term Pitypes.reduc_state
val add_public_list :
    term Pitypes.reduc_state -> (term * term) list -> term Pitypes.reduc_state
val close_public_phase_change : term Pitypes.reduc_state -> int -> term Pitypes.reduc_state
val close_public_initial : term Pitypes.reduc_state -> term Pitypes.reduc_state
val extract_phase : int ->
  (process * 'a * 'b * 'c * 'd) list ->
  (process * 'a * 'b * 'c * 'e Pitypes.info) list
