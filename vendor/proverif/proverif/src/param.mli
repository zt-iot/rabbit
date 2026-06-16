open Types

val lib_name : string list ref

val def_var_name : string
val ignored_var_name : string
    
(* Use the following constants to set bits of the p_prop field
   of predicates. For the predicate p,

   pred_ANY means that there exists x1,...,xn such that p:x1,...,xn and
   if all inequalities involving x1...xn are satisfiable, then they are
   satisfied for this x1...xn.

   pred_ANY_STRICT means that there exists x such that p:x,...,x

   pred_TUPLE means that p:(x_1, ..., x_n) iff p:x_1 and ... and p:x_n
   pred_TUPLE_SELECT means further that facts p:x may be selected by the
   selection function

   pred_BLOCKING means that the predicate must never be selected by
   the selection function.

   pred_ELEM means that
     att(x) /\ elem(M_1, x) /\ ... /\ elem(M_n, x)
   becomes
     att(x) /\ att(M_1) /\ ... /\ att(M_n)
   when elem is a predicate pred_ELEM and att is a predicate pred_TUPLE
   This simplification is always done when x does not occur elsewhere.
   When x occurs elsewhere, the simplification can be done when the
   clause has no selected fact. It leads to a loss of precision in
   this case.

   pred_ATTACKER means that the predicate is one of the attacker, attacker_pi
   predicates for the different phases.

   pred_ELIMVAR means that p(y,x) /\ p(y',x) /\ y <> y' -> bad
   and p(x,y) /\ p(x,y') /\ y <> y' -> bad are present

   pred_SIMPEQ means that one should use the equational theory
   to simplify the arguments of this predicate.
*)
val pred_ANY : int
val pred_ANY_STRICT : int
val pred_TUPLE : int
val pred_TUPLE_SELECT : int
val pred_BLOCKING : int
val pred_ELEM : int
val pred_ATTACKER : int
val pred_ELIMVAR : int
val pred_SIMPEQ : int

val fun_TYPECONVERTER : int

val additional_settings : (Ptree.ident * Ptree.pval) list ref

val max_depth : int ref
val max_hyp : int ref
val max_inequality_chain : int ref
val ansi_color : bool ref
val active_attacker : bool ref
val key_compromise : int ref
val precise_let_expand : bool ref
val expand_simplify_if_cst : bool ref

val typed_frontend : bool ref
val get_ignore_types : unit -> bool
val set_ignore_types : bool -> unit
val default_set_ignore_types : unit -> unit
val get_type : typet -> typet

(* For interactive mode *)
val allow_tilde : bool ref
val trace_win_open : bool ref
val interactive_dot_command : string ref

val bipro_i_mode : bool ref

val html_output : bool ref
val html_dir : string ref
val current_query_number : int ref
val current_process_number : int ref
val derivation_number : int ref
val inside_query_number : int ref
val process_number : int ref

val allow_diff_patterns : bool ref
val has_restrictions : bool ref
val allow_private_comm_on_public_terms : bool ref

val simplify_process : int ref
val reject_choice_true_false : bool ref
val reject_no_simplif : bool ref
val prove_lemma_only : bool ref
    
val verbose_rules : bool ref
val verbose_base : bool ref
val verbose_lemmas : bool ref
type explain_clauses = NoClauses | Clauses | ExplainedClauses
val verbose_explain_clauses : explain_clauses ref
val verbose_redundant : bool ref
val verbose_completed : bool ref
val verbose_eq : bool ref
val verbose_destr : bool ref
val verbose_term : bool ref
val verbose_goal_reachable : bool ref
val verbose_dynamic_statistics : bool ref
val abbreviate_clauses : bool ref
val remove_subsumed_clauses_before_display : bool ref

val reconstruct_derivation : bool ref
val simplify_derivation : bool ref
type simplification_level_t = AttackerOnly | AttackerSameTree | AllFacts
val simplify_derivation_level : simplification_level_t ref
val unify_derivation : bool ref
val display_derivation : bool ref
val abbreviate_derivation : bool ref
val explain_derivation : bool ref
val reconstruct_trace : int ref
val trace_backtracking : bool ref
val display_init_state : bool ref

(* Parameters for recording features for the subsumption test *)

val feature : bool ref
val record_funs : bool ref
val record_names : bool ref
val record_predicates : bool ref
val record_events : bool ref
val record_tables : bool ref

val record_depth : bool ref
val record_width : bool ref

val cleanup_threshold : int ref

(* Parameter for unification trie *)
val unify_trie_term_max_depth : int ref

type sel_type = NounifsetMaxsize | Nounifset | Term | TermMaxsize
val select_fun : sel_type ref

val should_stop_term : bool ref

type red_type = NoRed | SimpleRed | BestRed
val redundancy_test : red_type ref

val move_new : bool ref
val move_let : bool ref

val redundant_hyp_elim : bool ref
val redundant_hyp_elim_begin_only : bool ref
val check_pred_calls : bool ref
val eq_in_names : bool ref

val simpeq_all_predicates : bool ref
val simpeq_final : bool ref

type eqtreatment = ConvLin | NonProved
val eqtreatment : eqtreatment ref

val symb_order : (string * Parsing_helper.extent) option ref

type trace_display = NoDisplay | ShortDisplay | LongDisplay
val trace_display : trace_display ref

type trace_display_graphicx = TextDisplay | GraphDisplay
val trace_display_graphicx : trace_display_graphicx ref


val command_line_graph : string ref
val command_line_graph_set : bool ref

val graph_output : bool ref

val tulafale : int ref

(* For swapping at barriers *)

val interactive_swapping : bool ref
val set_swapping : (string * Parsing_helper.extent) option ref

val boolean_param : bool ref -> string -> Parsing_helper.extent -> Ptree.pval -> unit
val common_parameters : string -> Parsing_helper.extent -> Ptree.pval -> unit



(* types *)

val any_type : typet
val time_type : typet
val bitstring_type : typet
val channel_type : typet
val sid_type : typet
val event_type : typet
val bool_type : typet
val table_type : typet
val nat_type : typet
val occurrence_type : typet

(* Special type to record that the type is not defined yet *)
val tmp_type : typet list

val get_type_suffix : typet -> string

(* predicates *)

val event_pred : predicate
val inj_event_pred : predicate
val event2_pred : predicate
val event_pred_block : predicate
val inj_event_pred_block : predicate
val event2_pred_block : predicate
val bad_pred : predicate
val dummy_pred : predicate

val dummy_fact : fact

val fresh_injective_index : unit -> int

(* For integer *)

val has_integer : bool ref

(* [memo f] is the memoizing version of function [f]:
   when [f] is called several times with the same argument, it returns
   the same result without recomputing [f] *)

val memo : ('a -> 'b) -> 'a -> 'b

(* [memo_type f] is similar to [memo f] but specific to functions that
   take a type as argument. It normalizes the type argument before
   calling the memoizing version of [f]: when types are ignored, the
   type is always [any_type]. *)

val memo_type : (typet -> 'b) -> (typet -> 'b)

(* Phases *)

val build_pred_memo : info -> predicate
val get_pred : info -> predicate

(* Precise *)

type precise_t =
  | NotPrecise
  | Precise
  | PreciseWithoutArgsInNames

val precise_actions : precise_t ref
val get_precise : unit -> bool
val get_names_with_args : unit -> bool
val get_precise_event : precise_info -> funsymb

(* Choice *)

val choice_fun : typet -> funsymb
val choice_fst_fun : typet -> funsymb
val choice_snd_fun : typet -> funsymb
val has_choice : bool ref
val has_barrier : bool ref

(* For the saturation and verification of queries *)

val event_lemma_simplification : bool ref

val induction_lemmas : bool ref
val induction_queries : bool ref

val sat_application : t_lemma_application ref
val verif_application : t_lemma_application ref

val dummy_solve_status : Pitypes.t_solve_corresp_status

type nounif_ignore_once_t = NIO_None | NIO_Auto | NIO_All
val nounif_ignore_once : nounif_ignore_once_t ref
val initial_nb_of_nounif_ignore : int ref

(* Values computed from the input file *)

val types_initial : typet list
val session1 : funsymb

(* Current pi calculus state *)

val dummy_pi_state : Pitypes.t_pi_state
val current_state : Pitypes.t_pi_state ref
val get_process_query : Pitypes.t_pi_state -> Pitypes.t_process_desc * Pitypes.t_query
val is_noninterf : Pitypes.t_pi_state -> bool
val is_equivalence_two_processes : Pitypes.t_pi_state -> bool

(* Reset parameters to their default values *)

val reset_param : unit -> unit

val fresh_record : unit -> int
