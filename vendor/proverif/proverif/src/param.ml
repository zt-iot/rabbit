open Types
open Pitypes
open Ptree

let output_is_terminal = Unix.isatty Unix.stdout && Sys.os_type = "Unix"
  
let lib_name = ref ([]:string list)

let def_var_name = "v"
let ignored_var_name = "ignored_v"
    
(* constants for predicate properties *)

let pred_ANY = 1
let pred_TUPLE = 2
let pred_BLOCKING = 4
let pred_ANY_STRICT = 8
let pred_ELEM = 16
let pred_ATTACKER = 32
let pred_ELIMVAR = 64
let pred_SIMPEQ = 128
let pred_TUPLE_SELECT = 256

(* constants for function properties *)

let fun_TYPECONVERTER = 2

(* various parameters that can be set by the user *)

let additional_settings = ref []

let max_depth = ref (-1)
let max_hyp = ref (-1)
let max_inequality_chain = ref (-1)

let ansi_color = ref output_is_terminal

let active_attacker = ref true

let key_compromise = ref 0

let typed_frontend = ref false
type ignore_t =
    NotSet
  | Ignore
  | NotIgnore
let ignore_types = ref NotSet

let get_ignore_types () =
  match !ignore_types with
    NotSet -> Parsing_helper.internal_error "ignore_types read before set"
  | Ignore -> true
  | NotIgnore -> false

let set_ignore_types b =
  begin
  match !ignore_types with
    NotSet -> ()
  | _ -> print_string "Warning: ignore_types set twice\n"
  end;
  ignore_types := if b then Ignore else NotIgnore

let default_set_ignore_types() =
  match !ignore_types with
    NotSet -> ignore_types := Ignore
  | _ -> ()

let html_output = ref false
let html_dir = ref ""
let current_query_number = ref 1
let current_process_number = ref 1
let derivation_number = ref 0
let inside_query_number = ref 0
let process_number = ref 0

let allow_diff_patterns = ref false
let has_restrictions = ref false

let allow_private_comm_on_public_terms = ref true

let precise_let_expand = ref true
let expand_simplify_if_cst = ref true
let simplify_process = ref 1
let reject_choice_true_false = ref true
let reject_no_simplif = ref true
let prove_lemma_only = ref false
    
let verbose_rules = ref false
let verbose_base = ref false
let verbose_lemmas = ref false
type explain_clauses = NoClauses | Clauses | ExplainedClauses
let verbose_explain_clauses = ref NoClauses
let verbose_redundant = ref false
let verbose_completed = ref false
let verbose_goal_reachable = ref true
let verbose_eq = ref true
let verbose_destr = ref false
let verbose_term = ref true
let verbose_dynamic_statistics = ref output_is_terminal
let abbreviate_clauses = ref true
let remove_subsumed_clauses_before_display = ref true

let reconstruct_derivation = ref true
let simplify_derivation = ref true
type simplification_level_t = AttackerOnly | AttackerSameTree | AllFacts
let simplify_derivation_level = ref AttackerSameTree
let unify_derivation = ref true

let display_derivation = ref true
let abbreviate_derivation = ref true
let explain_derivation = ref true
let reconstruct_trace = ref 4
let trace_backtracking = ref true

(* Parameters for recording features for the subsumption test *)

let feature = ref true

let record_funs = ref true
let record_names = ref false
let record_predicates = ref true
let record_events = ref true
let record_tables = ref true

let record_depth = ref false
let record_width = ref false

let cleanup_threshold = ref 10

(* Parameter for unification trie *)

let unify_trie_term_max_depth = ref 5

(* For trace reconstruction, to disable display of initial state when
   backtracking is forbidden and the trace is displayed as it is build. *)
let display_init_state = ref true

(* let testeq = ref (None : (Types.predicate * Types.funsymb list) option) *)

type sel_type = NounifsetMaxsize | Nounifset | Term | TermMaxsize
let select_fun = ref TermMaxsize

let should_stop_term = ref true

type red_type = NoRed | SimpleRed | BestRed
let redundancy_test = ref BestRed

let move_new = ref false
let move_let = ref true

let redundant_hyp_elim = ref true
let redundant_hyp_elim_begin_only = ref true

let check_pred_calls = ref true

let eq_in_names = ref false

let simpeq_final = ref true
let simpeq_all_predicates = ref false

type eqtreatment = ConvLin | NonProved
let eqtreatment = ref ConvLin

let symb_order = ref None

type trace_display = NoDisplay | ShortDisplay | LongDisplay
let trace_display = ref ShortDisplay

(*for interactive mode *)
let allow_tilde = ref false
(* Reference to know if win_trace is open in interactive mode *)
let trace_win_open = ref false
let interactive_dot_command = ref "dot"

(* Reference to true if the user choose to simulate biprocesses *)
let bipro_i_mode = ref false

(* for trace graph *)
type trace_display_graphicx = TextDisplay | GraphDisplay
let trace_display_graphicx = ref TextDisplay


let command_line_graph = ref "dot -Tpdf %1.dot -o %1.pdf"
let command_line_graph_set = ref false

let graph_output = ref false

let tulafale = ref 0

(* For swapping at barriers *)

let interactive_swapping = ref false
let set_swapping = ref None

let boolean_param flag p ext v =
  match v with
    S ("no",_) | S ("false",_) -> flag := false
  | S ("yes",_) | S ("true",_) -> flag := true
  | _ -> Parsing_helper.input_error ("Unexpected value for parameter " ^ p ^ "=" ^
		       (match v with S (s,_) -> s | I n -> string_of_int n)) ext

let common_parameters p ext v =
  match (p,v) with
  | "color", _ -> boolean_param ansi_color p ext v
  | "verboseBase", _ -> boolean_param verbose_base p ext v
  | "verboseStatistics", _ -> boolean_param verbose_dynamic_statistics p ext v
  | "verboseGoalReachable", _ -> boolean_param verbose_goal_reachable p ext v
  | "verboseRules", _ -> boolean_param verbose_rules p ext v
  | "verboseRedundant", _ -> boolean_param verbose_redundant p ext v
  | "verboseCompleted", _ -> boolean_param verbose_completed p ext v
  | "verboseEq", _ -> boolean_param verbose_eq p ext v
  | "verboseTerm", _ -> boolean_param verbose_term p ext v
  | "abbreviateClauses", _ -> boolean_param abbreviate_clauses p ext v
  | "maxDepth", S ("none",_) -> max_depth := -1
  | "maxDepth", I s -> max_depth := s
  | "maxInequalityChain", S ("none",_) -> max_inequality_chain := -1
  | "maxInequalityChain", I s -> max_inequality_chain := s
  | "maxHyp", I s -> max_hyp := s
  | "maxHyp", S ("none",_) -> max_hyp := -1
  | "selFun", S ("Nounifset",_) -> select_fun := Nounifset
  | "selFun", S ("NounifsetMaxsize",_) -> select_fun := NounifsetMaxsize
  | "selFun", S ("Term",_) -> select_fun := Term
  | "selFun", S ("TermMaxsize",_) -> select_fun := TermMaxsize
  | "stopTerm", _ -> boolean_param should_stop_term p ext v
  | "redundancyElim", S("no",_) -> redundancy_test := NoRed
  | "redundancyElim", S("simple",_) -> redundancy_test := SimpleRed
  | "redundancyElim", S("best",_) -> redundancy_test := BestRed
  | "redundantHypElim", S("beginOnly",_) ->
      redundant_hyp_elim := true;
      redundant_hyp_elim_begin_only := true
  | "redundantHypElim", S (("true"|"yes"),_) ->
      redundant_hyp_elim := true;
      redundant_hyp_elim_begin_only := false
  | "redundantHypElim", S (("false"|"no"),_) -> redundant_hyp_elim := false
  | "simpEqFinal", _ ->  boolean_param simpeq_final p ext v
  | "simpEqAll", _ ->  boolean_param simpeq_all_predicates p ext v
  | "eqTreatment", S ("convLin",_) -> eqtreatment := ConvLin
  | "eqTreatment", S ("nonProved",_) -> eqtreatment := NonProved (* Undocumented! *)
  | "symbOrder", S sext -> symb_order := Some sext
  | "reconstructDerivation", _ -> boolean_param reconstruct_derivation p ext v
  | "simplifyDerivation", _ -> boolean_param simplify_derivation p ext v
  | "displayDerivation", _ -> boolean_param display_derivation p ext v
  | "abbreviateDerivation", _ -> boolean_param abbreviate_derivation p ext v
  | "feature", _ -> boolean_param feature p ext v
  | "featureFuns", _ -> boolean_param record_funs p ext v
  | "featureNames", _ -> boolean_param record_names p ext v
  | "featurePredicates", _ -> boolean_param record_predicates p ext v
  | "featureEvents", _ -> boolean_param record_events p ext v
  | "featureTables", _ -> boolean_param record_tables p ext v
  | "featureDepth", _ -> boolean_param record_depth p ext v
  | "featureWidth", _ -> boolean_param record_width p ext v
  | "cleanupThreshold", I n ->
      if n < 0 || n > 100 then
	Parsing_helper.input_error "The cleanupThreshold value should be between 0 and 100" ext;
      cleanup_threshold := n
  | "unifyTrieTermMaxDepth", I n ->
      if n < 1 then
	Parsing_helper.input_error "The unifyTrieTermMaxDepth value should be at least 1" ext;
      unify_trie_term_max_depth := n
  | _, _ -> Parsing_helper.input_error ("Bad parameter " ^ p ^ "=" ^
			 (match v with S (s,_) -> s | I n -> string_of_int n) ^ ".") ext

(* types *)

let any_type = { tname = "any_type" }
let bitstring_type = { tname = "bitstring" }
let time_type = { tname = "time" }
let channel_type = { tname = "channel" }
let sid_type = { tname = "sid" } (* session ids *)
let event_type = { tname = "event" }
let bool_type = { tname = "bool" }
let nat_type = { tname = "nat" }
let table_type = { tname = "table" }
let occurrence_type = { tname = "occurrence" } (* Occurence for injectivity *)

let tmp_type = [{ tname = "temporary_type_should_be_removed" }]

let get_type ty =
  if get_ignore_types() then any_type else ty

(* predicates *)

let get_phase_suffix i =
  if i = 0 then "" else "_p" ^ (string_of_int i)

let get_type_suffix t =
  if t == any_type then "" else "_" ^ t.tname

let rec tl_to_string sep = function
    [] -> ""
  | [a] -> a.tname
  | (a::l) -> a.tname ^ sep ^ (tl_to_string sep l)

let build_pred = function
    Attacker(i,t) ->
      { p_name = "attacker" ^ (get_type_suffix t) ^ (get_phase_suffix i);
        p_type = [t];
        p_prop = pred_ANY + pred_TUPLE + pred_ATTACKER;
        p_info = Attacker(i,t);
        p_record = 0 }
  | Mess(i,t) ->
      { p_name = "mess" ^ (get_type_suffix t) ^ (get_phase_suffix i);
        p_type = [channel_type; t];
        p_prop = 0;
        p_info = Mess(i,t);
        p_record = 0 }
  | InputP(i) ->
      { p_name = "input" ^ (get_phase_suffix i);
        p_type = [channel_type];
        p_prop = 0;
        p_info = InputP(i);
        p_record = 0 }
  | OutputP(i) ->
      { p_name = "output" ^ (get_phase_suffix i);
        p_type = [channel_type];
        p_prop = 0;
        p_info = OutputP(i);
        p_record = 0 }
  | AttackerBin(i,t) ->
      { p_name = "attacker2" ^ (get_type_suffix t) ^ (get_phase_suffix i);
        p_type = [t;t];
        p_prop = pred_TUPLE + pred_TUPLE_SELECT + pred_ELIMVAR + pred_SIMPEQ + pred_ANY + pred_ATTACKER;
        p_info = AttackerBin(i,t);
        p_record = 0 }
  | MessBin(i,t) ->
      { p_name = "mess2" ^ (get_type_suffix t) ^ (get_phase_suffix i);
        p_type = [channel_type; t; channel_type; t];
        p_prop = 0;
        p_info = MessBin(i,t);
        p_record = 0 }
  | InputPBin(i) ->
      { p_name = "input2" ^ (get_phase_suffix i);
        p_type = [channel_type; channel_type];
        p_prop = 0;
        p_info = InputPBin(i);
        p_record = 0 }
  | OutputPBin(i) ->
      { p_name = "output2" ^ (get_phase_suffix i);
        p_type = [channel_type; channel_type];
        p_prop = 0;
        p_info = OutputPBin(i);
        p_record = 0 }
  | AttackerGuess(t) ->
      { p_name = "attacker_guess" ^ (get_type_suffix t);
        p_type = [t;t];
        p_prop = pred_TUPLE + pred_TUPLE_SELECT + pred_ELIMVAR + pred_SIMPEQ + pred_ANY + pred_ATTACKER;
        p_info = AttackerGuess(t);
        p_record = 0 }
  | Compromise(t) ->
      { p_name = "comp" ^ (get_type_suffix t);
        p_type = [t];
        p_prop = pred_TUPLE + pred_ANY;
        p_info = Compromise(t);
        p_record = 0 }
  | Equal(t) ->
      { p_name = "equal" ^ (get_type_suffix t);
        p_type = [t;t];
        p_prop = 0;
        p_info = Equal(t);
        p_record = 0 }
  | Table(i) ->
      { p_name = "table" ^ (get_phase_suffix i);
        p_type = [table_type];
        p_prop = 0;
        p_info = Table(i);
        p_record = 0 }
  | TableBin(i) ->
      { p_name = "table2" ^ (get_phase_suffix i);
        p_type = [table_type;table_type];
        p_prop = 0;
        p_info = TableBin(i);
        p_record = 0 }
  | UserPred(Polym(s,i,tl)) ->
      { p_name = s ^ (if List.for_all (fun x -> x == any_type) tl then "" else
                      if List.for_all (fun x -> x == List.hd tl) tl then "_" ^ (List.hd tl).tname else
                      "_" ^ (tl_to_string "_" tl));
        p_type = tl;
        p_prop = i;
        p_info = UserPred(Polym(s,i,tl));
        p_record = 0 }
  | TestUnifP(t) ->
      { p_name = "testunif" ^ (get_type_suffix t);
        p_type = [t; t];
        p_prop = pred_BLOCKING;
        p_info = TestUnifP(t);
        p_record = 0 }
  | Combined(pl) ->
      (* Combines predicates in [pl] into a single predicate *)
      { p_name = "combined_" ^ (String.concat "_" (List.map (fun p -> p.p_name) pl));
        p_type = List.concat (List.map (fun p -> p.p_type) pl);
        p_prop = 0;
        p_info = Combined(pl);
        p_record = 0 }
  | Subterm(t,t') ->
      { p_name = "subterm";
        p_type = [t;t'];
        p_prop = 0;
        p_info = Subterm(t,t');
        p_record = 0
      }
  | Block p ->
      if p.p_prop land pred_BLOCKING != 0
      then Parsing_helper.internal_error "[param.ml >> build_pred] A predicate cannot be the block version of another blocking predicate.";

      { p_name = ("b-"^p.p_name);
        p_type = p.p_type;
        p_prop = pred_BLOCKING;
        p_info = Block p;
        p_record = 0
      }
  | UserPred(Monom) | OtherInternalPred -> Parsing_helper.internal_error "[param.ml >> build_pred] Unexpected info."

let memo f =
  let table = Hashtbl.create 7 in
  fun x ->
    try
      Hashtbl.find table x
    with Not_found ->
    let r = f x in
    Hashtbl.add table x r;
    r

let memo_type f =
  (* Build the memoizing version of [f] before having the type argument *)
  let memo_f = memo f in
  fun ty -> memo_f (get_type ty)

let build_pred_memo = memo build_pred

let get_pred info =
  let info =
    if get_ignore_types() then
      match info with
        Attacker(i,t) -> Attacker(i,any_type)
      |	Mess(i,t) -> Mess(i,any_type)
      |	AttackerBin(i,t) -> AttackerBin(i,any_type)
      |	MessBin(i,t) -> MessBin(i,any_type)
      |	AttackerGuess(t) -> AttackerGuess(any_type)
      |	Compromise(t) -> Compromise(any_type)
      |	Equal(t) -> Equal(any_type)
      |	UserPred(Polym(s,i,tl)) -> UserPred(Polym(s,i, List.map (fun _ -> any_type) tl))
      |	TestUnifP(t) -> TestUnifP(any_type)
      | Subterm(t,t') -> Subterm(any_type,any_type)
      |	x -> x
    else
      info
  in
  build_pred_memo info

let fresh_injective_index =
  let accu = ref 0 in
  let f () =
    incr accu;
    !accu
  in
  f

(* For authenticity *)

let event_pred = { p_name = "event"; p_type = [event_type]; p_prop = 0; p_info = OtherInternalPred; p_record = 0 }
let inj_event_pred = { p_name = "inj-event"; p_type = [event_type;occurrence_type] ; p_prop = 0; p_info = OtherInternalPred; p_record = 0 }
let event2_pred = { p_name = "event2"; p_type = [event_type;event_type]; p_prop = 0; p_info = OtherInternalPred; p_record = 0 }

let event_pred_block = build_pred_memo (Block event_pred)
let inj_event_pred_block = build_pred_memo (Block inj_event_pred)
let event2_pred_block = build_pred_memo (Block event2_pred)

(* For non-interference *)

let bad_pred = { p_name = "bad"; p_type = []; p_prop = pred_BLOCKING; p_info = OtherInternalPred; p_record = 0 }

(* Predicate used as replacement for the conclusion in backward search *)

let dummy_pred = { p_name = "dummy"; p_type = []; p_prop = 0; p_info = OtherInternalPred; p_record = 0 }
let dummy_fact = Pred(dummy_pred, [])

(* Incremental index for function *)

let fresh_record =
  let i = ref 0 in

  (fun () ->
    decr i;
    !i
  )

(* For lemma *)

type precise_t =
  | NotPrecise
  | Precise
  | PreciseWithoutArgsInNames

let precise_actions = ref NotPrecise

let get_precise() =
  match !precise_actions with
  | NotPrecise -> false
  | _ -> true

let get_names_with_args() =
  match !precise_actions with
  | PreciseWithoutArgsInNames -> false
  | _ -> true

let build_precise_event = function
  | Action ty ->
      let name = "@p_act" ^ (get_type_suffix ty) in
      {
        f_name = Fixed name;
        f_type = [occurrence_type;ty],event_type;
        f_cat = Eq[];
        f_initial_cat = Eq[];
        f_private = true;
        f_options = 0;
        f_record = fresh_record ()
      }

let build_precise_event_memo = memo build_precise_event

let get_precise_event info =
  let info =
    if get_ignore_types() then
      match info with
        | Action ty -> Action any_type
    else info
  in
  build_precise_event_memo info

(* For integers *)

let has_integer = ref false

(* For choice *)

let choice_fun =
  memo_type (fun t ->
      { f_name = Fixed "choice";
        f_type = [t;t],t;
        f_cat = Choice;
        f_initial_cat = Choice;
        f_private = true;
        f_options = 0;
        f_record = fresh_record () })

let choice_fst_fun =
  memo_type (fun t ->
      { f_name = Fixed "choice-fst";
        f_type = [t;t],t;
        f_cat = ChoiceFst;
        f_initial_cat = ChoiceFst;
        f_private = true;
        f_options = 0;
        f_record = fresh_record () })

let choice_snd_fun =
  memo_type (fun t ->
      { f_name = Fixed "choice-snd";
        f_type = [t;t],t;
        f_cat = ChoiceSnd;
        f_initial_cat = ChoiceSnd;
        f_private = true;
        f_options = 0;
        f_record = fresh_record () })


let has_choice = ref false
let has_barrier = ref false

(* For the saturation and verification of queries *)

let event_lemma_simplification = ref false

let induction_lemmas = ref false
let induction_queries = ref false

let sat_application = ref LAOnlyWhenInstantiate
let verif_application = ref LAFull

let dummy_solve_status =
  {
     s_max_subset = false;
     s_ind_sat_app = LANone;
     s_ind_verif_app = LANone;
     s_induction = false
   }

type nounif_ignore_once_t = NIO_None | NIO_Auto | NIO_All
let nounif_ignore_once = ref NIO_None
let initial_nb_of_nounif_ignore = ref 1

(* Values computed from the input file *)

let types_initial = [channel_type; bitstring_type; bool_type; nat_type]
let dummy_pi_state =
  { pi_process_query = SingleProcess({ proc = Nil; bi_pro = false; display_num = None; construction = Initial_process}, []);
    pi_global_env = Unset;
    pi_glob_table = Unset;
    pi_glob_table_var_name = Unset;
    pi_types = [];
    pi_funs = [];
    pi_freenames = [];
    pi_events = [];
    pi_equations = [];
    pi_max_used_phase = 0;
    pi_all_barrier_tags = [];
    pi_input_clauses = [];
    pi_elimtrue = [];
    pi_equivalence_clauses = [];
    pi_destructors_check_deterministic = [];
    pi_disequations = [];
    pi_event_status_table = Unset;
    pi_get_not = (fun _ -> []);
    pi_get_nounif = (fun _ -> []);
    pi_terms_to_add_in_name_params = Unset;
    pi_min_choice_phase = Unset;
    pi_need_vars_in_names = Function(fun _ -> []);
    pi_name_args_exact = true;
    pi_lemma = [];
    pi_original_axioms = [];
    pi_precise_actions = [];
    pi_originally_lemma = false
  }

let current_state = ref dummy_pi_state

let get_process_query pi_state =
  match pi_state.pi_process_query with
  | SingleProcessSingleQuery(p,q) -> p,q
  | _ -> Parsing_helper.internal_error "SingleProcessSingleQuery expected in get_process_query"

let is_noninterf pi_state =
  match pi_state.pi_process_query with
    SingleProcessSingleQuery(_, NonInterfQuery _) -> true
  | _ -> false

let is_equivalence_two_processes pi_state =
  match pi_state.pi_process_query with
    Equivalence _ -> true
  | _ -> false

let session1 = { f_name = Fixed "@session1";
		 f_type = [], sid_type;
                 f_private = false;
		 f_options = 0;
		 f_cat = Eq [];
	         f_initial_cat = Eq [];
                 f_record = fresh_record () }

let reset_param() =
  (* Do not reset:
     lib_name, tulafale, graph_output, trace_display_graphicx, html_dir,
     command_line_graph_set, command_line_graph, ansi_color, html_output,
     interactive_dot_command
     which are set on the command-line.

     Do not reset:
     verbose_explain_clauses, explain_derivation, abbreviate_clauses, typed_frontend
     which are set before parsing the file in a fairly complicated way
     (depends on -in, -test, -tulafale, -html and the extension of the input file).
     That is not perfect because the values of these parameters may remain
     those of a previous input file instead of the desired value.
     No problem for the interactive simulator, and currently we do not
     load several files in proverif itself.

     Do not reset:
     allow_tilde, trace_win_open
     Used by interactive simulator *)
  bipro_i_mode := false;
  max_depth := (-1);
  max_hyp := (-1);
  max_inequality_chain := (-1);
  active_attacker := true;
  allow_diff_patterns := false;
  allow_private_comm_on_public_terms := true;
  key_compromise := 0;
  ignore_types := NotSet;
  current_query_number := 1;
  derivation_number := 0;
  inside_query_number := 0;
  process_number := 0;
  precise_let_expand := true;
  expand_simplify_if_cst := true;
  simplify_process := 1;
  reject_choice_true_false := true;
  reject_no_simplif := true;
  prove_lemma_only := false;
  verbose_rules := false;
  verbose_base := false;
  verbose_redundant := false;
  verbose_completed := false;
  verbose_eq := true;
  verbose_destr := false;
  verbose_term := true;
  verbose_goal_reachable := true;
  remove_subsumed_clauses_before_display := true;
  reconstruct_derivation := true;
  simplify_derivation := true;
  simplify_derivation_level := AttackerSameTree;
  unify_derivation := true;
  display_derivation := true;
  abbreviate_derivation := true;
  reconstruct_trace := 4;
  trace_backtracking := true;
  display_init_state := true;
  select_fun := TermMaxsize;
  should_stop_term := true;
  redundancy_test := BestRed;
  move_new := false;
  move_let := true;
  redundant_hyp_elim := true;
  redundant_hyp_elim_begin_only := true;
  check_pred_calls := true;
  eq_in_names := false;
  simpeq_all_predicates := false;
  simpeq_final := true;
  eqtreatment := ConvLin;
  symb_order := None;
  trace_display := ShortDisplay;
  interactive_swapping := false;
  set_swapping := None;
  has_choice := false;
  has_barrier := false;
  current_state := dummy_pi_state;
  has_integer := false;
  induction_lemmas := false;
  induction_queries := false;
  sat_application := LAOnlyWhenInstantiate;
  verif_application := LAFull;
  event_lemma_simplification := false;
  nounif_ignore_once := NIO_None;
  precise_actions := NotPrecise;
  feature := true;
  record_funs := true;
  record_names := false;
  record_predicates := true;
  record_events := true;
  record_tables := true;
  record_depth := false;
  record_width := false;
  cleanup_threshold := 10;
  unify_trie_term_max_depth := 5;

  if (!tulafale) = 1 then
    begin
      reconstruct_trace := 0;
      abbreviate_derivation := false;
      redundant_hyp_elim := true;
      redundant_hyp_elim_begin_only := true
    end;
