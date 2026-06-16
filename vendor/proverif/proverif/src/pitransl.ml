open Parsing_helper
open Types
open Pitypes
open Funsymbhash

(* Information computed by [transl], to add to the [pi_state] *)

let terms_to_add_in_name_params = ref []

(* Variables local to this module, used to store elements of the t_horn_state we are going to return *)

(** Indicates the number of rules created *)
let nrule = ref 0
(** List of the rules created *)
let red_rules = ref ([] : reduction list)
let no_gen_var = ref []
let no_unif_set = ref ([] : (fact_format * nounif_value * nounif_op) list)
(* List of precise action events used *)
let current_precise_actions = ref ([] : funsymb list)

let add_in_precise_actions ev =
  if List.memq ev !current_precise_actions
  then ()
  else current_precise_actions := ev :: !current_precise_actions

let add_rule_follow f_next hyp concl constra tags =
  let constra = TermsEq.remove_caught_fail constra in
  let rule = (hyp, concl, Rule (!nrule, tags, hyp, concl, constra), constra) in
  f_next rule;
  incr nrule

let add_rule hyp concl constra tags =
  let constra = TermsEq.remove_caught_fail constra in
  let rule = (hyp, concl, Rule (!nrule, tags, hyp, concl, constra), constra) in
  Database.record_from_rule rule;
  red_rules := rule :: !red_rules;
  incr nrule

let add_no_unif f n for_hyp =
  no_unif_set := (f,n,for_hyp) ::(!no_unif_set)

(* For key compromise *)
let session0 = { f_name = Fixed "@session0";
                 f_type = [], Param.sid_type;
                 f_private = false;
                 f_options = 0;
                 f_cat = Eq [];
                 f_initial_cat = Eq [];
                 f_record = Param.fresh_record ()
               }
let compromised_session = FunApp(session0, [])

let session1 = Param.session1

(* Because [comp_session_var] is created at the very beginning,
   before parsing is initialized, it is named with [name = session, idx = 0]
   and other identifiers may have the same [name,idx]. At the display
   level, they will still be displayed differently, because the fields
   [name,idx] are no longer used for display. *)
let comp_session_var = Terms.new_var ~orig:false "session" Param.sid_type

(* For non-interference *)

let bad_pred = Param.bad_pred

(* Check that predicate calls are implementable *)

let rec get_other_vars other_vars vlist = function
    Var v ->
      if not (List.memq v vlist) then
        other_vars := v :: (!other_vars)
  | FunApp(f,l) ->
      List.iter (get_other_vars other_vars vlist) l

let rec is_ground bound_vars t =
  match t with
    Var v -> List.memq v bound_vars
  | FunApp(f,l) -> List.for_all (is_ground bound_vars) l

let check_constra error_message bound_vars c =
  Terms.iter_constraints (fun t ->
    if not (is_ground !bound_vars t)
    then
      begin
        error_message();
        user_error "In clauses, variables in inequalities, disequalities or equalities should all be bound."
      end
  ) c

let rec binds_vars error_message bound_vars = function
    FunApp(f,l) ->
      begin
        match f.f_cat with
          Tuple -> List.iter (binds_vars error_message bound_vars) l
        | _ ->
            if not (List.for_all (is_ground (!bound_vars)) l) then
              begin
                error_message();
                user_error ("Cannot bind variables under non-data constructors ("
                            ^ (Display.string_of_fsymb f) ^ ").")
              end
            (* Do not bind variables under non-data constructors *)
      end
  | Var v ->
      if not (List.memq v (!bound_vars)) then
        bound_vars := v :: (!bound_vars)

let rec check_fact pi_state error_message seen_pred_calls bound_vars = function
    Pred(p, l) ->
      check_pred pi_state error_message seen_pred_calls (p, List.map (is_ground (!bound_vars)) l);
      List.iter (binds_vars error_message bound_vars) l

and check_pred pi_state error_message seen_pred_calls (p, ground_list) =
  try
    let ground_list_seen = List.assq p seen_pred_calls  in
    if List.exists2 (fun g_seen g -> g_seen && (not g)) ground_list_seen ground_list then
      begin
        error_message();
        user_error ("Too many unbound vars in recursive call to predicate " ^ p.p_name)
      end
  with Not_found ->
    let seen_pred_calls' = (p, ground_list) :: seen_pred_calls in
    List.iter (function
        (hyp, (Pred(p', l') as concl), constra, _) ->
          if p == p' then
            let error_message' () =
              error_message();
              print_string "Clause ";
              Display.Text.display_rule (hyp, concl, Empty concl, constra)
            in
            let error_message'' () =
              error_message'();
              print_string "Conclusion ";
              Display.Text.display_fact concl;
              Display.Text.newline()
            in
            let bound_vars = ref [] in
            List.iter2 (fun t g ->
              if g then binds_vars error_message'' bound_vars t) l' ground_list;
            List.iter (fun f ->
              check_fact pi_state
                (fun () ->
                  error_message'();
                  print_string "Hypothesis ";
                  Display.Text.display_fact f;
                  Display.Text.newline()
                )
                seen_pred_calls' bound_vars f) hyp;
            check_constra
              (fun () ->
                error_message'();
                print_string "Hypothesis ";
                Display.Text.display_constraints constra;
                Display.Text.newline()
              ) bound_vars constra;
            List.iter (fun t ->
              if not (is_ground (!bound_vars) t) then
                begin
                  error_message''();
                  user_error "In the conclusion of a clause, all variables should have been bound by evaluating the hypothesis"
                end) l'
      ) pi_state.pi_input_clauses;
    List.iter (function
        (Pred(p', l') as concl) ->
          if p == p' then
            let error_message' () =
              error_message();
              print_string "Elimtrue fact ";
              Display.Text.display_fact concl;
              Display.Text.newline()
            in
            let bound_vars = ref [] in
            List.iter2 (fun t g ->
              if g then binds_vars error_message' bound_vars t) l' ground_list;
            List.iter (fun t ->
              if not (is_ground (!bound_vars) t) then
                begin
                  error_message'();
                  user_error "In a fact, all variables should have been bound"
                end) l'
      ) pi_state.pi_elimtrue

let check_first_fact pi_state vlist = function
    Pred(p,l) as f ->
      let bound_vars = ref [] in
      List.iter (get_other_vars bound_vars vlist) l;
      let error_message = fun () ->
        print_string "Error while checking implementability of \"";
        begin
          match vlist with
            [] ->
              Display.Text.display_keyword "if"
          | (a::restv) ->
              Display.Text.display_keyword "let";
              print_string (" " ^ (Display.string_of_binder a));
              List.iter (fun v -> print_string (", " ^ (Display.string_of_binder v))) restv;
              print_string " ";
              Display.Text.display_keyword "suchthat"
        end;
        print_string " ";
        Display.Text.display_fact2 f;
        print_string "\"";
        Display.Text.newline()
      in
      List.iter (fun v ->
        if not (List.exists (Terms.occurs_var v) l) then
          begin
            error_message();
            user_error ("Variable " ^ (Display.string_of_binder v) ^ " should occur in the fact.")
          end
                 ) vlist;
      check_fact pi_state error_message [] bound_vars f

type name_param_info =
    arg_meaning * term * when_include
(* arg_meaning: meaning of the argument
   term: to put as parameter of name function symbol
   when_include: indicates when the parameter should be included
*)

type transl_state =
    { tr_pi_state : t_pi_state; (* [pi_state] received as input *)
      hypothesis : fact list; (* Current hypotheses of the rule *)
      constra : constraints; (* Current constraints of the rule *)

      mapping_secret_vars : (funsymb * binder) list;
      (* Used only for non interference. Mapping of the secrets to variables.
         Outside a destructor group, for all (f,x) in the mapping, x should be
         linked to FunApp(f,[]).
      *)

      last_step_variables : binder list;
      (* Variables that were generated in the last group of destructor applications  *)
      last_step_constra : constraints;
      (* Constraints for the last group of destructor applications. *)
      last_step_unif_left : term list;
      last_step_unif_right : term list;
      (* Unifications to do for the last group of destructor applications.
         last_step_unif will be appended to unif before emitting clauses.
         The separation between last_step_unif and unif is useful only
         for non-interference. *)
      neg_success_conditions : constraints ref option ref;
      (* List of constraints that should be false for the evaluation
         of destructors to succeed *)
      name_params : name_param_info list; (* List of parameters of names *)
      repl_count : int;
      (* Session identifier, to include in the parameter of
         end events for injective agreement *)
      current_session_id : binder option;
      is_below_begin : bool;
      cur_phase : int;
      input_pred : predicate;
      output_pred : predicate;
      hyp_tags : hypspec list;

      record_fun_opt : (reduction -> unit) option
      (* When [None], we do not really generate clauses, we just initialize the
         information for the arguments of names created by restrictions
	 and record symbols for features used to index clauses for subsumption.
         When [Some record_fun], we generate the clauses and pass each
         generated clause to the function [record_fun]. *)
    }

(* List recording which occurrence of the process we have already explored.
  Used only in the dummy translation. *)

let explored_occurrences = Hashtbl.create 7

let verify_explored_occurrence cur_state process f_next =
  if cur_state.record_fun_opt <> None
  then f_next ()
  else
    match process with
      | Nil | Par _ | NamedProcess _ -> f_next ()
      | Repl(_,occ) | Restr(_,_,_,occ) | Test(_,_,_,occ)
      | Input(_,_,_,occ) | Output(_,_,_,occ) | Let(_,_,_,_,occ)
      | LetFilter(_,_,_,_,occ) | Event(_,_,_,occ) | Insert(_,_,occ)
      | Get(_,_,_,_,occ) | Phase(_,_,occ) ->
          if Hashtbl.mem explored_occurrences occ.occ
          then ()
          else
            begin
              Hashtbl.add explored_occurrences occ.occ ();
              f_next ()
            end
      | Barrier _ | AnnBarrier _ -> internal_error "[pitransl.ml >> verify_explored_occurrence] Barriers should not appear here."

let att_fact phase t =
  Pred(Param.get_pred (Attacker(phase, Terms.get_term_type t)), [t])

let mess_fact phase tc tm =
  Pred(Param.get_pred (Mess(phase, Terms.get_term_type tm)), [tc;tm])

let table_fact phase t =
  Pred(Param.get_pred (Table(phase)), [t])

let testunif_fact t1 t2 =
  Pred(Param.get_pred (TestUnifP(Terms.get_term_type t1)), [t1;t2])

let pred_phase_0_to_1 p =
  match p.p_info with
  | Attacker(0,ty) -> Param.get_pred (Attacker(1,ty))
  | Mess(0,ty) -> Param.get_pred(Mess(1,ty))
  | Table(0) -> Param.get_pred(Table(1))
  | _ -> p
	
(* With non-interference, all variables mapping to a secret in the state should
   be linked with their secret. Moreover, last_step_variables and last_step_constra
   should be empty. *)
let output_rule cur_state out_fact = match cur_state.record_fun_opt with
  | None ->
      (* We record the symbols from the rule *)
      List.iter Database.record_from_fact (out_fact::cur_state.hypothesis);
      if !Param.key_compromise = 2
      then
        begin
          List.iter (function
            | Pred(p,args) ->
                Database.record_from_fact (Pred(pred_phase_0_to_1 p,args))
          ) (out_fact::cur_state.hypothesis)
        end
  | Some f_rule ->
      let name_params = Reduction_helper.extract_name_params_noneed cur_state.name_params in
      Terms.auto_cleanup (fun _ ->
        assert (cur_state.last_step_unif_left == [] && cur_state.last_step_unif_right == []); (* "last_step_unif should have been appended to unif" *)
        let hyp = List.map Terms.copy_fact2 cur_state.hypothesis in
        let concl = Terms.copy_fact2 out_fact in
        let constra2 = Terms.copy_constra2 cur_state.constra in
        let name_params2 = List.map Terms.copy_term2 name_params in
        Terms.cleanup();
        begin
          try
            TermsEq.simplify_constraints (fun constra3 ->
              add_rule_follow f_rule hyp concl constra3 (ProcessRule(cur_state.hyp_tags, name_params2))
            ) (fun constra3 ->
              let hyp3 = List.map Terms.copy_fact4 hyp in
              let concl3 = Terms.copy_fact4 concl in
              let name_params3 = List.map Terms.copy_term4 name_params2 in
              add_rule_follow f_rule hyp3 concl3 constra3 (ProcessRule(cur_state.hyp_tags, name_params3))
            ) (concl::hyp) constra2
          with TermsEq.FalseConstraint -> ()
        end;
        if !Param.key_compromise = 2 then
          begin
            assert (!Terms.current_bound_vars == []);

            (* substitutes session1 for session0, attacker_p1 for
               attacker_p0 and mess_p1 for mess_p0 *)
            let rec copy_term3 = function
                FunApp(f,l) ->
                  FunApp((if f == session0 then session1 else f),
                         List.map copy_term3 l)
              | Var v -> match v.link with
                  NoLink ->
                    let r = Terms.copy_var v in
                    Terms.link v (VLink r);
                    Var r
                | TLink l -> copy_term3 l
                | VLink r -> Var r
                | _ -> internal_error "unexpected link in copy_term3"
            in
            let copy_fact3 = function
                Pred(chann, t) ->
                  Pred(pred_phase_0_to_1 chann, List.map copy_term3 t)
            in

            let hyp = List.map copy_fact3 cur_state.hypothesis in
            let concl = copy_fact3 out_fact in
            let constra3 = Terms.map_constraints copy_term3 cur_state.constra in
            let name_params3 = List.map copy_term3 name_params in
            Terms.cleanup();
            try
              TermsEq.simplify_constraints (fun constra4 ->
                add_rule_follow f_rule hyp concl constra4 (ProcessRule(cur_state.hyp_tags, name_params3))
              ) (fun constra4 ->
                let hyp4 = List.map Terms.copy_fact4 hyp in
                let concl4 = Terms.copy_fact4 concl in
                let name_params4 = List.map Terms.copy_term4 name_params3 in
                add_rule_follow f_rule hyp4 concl4 constra4 (ProcessRule(cur_state.hyp_tags, name_params4))
              ) (concl::hyp) constra3
            with TermsEq.FalseConstraint -> ()
          end
      )

(* For non-interference *)

(* This reference gathers the variables that have been instantiated during the
   translation of a group destructor. Since Terms.auto_cleanup saves but cleans
   the reference Terms.current_bound_vars, we need to introduce a new list
   with new specific functions for saving and cleaning up.

   Terms.current_bound_vars contains variables bound under the last cleanup.
   current_bound_vars_destructor countains variables bound above the last
   cleanup, but inside the current destructor group. *)
let current_bound_vars_destructor = ref ([] : binder list)

(* [save_bound_vars f] has the same behaviour as Terms.auto_cleanup for the
   reference Terms.current_bound_vars but does not empty the reference
   current_bounds_vars_destructor. Moreover, before running [f], the function
   saves the variables in Terms.current_bound_vars in current_bound_vars_destructor *)
let save_bound_vars f =
  let tmp_bound_vars = !Terms.current_bound_vars in
  let tmp_bound_vars_dest = !current_bound_vars_destructor in
  Terms.current_bound_vars := [];
  current_bound_vars_destructor := List.rev_append tmp_bound_vars !current_bound_vars_destructor;
  try
    let r = f () in
    List.iter (fun v -> v.link <- NoLink) !Terms.current_bound_vars;
    Terms.current_bound_vars := tmp_bound_vars;
    current_bound_vars_destructor := tmp_bound_vars_dest;
    r
  with
    | Terms.Unify | TermsEq.FalseConstraint ->
        List.iter (fun v -> v.link <- NoLink) !Terms.current_bound_vars;
        Terms.current_bound_vars := tmp_bound_vars;
        current_bound_vars_destructor := tmp_bound_vars_dest
    | x ->
        List.iter (fun v -> v.link <- NoLink) !Terms.current_bound_vars;
        Terms.current_bound_vars := tmp_bound_vars;
        current_bound_vars_destructor := tmp_bound_vars_dest;
        raise x

let cleanup_bound_vars f =
  let tmp_bound_vars = !Terms.current_bound_vars in
  let tmp_bound_vars_dest = !current_bound_vars_destructor in
  Terms.current_bound_vars := [];
  current_bound_vars_destructor := [];
  try
    let r = f () in
    List.iter (fun v -> v.link <- NoLink) !Terms.current_bound_vars;
    Terms.current_bound_vars := tmp_bound_vars;
    current_bound_vars_destructor := tmp_bound_vars_dest;
    r
  with
    | Terms.Unify | TermsEq.FalseConstraint ->
        List.iter (fun v -> v.link <- NoLink) !Terms.current_bound_vars;
        Terms.current_bound_vars := tmp_bound_vars;
        current_bound_vars_destructor := tmp_bound_vars_dest
    | x ->
        List.iter (fun v -> v.link <- NoLink) !Terms.current_bound_vars;
        Terms.current_bound_vars := tmp_bound_vars;
        current_bound_vars_destructor := tmp_bound_vars_dest;
        raise x

let get_bound_vars () =
  List.rev_append !Terms.current_bound_vars !current_bound_vars_destructor

let link_mapping_vars (f,v) = Terms.unify (FunApp(f,[])) (Var v)

(* Function unify that takes into account whether or not we need to keep
   equalities into last_step_unif or if we can directly unify them *)

let unify_list f_next cur_state tl1 tl2 =
  if cur_state.record_fun_opt = None
  then f_next cur_state
  else
    if !(cur_state.neg_success_conditions) != None
    then
      (* We cannot apply the syntactic equalities so we add them to last_step_unif *)
      f_next
        { cur_state with
          last_step_unif_left = tl1 @ cur_state.last_step_unif_left;
          last_step_unif_right = tl2 @ cur_state.last_step_unif_right
        }
    else
      save_bound_vars (fun () ->
        List.iter2 Terms.unify tl1 tl2;

        (* We unify the previous element in last_step_unif if there are some *)
        if cur_state.last_step_unif_left != []
        then
          begin
            List.iter2 Terms.unify cur_state.last_step_unif_left cur_state.last_step_unif_right;
            f_next { cur_state with last_step_unif_left = []; last_step_unif_right = [] }
          end
        else f_next cur_state
      )

let unify f_next cur_state t1 t2 =
  if cur_state.record_fun_opt = None
  then f_next cur_state
  else unify_list f_next cur_state [t1] [t2]

(* Raises TermsEq.FalseConstraint when cur_state does not need to be considered
   - When we want to compute the negation of success conditions,
   we need to perform unification modulo the equational theory,
   because in the negation, the inequalities are modulo the
   equational theory.
   - In the case non-interference, the syntactic unifications
   are still performed on the fly, because the values of the secrets
   have been replaced with variables (in begin_destructor_group),
   so the unifications will work even when they work for some values
   of the secrets only.
 *)

let check_feasible f_next check cur_state =
  if !(cur_state.neg_success_conditions) != None
  then
    (* We need to check modulo the equational theory since we are gathering the
       negation of success conditions.
       Note that [check_feasible] is applied during the translation of a destructor
       group. In particular, in the case of non interference, the variables in
       cur_state.mapping_secret_vars are not linked to their secret. *)
    try
      let last_constra = TermsEq.simple_simplify_constraints cur_state.last_step_constra in
      let constra' = Terms.wedge_constraints last_constra cur_state.constra in
      TermsEq.unify_modulo_list (fun () ->
        try
          TermsEq.check_constraints constra';
        with TermsEq.FalseConstraint -> raise Terms.Unify
      ) cur_state.last_step_unif_left cur_state.last_step_unif_right;

      f_next { cur_state with last_step_constra = last_constra }
    with Terms.Unify | TermsEq.FalseConstraint -> ()
  else
    (* In such a case, we do not need to check for unification modulo the equational
       theory since we're not gathering the negation of success consitions.
       Note that [check_feasible] is applied during the translation of a destructor
       group. In particular, in the case of non interference, the variables in
       cur_state.mapping_secret_vars are not linked to their secret. *)

    let check_constraints () =
      if Param.is_noninterf cur_state.tr_pi_state
      then
        begin
          (* We need to keep separated last_step_constra from constra *)
          let last_constra = TermsEq.simple_simplify_constraints cur_state.last_step_constra in
          TermsEq.check_constraints (Terms.wedge_constraints last_constra cur_state.constra);
          f_next
            { cur_state with
              last_step_unif_left = [];
              last_step_unif_right = [];
              last_step_constra = last_constra
            }
        end
      else
        (* We can regroup last_step_constra and constra since the query is not
           non interference *)
        f_next
          { cur_state with
            constra = TermsEq.simple_simplify_constraints (Terms.wedge_constraints cur_state.last_step_constra cur_state.constra);
            last_step_unif_left = [];
            last_step_unif_right = [];
            last_step_constra = Terms.true_constraints
          }
    in

    if cur_state.last_step_unif_left != []
    then
      save_bound_vars (fun () ->
        List.iter2 Terms.unify cur_state.last_step_unif_left cur_state.last_step_unif_right;
        check_constraints ()
      )
    else
      if check
      then try check_constraints () with TermsEq.FalseConstraint -> ()
      else f_next cur_state

(*let check_feasible f_next check cur_state = record_time time_check_feasible (fun () -> check_feasible f_next check cur_state)*)

let wedge_constraints cur_state constra =
  if Param.is_noninterf cur_state.tr_pi_state || !(cur_state.neg_success_conditions) != None
  then { cur_state with last_step_constra = Terms.wedge_constraints constra cur_state.last_step_constra }
  else { cur_state with constra = Terms.wedge_constraints constra cur_state.constra }

(* End destructor group *)

let end_destructor_group_no_test_unif next_f cur_state =
  if cur_state.record_fun_opt = None
  then next_f cur_state
  else
    cleanup_bound_vars (fun () ->
      (* We unify the secrets with their variables. If the unification fails,
      then we can remove this branch. Similarly, we simplify the constraints
      and remove the branch if it fails. *)
      List.iter link_mapping_vars cur_state.mapping_secret_vars;

      (* We also unify the last step unif (does nothing when neg_success_conditions = None *)
      List.iter2 Terms.unify cur_state.last_step_unif_left cur_state.last_step_unif_right;

      (* Check that constraints are still satisfiable.
         We check all constraints and not only the new ones, because
         the old constraints may have been modified by unification,
         so they may no longer be satisfiable. *)
      let constra = TermsEq.simple_simplify_constraints (Terms.wedge_constraints cur_state.last_step_constra cur_state.constra) in

      next_f
        { cur_state with
          last_step_constra = Terms.true_constraints;
          last_step_variables = [];
          last_step_unif_left = [];
          last_step_unif_right = [];
          constra = constra;
          neg_success_conditions = ref None
        }
    )

let noninterf_equalities cur_state occ eq_left eq_right =
  (* Output the rule *)
  let tuple_fun = Terms.get_tuple_fun (List.map Terms.get_term_type eq_left) in
  let new_hyp = testunif_fact (FunApp(tuple_fun, eq_left)) (FunApp(tuple_fun, eq_right)) in
  output_rule { cur_state with
            hypothesis = new_hyp :: cur_state.hypothesis;
            hyp_tags = TestUnifTag(occ) :: cur_state.hyp_tags;
            last_step_variables = [];
            last_step_constra = Terms.true_constraints;
            last_step_unif_left = [];
            last_step_unif_right = [] } (Pred(bad_pred, []))

let noninterf_constraints cur_state secret_not_applied occ =
  (** Second, output the rule for constraints *)
  if cur_state.last_step_constra.is_nat != [] || cur_state.last_step_constra.is_not_nat != [] || cur_state.last_step_constra.geq != []
  then Parsing_helper.user_error "Natural numbers do not work with non-interference yet.";

  Terms.auto_cleanup (fun () ->
    try
      if secret_not_applied
      then
        (* We unify the secrets with their variables *)
        List.iter link_mapping_vars cur_state.mapping_secret_vars;

      (* We unify the last_step_unif (does nothing when neg_success_conditions = None) *)
      List.iter2 Terms.unify cur_state.last_step_unif_left cur_state.last_step_unif_right;

      List.iter (fun constra_neq ->
        let (l1,l2) = List.split constra_neq in
        let tuple_fun = Terms.get_tuple_fun (List.map Terms.get_term_type l1) in
        let new_hyp = testunif_fact (FunApp(tuple_fun, l1)) (FunApp(tuple_fun, l2)) in
        output_rule
          { cur_state with
            hypothesis = new_hyp :: cur_state.hypothesis;
            hyp_tags = TestUnifTag(occ) :: cur_state.hyp_tags;
            last_step_variables = [];
            last_step_constra = Terms.true_constraints;
            last_step_unif_left = [];
            last_step_unif_right = []
          } (Pred(bad_pred, []))
      ) cur_state.last_step_constra.neq

    with Terms.Unify -> ()
  )

let noninterf_record_symbol cur_state =
  List.iter Database.record_from_fact cur_state.hypothesis;
  Database.record_predicate (Param.get_pred (TestUnifP Param.bitstring_type))

let end_destructor_group next_f occ cur_state =
  end_destructor_group_no_test_unif next_f cur_state;

  if cur_state.record_fun_opt = None
  then (if Param.is_noninterf cur_state.tr_pi_state then noninterf_record_symbol cur_state)
  else
    if (Param.is_noninterf cur_state.tr_pi_state) || (!(cur_state.neg_success_conditions) != None)
    then
      check_feasible (fun cur_state1 ->
        match !(cur_state1.neg_success_conditions) with
        | None ->
            (* We need to apply non interference *)
            let bound_vars = get_bound_vars () in

            let vars_links =
              List.map (fun v ->
                let l = v.link in
                v.link <- NoLink;
                (v,l)
              ) bound_vars
            in

            (* When bound_vars = [], there is no instantiated variable and so
               there is no need to create the non interference rule for equality.
               There may still be constraints in last_step_constra. *)
            if bound_vars != []
            then
              Terms.auto_cleanup (fun () ->
                try
                  (* We unify the secrets with their variables *)
                  List.iter link_mapping_vars cur_state1.mapping_secret_vars;

                  (* Retrieve the equations and replace the variables from last_step_variables
                     by universal variables *)
                  let (eq_left,eq_right) =
                    Terms.auto_cleanup (fun _ ->
                      List.fold_right (fun (v,link) (acc_l,acc_r) -> match link with
                        | TLink t ->
                            let t' = Terms.copy_term4 t in
                            let t_left = Terms.generalize_vars_in cur_state1.last_step_variables (Var v) in
                            let t_right = Terms.generalize_vars_in cur_state1.last_step_variables t' in
                            (t_right::acc_l,t_left::acc_r)
                        | _ -> Parsing_helper.internal_error "[pitransl.ml >> end_destructor_group] Variables should be linked."
                      ) vars_links ([],[])
                    )
                  in

                  (* Create the rule *)
                  noninterf_equalities cur_state occ eq_left eq_right;
                with Terms.Unify | TermsEq.FalseConstraint -> Parsing_helper.internal_error "[pitransl.ml >> end_destructor_group] The unification should not fail (they were true at the beginning of the group and should be at the end)"
              );

            (* Put back the links *)
            List.iter (fun (v,l) -> v.link <- l) vars_links;

            (* Create the rule for constraints *)
            noninterf_constraints cur_state true occ
        | Some r ->
            assert (get_bound_vars () = []);

            Terms.auto_cleanup (fun () ->
              try
                (* We unify the secrets with their variables *)
                List.iter link_mapping_vars cur_state1.mapping_secret_vars;

                (* First compute the generalization of last_step_unif *)
                let (eq_left,eq_right) =
                  if cur_state.last_step_unif_left != []
                  then
                    Terms.auto_cleanup (fun () ->
                      List.fold_left2 (fun (acc_l,acc_r) tl tr ->
                        (Terms.generalize_vars_in cur_state.last_step_variables tl)::acc_l,(Terms.generalize_vars_in cur_state.last_step_variables tr)::acc_r
                      ) ([],[]) cur_state1.last_step_unif_left cur_state1.last_step_unif_right
                    )
                  else [],[]
                in

                (* We first update the success conditions *)
                if Terms.is_true_constraints cur_state1.last_step_constra then
                  (* The success condition contains no inequality,
                     we store in cur_state.neg_success_conditions the
                     negation of the unifications, to serve to detect failure *)

                  let new_neq_disj = List.map2 (fun t1 t2 -> (t1,t2)) eq_left eq_right in
                  r := { !r with neq = new_neq_disj :: (!r).neq }
                else
                  (* The success condition contains an inequality.
                     Taking its negation is too complicated,
                     we forget about neg_success_conditions, and will
                     compute the failure condition in another way. *)
                  cur_state1.neg_success_conditions := None;

                (* Treat the non-interference *)
                if Param.is_noninterf cur_state1.tr_pi_state
                then
                  begin
                    if cur_state1.last_step_unif_left != []
                    then noninterf_equalities cur_state occ eq_left eq_right;

                    noninterf_constraints cur_state false occ
                  end
              with Terms.Unify | TermsEq.FalseConstraint  -> Parsing_helper.internal_error "[pitransl.ml >> end_destructor_group] The unification should not fail (they were true at the beginning of the group and should be at the end) (2)"
            )
      ) true cur_state

let begin_destructor_group next_f cur_state =
  if cur_state.record_fun_opt = None
  then next_f cur_state
  else
    if Param.is_noninterf cur_state.tr_pi_state
    then
      (* In the case of non interference, before starting the translation of a destructor group,
         the variables in cur_state.mapping_secret_vars are linked to the secrets.
         We need to remove these links. Moreover, we also have that current_bound_vars_destructor
         should be empty. *)
      begin
        assert(!current_bound_vars_destructor = []);
        let mapping = List.map (fun (f,v) ->
          let rec get_var v =
            match v.link with
            | TLink(FunApp(f',[])) when f == f' -> v
            | TLink(Var v') -> get_var v'
            | _ -> Parsing_helper.internal_error "[pitransl.ml >> begin_destructor_group] The mapping variables should be linked with their symlbol."
          in
          let v' = get_var v in
          v'.link <- NoLink;
          (f,v')
            ) cur_state.mapping_secret_vars
        in
        Terms.auto_cleanup (fun () ->
          next_f cur_state
        );
        List.iter (fun (f,v) -> v.link <- TLink(FunApp(f,[]))) mapping
      end
    else
      Terms.auto_cleanup (fun () ->
        next_f cur_state
      )

(* Decide when to optimize mess(c,M) into attacker(M) *)

let optimize_mess cur_state tc =
  let rec is_public_term = function
    | Var({ link = TLink t; _}) -> is_public_term t
    | FunApp({ f_cat = Name _; f_private = false },_) -> true
    | FunApp({ f_cat = Eq _; f_private = false; _ }, args)
    | FunApp({ f_cat = Tuple; _}, args) -> List.for_all is_public_term args
    | _ -> false
  in
  !Param.active_attacker &&
  (is_public_term tc) &&
  ((not (!Param.allow_private_comm_on_public_terms)) ||
   (not (Reduction_helper.prove_att_phase cur_state.tr_pi_state cur_state.cur_phase)))

(* Functions that modify last_step_unif, and that should
   therefore be followed by a call to end_destructor_group

   transl_term
   transl_term_list
   transl_term_incl_destructor
   transl_term_list_incl_destructor
   transl_pat
   transl_fact

*)

(* Translate term *)

let check_feasible_rewrite_rules f_next check args_rw_list cur_state =
  if Param.is_noninterf cur_state.tr_pi_state || !(cur_state.neg_success_conditions) != None
  then
    let vars = ref [] in
    List.iter (Terms.get_vars vars) args_rw_list;
    check_feasible f_next check { cur_state with last_step_variables = !vars @ cur_state.last_step_variables }
  else check_feasible f_next check cur_state

let rec retrieve_rw_rules_at_pos acc_c acc_e pos = function
  | (ToCheck(i,_),_) as s :: q when i = pos ->
      retrieve_rw_rules_at_pos (s::acc_c) acc_e pos q
  | (ToExecute i,rw) :: q when i = pos ->
      retrieve_rw_rules_at_pos acc_c (rw::acc_e) pos q
  | q -> acc_c, acc_e, q

(* In the call [transl_rewrite_rules next_f cur_state check transl_args args pos rules],
    - [pos] represents the index of the latest argument translated. It starts at 0, i.e. no argument translated.
    - [transl_args] is the list of resulting translated argument. We always have [List.length transl_args = pos].
      Note that the order of arguments are preserved, i.e. the first element of [transl_args] corresponds to the
      first argument.
    - [args] is the list of arguments remaining to be translated
    - [rules] are the rewrite rules that still require translation.
    - [check] indicates whether we should check the satisfiability of the constraints.
*)
let rec transl_rewrite_rules next_f cur_state check transl_args args pos rules =
  if List.for_all (function
    | ToExecute i, _ when pos < i -> true
    | _ -> false
    ) rules
  then transl_rewrite_rules_execute next_f cur_state transl_args args pos rules
  else
    match rules with
      | [] -> ()
      | (ToCheck(i,_),_)::_
      | (ToExecute i, _):: _ when pos > i -> Parsing_helper.internal_error "[pitransl.ml >> transl_rewrite_rules] Should have been handled before";
      | (ToCheck(i,_),_)::_
      | (ToExecute i,_)::_ when pos < i ->
          (* All rules require to translate the next argument *)
          let t = List.hd args in
          transl_term (fun cur_state1 t1 ->
            transl_rewrite_rules next_f cur_state1 check (transl_args@[t1]) (List.tl args) (pos+1) rules
              ) cur_state t
      | _ ->
          let check_rules, execute_rules, others = retrieve_rw_rules_at_pos [] [] pos rules in
          let others1 = ref others in

	  List.iter (function
	    | ToCheck(i,j),((left_list, right, side_c) as rw) ->
                (* i = pos hence we need to check if the rule is applicable *)

                (* We retrieve the [pos] first arguments of the rewrite rule. *)
		let left_list_to_check =
		  if args = []
		  then left_list (* Since args = [], all terms have been translated. *)
		  else Reduction_helper.get_until_pos pos left_list
		in

		if i = j
		then
                  (* Since i = j, we don't need to translate more arguments to know
		     the result of the application of the rewrite rule. *)
		  if i = 0
		  then
                    (* This corresponds to the case where we have a rewrite rule of the form f(v1,...,vn) -> c
                       where v_1 ... v_n are distinct may fail variables and c is a constant. *)
                    next_f cur_state right
		  else
                    (* We unify the arguments of the rewrite rules with the translated
		       arguments to obtain the result of the application
                       of the rewrite rule *)
                    unify_list (fun cur_state1 ->
                      let cur_state2 = wedge_constraints cur_state1 side_c in
                      check_feasible_rewrite_rules (fun cur_state3 -> next_f cur_state3 right) check left_list_to_check cur_state2
			) cur_state transl_args left_list_to_check

		else
                  (* In such a case, we cannot yet obtain the result of the
		     application of the rewrite rule but we can already check
		     if the rewrite rule is applicable or not. *)
		  let is_applicable = ref false in

		  unify_list (fun cur_state1 ->
                    let cur_state2 = wedge_constraints cur_state1 side_c in
                    check_feasible_rewrite_rules (fun _ -> is_applicable := true) check left_list_to_check cur_state2
		      ) cur_state transl_args left_list_to_check;

		  if !is_applicable
		  then others1 := Terms.add_in_sorted_status (ToExecute j,rw) !others1
	    | _ -> Parsing_helper.internal_error "[pitransl.ml >> transl_rewrite_rules_one_side] should only contain ToCheck"
		  ) check_rules;

	  (* Execute *)
	  List.iter (fun (left_list, right, side_c) ->
            (* i = pos hence we can apply the rewrite rule.
               We do not need to create a fresh rule. It was done in the call to [Terms.get_all_rewrite_rules_status] in [trans_term]. *)
            let left_list_to_check =
              if args = []
              then left_list (* Since args = [], all terms have been translated. *)
              else Reduction_helper.get_until_pos pos left_list
            in

            unify_list (fun cur_state1 ->
              let cur_state2 = wedge_constraints cur_state1 side_c in
              (* We put the check variable to false since the check of constraints
               was done when handling ToCheck(i,j). We could still check the constraints
               too but i think it is superfleous. *)
              check_feasible_rewrite_rules (fun cur_state3 -> next_f cur_state3 right) false left_list_to_check cur_state2
		) cur_state transl_args left_list_to_check
	      ) execute_rules;

          transl_rewrite_rules next_f cur_state check transl_args args pos !others1

and transl_rewrite_rules_execute next_f cur_state transl_args args pos rules = match rules with
  | [] -> ()
  | (ToExecute i,_)::q ->
      let (check_rules,same_to_execute,other_to_execute) = retrieve_rw_rules_at_pos [] [] i rules in
      if check_rules <> []
      then Parsing_helper.internal_error "[pitransl.ml >> transl_rewrite_rules_one_side_execute] The list should not contain ToCheck.";

      let t_to_translate = List.nth args (i-pos-1) in
      transl_term (fun cur_state1 t1 ->
        List.iter (fun (left_list,right,side_c) ->
          let left_list_to_check = Reduction_helper.get_until_pos pos left_list in
          unify_list (fun cur_state2 ->
            let cur_state3 = wedge_constraints cur_state2 side_c in
            (* We put the check variable to false since the check of constraints
               was done when handling ToCheck(i,j). We could still check the constraints
               too but i think it is superfleous. *)
            check_feasible_rewrite_rules (fun cur_state4 -> next_f cur_state4 t1) false (right::left_list_to_check) cur_state3
          ) cur_state1 (t1::transl_args) (right::left_list_to_check)
        ) same_to_execute
      ) cur_state t_to_translate;

      transl_rewrite_rules_execute next_f cur_state transl_args args pos other_to_execute
  | _ -> Parsing_helper.internal_error "[pitransl.ml >> transl_rewrite_rules_execute] Unexpected case."

(* next_f takes a state and a pattern as parameter *)
and transl_term next_f cur_state = function
    Var v ->
      begin
        match v.link with
          TLink t -> next_f cur_state t
        | _ -> internal_error ("unexpected link in transl_term "^Display.string_of_binder v)
      end
  | FunApp(f,l) ->
      let transl_red check =
        if l = []
        then
          (* In such a case, all rules are of the form f -> a *)
          let red_rules = Terms.red_rules_fun f in
          List.iter (fun (_,t,_) -> next_f cur_state t) red_rules
        else transl_rewrite_rules next_f cur_state check [] l 0 (Terms.get_all_rewrite_rules_status f)
      in
      match f.f_cat with
        Name n ->
          begin
            match n.prev_inputs with
              Some t -> next_f cur_state t
            | _ -> internal_error "unexpected prev_inputs in transl_term"
          end
      | Tuple | Eq [] | Failure -> transl_red false
      | Red _ | Eq _ -> transl_red true
      | _ -> Parsing_helper.internal_error "function symbols of these categories should not appear in input terms (pitransl)"

let transl_term next_f cur_state t =
  if cur_state.record_fun_opt = None
  then next_f cur_state t
  else transl_term next_f cur_state t

(* next_f takes a state and a list of patterns as parameter *)
let rec transl_term_list next_f cur_state = function
    [] -> next_f cur_state []
  | (a::l) ->
      transl_term (fun cur_state1 p ->
        transl_term_list (fun cur_state2 patlist ->
          next_f cur_state2 (p::patlist)) cur_state1 l) cur_state a

let transl_term_incl_destructor f cur_state occ t =
  let may_have_several_types = Reduction_helper.transl_check_several_patterns terms_to_add_in_name_params occ t in
  transl_term (fun cur_state1 pat1 ->
    if may_have_several_types then
      f { cur_state1 with name_params = (MUnknown, pat1, Always)::cur_state1.name_params } pat1
    else
      f cur_state1 pat1
    ) cur_state t

let transl_term_list_incl_destructor f cur_state occ tl =
  let may_have_several_types = List.exists (Reduction_helper.transl_check_several_patterns terms_to_add_in_name_params occ) tl in
  transl_term_list (fun cur_state1 patlist ->
    if may_have_several_types then
      f { cur_state1 with
          name_params = (List.map2 (fun t pat -> (MUnknown, pat, Always)) tl patlist) @ cur_state1.name_params } patlist
    else
      f cur_state1 patlist
    ) cur_state tl

(* Detect failure *)

let no_fail next_f cur_state t =
  if cur_state.record_fun_opt = None
  then next_f cur_state t
  else
    let x = Terms.new_var_def (Terms.get_term_type t) in
    unify (fun cur_state1 ->
      next_f { cur_state1 with last_step_variables = x :: cur_state1.last_step_variables } t
    ) cur_state t (Var x)

let no_fail_list next_f cur_state tl =
  if cur_state.record_fun_opt = None
  then next_f cur_state tl
  else
    let xl = List.map (fun t -> Terms.new_var_def (Terms.get_term_type t)) tl in
    let xl_term = List.map (fun x -> Var x) xl in
    unify_list (fun cur_state1 ->
      next_f { cur_state with last_step_variables = xl @ cur_state.last_step_variables } tl
    ) cur_state tl xl_term

let must_fail next_f cur_state t =
  if cur_state.record_fun_opt = None
  then next_f cur_state
  else
    let fail = Terms.get_fail_term (Terms.get_term_type t) in
    unify next_f cur_state t fail

(* Translate pattern *)

let rec transl_pat put_var f cur_state pat =
  match pat with
    PatVar b ->
      let b' = Terms.copy_var b in
      let pat' = Var b' in
      b.link <- TLink pat';
      let cur_state1 =
        { cur_state with
          name_params = (MVar(b, None), pat', put_var) :: cur_state.name_params;
          last_step_variables = b' :: cur_state.last_step_variables
        }
      in
      f cur_state1 (Var b');
      b.link <- NoLink
  | PatTuple (fsymb,pat_list) ->
      transl_pat_list put_var (fun cur_state2 term_list ->
        f cur_state2 (FunApp(fsymb, term_list))
          ) cur_state pat_list;
  | PatEqual t ->
      transl_term (no_fail f) cur_state t

and transl_pat_list put_var f cur_state = function
    [] -> f cur_state []
  | p::pl ->
      (* It is important to translate the head first, like the head is
         checked first in pisyntax.ml, because variables may be bound in the
         head and used in equality tests in the tail *)
      transl_pat put_var (fun cur_state2 term ->
        transl_pat_list put_var (fun cur_state3 term_list ->
          f cur_state3 (term::term_list)
            ) cur_state2 pl
          ) cur_state p

(* Function Not Used *)
(*
let rec transl_unif next_f cur_state accu = function
    [] -> next_f { cur_state with
                   last_step_constra = accu :: cur_state.last_step_constra }
  | (p,t)::l ->
      (* We have a term =t in the pattern, and its expected value is p *)
      transl_term (fun cur_state' t' ->
        (* t fails *)
        must_fail next_f cur_state' t';
        (* t does not fail, it is different from its expected value p *)
        no_fail (fun cur_state'' _ ->
          transl_unif next_f cur_state'' ((Neq(p, t'))::accu) l
            ) cur_state' t'
          ) cur_state t
*)

(* Handles the case in which one the terms =M in the pattern fails *)

let rec transl_pat_fail_term next_f cur_state = function
    PatVar b -> ()
  | PatTuple(f,l) ->
      List.iter (transl_pat_fail_term next_f cur_state) l
  | PatEqual t ->
      (* t fails *)
      transl_term (must_fail next_f) cur_state t

(* Handles the case in which the terms =M in the pattern succeed,
   but the result does not match
   [transl_pat_fail_rec] calls [next_f] with the current state
   and a term that represents the pattern, with general variables
   instead of variables bound by the pattern. *)

let rec transl_pat_fail_rec next_f cur_state = function
    PatVar b ->
      let gvar = Terms.new_gen_var b.btype false in
      next_f cur_state (FunApp(gvar, []));
  | PatTuple (fsymb,pat_list) ->
      transl_pat_fail_list (fun cur_state gen_list ->
        next_f cur_state (FunApp(fsymb, gen_list))
          ) cur_state pat_list
  | PatEqual t ->
      (* term t succeeds *)
      transl_term (no_fail next_f) cur_state t

and transl_pat_fail_list next_f cur_state = function
    [] -> next_f cur_state []
  | p::pl ->
      transl_pat_fail_rec (fun cur_state1 gen ->
        transl_pat_fail_list (fun cur_state2 gen_list ->
          next_f cur_state2 (gen::gen_list)
            ) cur_state1 pl
        ) cur_state p

let transl_pat_fail next_f cur_state pat pat' =
  (* one the terms =M in the pattern fails *)
  transl_pat_fail_term next_f cur_state pat;
  (* the terms =M in the pattern succeed, but the result does not match *)
  transl_pat_fail_rec (fun cur_state1 pat_gen ->
    next_f { cur_state1 with
             last_step_constra = { cur_state1.last_step_constra with neq = [pat_gen, pat']::cur_state1.last_step_constra.neq } };
      ) cur_state pat

(* Translate fact *)

let transl_fact next_fun cur_state occ f =
  match f with
  | Pred(p,tl) ->
      transl_term_list_incl_destructor (no_fail_list (fun cur_state1 patl ->
        next_fun (Pred(p,patl)) cur_state1)) cur_state occ tl

(* Translate process *)

let get_occurrence_name_for_precise cur_state occ =
  let name_params = cur_state.name_params in
  let (np, npm) =
    List.fold_right (fun (m,t,_) (acc_np,acc_npm) -> match m with
      | MSid _ -> (t::acc_np,m::acc_npm)
      | _ -> (acc_np,acc_npm)
    ) name_params ([],[])
  in
  let n = Reduction_helper.get_occ_name occ in
  (* Fix now how the name [n] is displayed, to avoid different
     displays in different clauses/derivations *)
  let n_string = Display.string_of_fsymb n in
  match n.f_cat with
    | Name r ->
        let nptype = List.map Terms.get_term_type np in
        if fst n.f_type == Param.tmp_type then
          begin
            n.f_type <- nptype, snd n.f_type;
            r.prev_inputs_meaning <- npm
          end
        else if Param.get_ignore_types() then
          begin
            (* When we ignore types, the types of the arguments may vary,
               only the number of arguments is preserved. *)
            if List.length (fst n.f_type) != List.length nptype then
              internal_error ("Name " ^ n_string ^ " has bad arity")
          end
        else
          begin
            if not (Terms.eq_lists (fst n.f_type) nptype) then
              internal_error ("Name " ^ n_string ^ " has bad type")
          end;

        FunApp(n,np)
    | _ -> internal_error "[pitransl.ml >> get_occurrence_name_for_precise] Unexpected function category in the translation of events."

let rec transl_process cur_state process =
  verify_explored_occurrence cur_state process (fun () -> match process with
    | Nil -> ()
    | NamedProcess(_, _, p) -> transl_process cur_state p
    | Par(p,q) ->
        transl_process cur_state p;
        transl_process cur_state q
    | Repl (p,occ) ->
        let cur_state = { cur_state with repl_count = cur_state.repl_count + 1 } in
        let sid_meaning = MSid cur_state.repl_count in
        (* Always introduce session identifiers ! *)
        let cur_state = { cur_state with is_below_begin = false } in
        let v = Terms.new_var ~orig:false (if !Param.tulafale != 1 then "@sid" else "sid") Param.sid_type in
        let count_params = Reduction_helper.count_name_params cur_state.name_params in
        begin
         if Param.is_noninterf cur_state.tr_pi_state then
           begin
             if (!Param.key_compromise == 0) then
               transl_process { cur_state with
                                hypothesis = (att_fact cur_state.cur_phase (Var v)) :: cur_state.hypothesis;
                                current_session_id = Some v;
                                name_params = (sid_meaning, Var v, Always) :: cur_state.name_params;
                                hyp_tags = (ReplTag(occ, count_params)) :: cur_state.hyp_tags
                              } p
             else if (!Param.key_compromise == 1) then
               transl_process { cur_state with
                                hypothesis = (att_fact cur_state.cur_phase (Var v)) :: (att_fact cur_state.cur_phase (Var comp_session_var)) :: cur_state.hypothesis;
                                current_session_id = Some v;
                                name_params = (MCompSid, Var comp_session_var, Always) ::
                                   (sid_meaning, Var v, Always) :: cur_state.name_params;
                                hyp_tags = (ReplTag(occ, count_params)) :: cur_state.hyp_tags
                              } p
             else
               transl_process { cur_state with
                                hypothesis = (att_fact cur_state.cur_phase (Var v)) :: cur_state.hypothesis;
                                current_session_id = Some v;
                                name_params = (MCompSid, compromised_session, Always) ::
                                   (sid_meaning, Var v, Always) :: cur_state.name_params;
                                hyp_tags = (ReplTag(occ, count_params)) :: cur_state.hyp_tags
                              } p
           end
         else
           begin
             if (!Param.key_compromise == 0) then
               transl_process { cur_state with
                                current_session_id = Some v;
                                name_params = (sid_meaning, Var v, Always) :: cur_state.name_params;
                                hyp_tags = (ReplTag(occ, count_params)) :: cur_state.hyp_tags
                              } p
             else if (!Param.key_compromise == 1) then
               transl_process { cur_state with
                                current_session_id = Some v;
                                name_params = (MCompSid, Var comp_session_var, Always) ::
                                   (sid_meaning, Var v, Always) :: cur_state.name_params;
                                hyp_tags = (ReplTag(occ, count_params)) :: cur_state.hyp_tags
                              } p
             else
               transl_process { cur_state with
                                current_session_id = Some v;
                                name_params = (MCompSid, compromised_session, Always) ::
                                   (sid_meaning, Var v, Always) :: cur_state.name_params;
                                hyp_tags = (ReplTag(occ, count_params)) :: cur_state.hyp_tags
                              } p
           end
        end
    | Restr(n,(args, env),p,_) ->
       begin
         let need_list = Reduction_helper.get_need_vars cur_state.tr_pi_state n in
         let include_info = Reduction_helper.prepare_include_info env args need_list in
         let name_params = cur_state.name_params in
         let npm = Reduction_helper.extract_name_params_meaning n include_info name_params in
         let np = Reduction_helper.extract_name_params n include_info name_params in
         match n.f_cat with
          Name r ->
           let nptype = List.map Terms.get_term_type np in
           if fst n.f_type == Param.tmp_type then
             begin
	       (* The arguments of names should all be set in the first dummy translation *)
	       assert (cur_state.record_fun_opt = None);
               n.f_type <- nptype, snd n.f_type;
               r.prev_inputs_meaning <- npm
             end
           else if Param.get_ignore_types() then
             begin
               (* When we ignore types, the types of the arguments may vary,
                  only the number of arguments is preserved. *)
               if List.length (fst n.f_type) != List.length nptype then
                 internal_error ("Name " ^ (Display.string_of_fsymb n) ^ " has bad arity")
             end
           else
             begin
               if not (Terms.eq_lists (fst n.f_type) nptype) then
                 internal_error ("Name " ^ (Display.string_of_fsymb n) ^ " has bad type")
             end;
           r.prev_inputs <- Some (FunApp(n, np));
           transl_process cur_state p;
           r.prev_inputs <- None
          | _ -> internal_error "A restriction should have a name as parameter"
       end
    | Test(t,p,q,occ) ->
        if q == Nil
        then
          (* We optimize the case q == Nil.
             In this case, the adversary cannot distinguish the situation
             in which t fails from the situation in which t is false. *)
          begin_destructor_group (fun cur_state0 ->
            transl_term_incl_destructor (no_fail (fun cur_state1 pat1 ->
              unify (fun cur_state2 ->
                end_destructor_group (fun cur_state3 ->
                  transl_process { cur_state3 with
                                   hyp_tags = (TestTag occ) :: cur_state3.hyp_tags } p
                ) occ cur_state2
              ) cur_state1 pat1 Terms.true_term
            )) cur_state0 (OTest(occ)) t
          ) cur_state
        else
          begin_destructor_group (fun cur_state0 ->
            transl_term_incl_destructor (no_fail (fun cur_state1 pat1 ->
              end_destructor_group (fun cur_state2 ->
                if Param.is_noninterf cur_state2.tr_pi_state then
                  output_rule { cur_state2 with
                                hypothesis = (testunif_fact pat1 Terms.true_term) :: cur_state2.hypothesis;
                                hyp_tags = TestUnifTag(occ) :: cur_state2.hyp_tags
                              } (Pred(bad_pred, []));

                Terms.auto_cleanup (fun _ ->
                  try
                    if cur_state2.record_fun_opt <> None then
		      Terms.unify pat1 Terms.true_term;
                    transl_process { cur_state2 with
                                     hyp_tags = (TestTag occ) :: cur_state2.hyp_tags } p
                  with Terms.Unify -> ()
                );
                Terms.auto_cleanup (fun _ ->
                  try
                    let constra' = { cur_state2.constra with neq = [pat1, Terms.true_term]::cur_state2.constra.neq } in
                    if cur_state2.record_fun_opt <> None then
                      TermsEq.check_constraints constra';
                    transl_process { cur_state2 with
                                     constra = constra';
                                     hyp_tags = (TestTag occ) :: cur_state2.hyp_tags } q
                  with Terms.Unify | TermsEq.FalseConstraint -> ()
                )
              ) occ cur_state1
            )) cur_state0 (OTest(occ)) t
           ) cur_state
    | Input(tc,pat,p,occ) ->
        if optimize_mess cur_state tc then
          begin
            begin_destructor_group (fun cur_state0 ->
              let x = Reduction_helper.new_var_pat pat in
              transl_pat Always (fun cur_state1 pat1 ->
                unify (fun cur_state2 ->
                  let cur_state3 =
                    if cur_state2.is_below_begin || occ.precise || Param.get_precise()
                    then
                      begin
                        let occ_name = get_occurrence_name_for_precise cur_state2 occ in
                        let ev = Param.get_precise_event (Action (Terms.get_term_type x)) in
                        Reduction_helper.add_precise_info_occ occ (Action (Terms.get_term_type x));
                        add_in_precise_actions ev;
                        { cur_state2 with
                          hypothesis = (att_fact cur_state2.cur_phase x) :: (Pred(Param.event_pred_block,[FunApp(ev,[occ_name;x])])) :: cur_state2.hypothesis;
                          hyp_tags = (InputTag(occ)) :: (PreciseTag(occ)) ::cur_state2.hyp_tags
                        }
                      end
                    else
                      { cur_state2 with
                        hypothesis = (att_fact cur_state2.cur_phase x) :: cur_state2.hypothesis;
                        hyp_tags = (InputTag(occ)) :: cur_state2.hyp_tags
                      }
                  in

                  end_destructor_group (fun cur_state4 -> transl_process cur_state4 p) occ cur_state3
                ) cur_state1 pat1 x
              ) cur_state pat;

              if Param.is_noninterf cur_state.tr_pi_state then
                transl_term_incl_destructor (no_fail (fun cur_state1 pat1 ->
                  end_destructor_group (fun cur_state2 ->
                    output_rule { cur_state2 with
                                  hyp_tags = (InputPTag(occ)) :: cur_state2.hyp_tags }
                      (Pred(cur_state2.input_pred, [pat1]))
                  ) occ cur_state1
                )) cur_state0 (OInChannel(occ)) tc
                ) cur_state
          end
        else
          begin
            begin_destructor_group (fun cur_state0 ->
              transl_term_incl_destructor (no_fail (fun cur_state1 pat1 ->
                end_destructor_group (fun cur_state1' ->
                  begin_destructor_group (fun cur_state2 ->
                    let x = Reduction_helper.new_var_pat pat in
                    transl_pat Always (fun cur_state3' pat2 ->
                      unify (fun cur_state3 ->
                        let cur_state4 =
                          if cur_state3.is_below_begin || occ.precise || Param.get_precise()
                          then
                            begin
                              let occ_name = get_occurrence_name_for_precise cur_state3 occ in
                              let ev = Param.get_precise_event (Action (Terms.get_term_type x)) in
                              Reduction_helper.add_precise_info_occ occ (Action (Terms.get_term_type x));
                              add_in_precise_actions ev;
                              { cur_state3 with
                                hypothesis = (mess_fact cur_state3.cur_phase pat1 x) :: (Pred(Param.event_pred_block,[FunApp(ev,[occ_name;x])])) :: cur_state3.hypothesis;
                                hyp_tags = (InputTag(occ)) :: (PreciseTag(occ)) ::cur_state3.hyp_tags
                              }
                            end
                          else
                            { cur_state3 with
                              hypothesis = (mess_fact cur_state3.cur_phase pat1 x) :: cur_state3.hypothesis;
                              hyp_tags = (InputTag(occ)) :: cur_state3.hyp_tags
                            }
                        in
                        end_destructor_group (fun cur_state5 -> transl_process cur_state5 p) occ cur_state4
                      ) cur_state3' pat2 x
                    ) cur_state2 pat
                  ) cur_state1';

                  if Param.is_noninterf cur_state1'.tr_pi_state then
  		  output_rule { cur_state1' with
                                  hyp_tags = (InputPTag(occ)) :: cur_state1'.hyp_tags }
  		    (Pred(cur_state1'.input_pred, [pat1]))
                ) occ cur_state1
              )) cur_state0 (OInChannel(occ)) tc
            ) cur_state
          end
    | Output(tc,t,p,occ) ->
        begin
          if optimize_mess cur_state tc
          then
            begin
              if Param.is_noninterf cur_state.tr_pi_state then
              begin
                begin_destructor_group (fun cur_state0 ->
                  transl_term (no_fail (fun cur_state1 patc ->
                    end_destructor_group (fun cur_state2 ->
                       output_rule { cur_state2 with
                                    hyp_tags = (OutputPTag occ) :: cur_state2.hyp_tags }
                        (Pred(cur_state2.output_pred, [patc]))
                    ) occ cur_state1
                  )) cur_state0 tc
                ) cur_state
              end;
              begin_destructor_group (fun cur_state0 ->
                transl_term (no_fail (fun cur_state1 pat1 ->
                  end_destructor_group (fun cur_state2 ->
                    output_rule { cur_state2 with
                                  hyp_tags = (OutputTag occ) :: cur_state2.hyp_tags
                                } (att_fact cur_state2.cur_phase pat1)
                  ) occ cur_state1
                )) cur_state0 t
              ) cur_state
            end
          else
            begin_destructor_group (fun cur_state0 ->
              transl_term (no_fail (fun cur_state1 patc ->
                transl_term (no_fail (fun cur_state2 pat1 ->
                  end_destructor_group (fun cur_state3 ->
                    if Param.is_noninterf cur_state3.tr_pi_state then
                      output_rule { cur_state3 with
                                    hyp_tags = (OutputPTag occ) :: cur_state3.hyp_tags
                                  } (Pred(cur_state2.output_pred, [patc]));
                    output_rule { cur_state3 with
                                   hyp_tags = (OutputTag occ) :: cur_state3.hyp_tags
                                } (mess_fact cur_state3.cur_phase patc pat1)
                   ) occ cur_state2
                 )) cur_state1 t
               )) cur_state0 tc
            ) cur_state
        end;
        transl_process { cur_state with
                         hyp_tags = (OutputTag occ) :: cur_state.hyp_tags } p
    | Let(pat,t,p,Nil,occ) ->
        assert (cur_state.last_step_unif_left == []); (* last_step_unif should have been appended unified *)
        (* We distinguish the case with Else branch Nil since [neg_success_conditions] remains equal
           to [None] which speeds up the translation. *)
        (* Case "in" branch taken *)
        begin_destructor_group (fun cur_state0 ->
          transl_term_incl_destructor (no_fail (fun cur_state1 pat1 ->
            transl_pat IfQueryNeedsIt (fun cur_state2 pat2 ->
              unify (
                end_destructor_group (fun cur_state3 -> transl_process cur_state3 p) occ
              ) cur_state2 pat1 pat2
            ) cur_state1 pat
          )) { cur_state0 with hyp_tags = (LetTag occ) :: cur_state0.hyp_tags } (OLet(occ)) t;
        ) cur_state
    | Let(pat,t,p,p',occ) ->
        assert (cur_state.last_step_unif_left == []); (* last_step_unif should have been appended unified *)
        (* Case "in" branch taken *)
        let neg_success_conditions = ref (Some (ref Terms.true_constraints)) in

        begin_destructor_group (fun cur_state0 ->
          transl_term_incl_destructor (no_fail (fun cur_state1 pat1 ->
            transl_pat IfQueryNeedsIt (fun cur_state2 pat2 ->
              unify (
                end_destructor_group (fun cur_state3 -> transl_process cur_state3 p) occ
              ) cur_state2 pat1 pat2
            ) cur_state1 pat
           ))
           { cur_state0 with
             neg_success_conditions = neg_success_conditions;
             hyp_tags = (LetTag occ) :: cur_state0.hyp_tags } (OLet(occ)) t
        ) cur_state;

        (* Case "else" branch taken *)
        begin
          match !neg_success_conditions with
          | None ->
              (* The neg_success_conditions have been forgotten because they
                 were too complicated to compute. Moreover, we do not start with
                 begin_destructor_group since we only apply at the end the
                 function end_destructor_group_no_test_unif *)
              transl_term_incl_destructor (fun cur_state1 pat1 ->
                must_fail (end_destructor_group_no_test_unif (fun cur_state2 -> transl_process cur_state2 p')) cur_state1 pat1;
                no_fail (fun cur_state2 _ ->
                  transl_pat_fail (end_destructor_group_no_test_unif (fun cur_state6 -> transl_process cur_state6 p'))
                    cur_state2 pat pat1
                ) cur_state1 pat1
              ) { cur_state with
                  hyp_tags = (LetTag occ) :: cur_state.hyp_tags } (OLet(occ)) t
          | Some r -> (* Use the neg_success_conditions has condition for taking
                        the else branch *)
             transl_process { cur_state with
                              constra = Terms.wedge_constraints !r cur_state.constra;
                              hyp_tags = (LetTag occ) :: cur_state.hyp_tags } p'
       end
    | LetFilter(vlist,f,p,q,occ) ->
      (* TO DO Warning! LetFilter is currently not compatible with
         non-interference! We have to generate more "test" clauses.

         For a predicate clause:
           F1 & ... & Fn -> F
         we should add the clauses:
           testF -> testF1
           testF & F1 -> testF2
           ....
           testF & F1 ... & Fn-1 -> testFn
         where, if Fi = p(M1, ..., Mn), testFi = testp(M1, ..., Mn)

         The process let v1...vn suchthat p(M1,...,Mn) generates
           h -> testp(testM1, ..., testMn)
         where testMi is obtained from Mi by existentially quantifying
         variables v1...vn. (???)
       *)
       if Param.is_noninterf cur_state.tr_pi_state then
         user_error "Predicates are currently incompatible with non-interference.";
       if !Param.check_pred_calls then check_first_fact cur_state.tr_pi_state vlist f;
       let vlist' = List.map (fun v ->
         let v' = Var (Terms.copy_var v) in
         v.link <- TLink v';
         v') vlist in

       begin_destructor_group (fun cur_state0 ->
         transl_fact (fun f1 cur_state1 ->
           end_destructor_group_no_test_unif (fun cur_state2 ->
             let cur_state3 =
               if cur_state2.is_below_begin || occ.precise || Param.get_precise()
               then
                 begin
                   match vlist' with
                     | [] ->
                         { cur_state2 with
                           hypothesis = f1 :: cur_state2.hypothesis;
                           hyp_tags = (LetFilterTag(occ)) :: cur_state2.hyp_tags
                         }
                     | [v] ->
                         let ty = Terms.get_term_type v in
                         let occ_name = get_occurrence_name_for_precise cur_state2 occ in
                         let ev = Param.get_precise_event (Action ty) in
                         Reduction_helper.add_precise_info_occ occ (Action ty);
                         add_in_precise_actions ev;
                         { cur_state2 with
                           hypothesis = f1 :: (Pred(Param.event_pred_block,[FunApp(ev,[occ_name;v])])) :: cur_state2.hypothesis;
                           hyp_tags = (LetFilterTag(occ)) :: (PreciseTag(occ)) :: cur_state2.hyp_tags
                         }
                     | _ ->
                         let ty_l = List.map Terms.get_term_type vlist' in
                         let f_tuple = Terms.get_tuple_fun ty_l in
                         let occ_name = get_occurrence_name_for_precise cur_state2 occ in
                         let ev = Param.get_precise_event (Action Param.bitstring_type) in
                         Reduction_helper.add_precise_info_occ occ (Action Param.bitstring_type);
                         add_in_precise_actions ev;
                         { cur_state2 with
                           hypothesis = f1 :: (Pred(Param.event_pred_block,[FunApp(ev,[occ_name;FunApp(f_tuple,vlist')])])) :: cur_state2.hypothesis;
                           hyp_tags = (LetFilterTag(occ)) :: (PreciseTag(occ)) :: cur_state2.hyp_tags
                         }
                 end
              else
                { cur_state2 with
                  hypothesis = f1 :: cur_state2.hypothesis;
                  hyp_tags = (LetFilterTag(occ)) :: cur_state2.hyp_tags
                }
             in
             transl_process cur_state3 p
           ) cur_state1
         ) { cur_state0 with name_params = (List.map2 (fun v v' -> (MVar(v, None), v', Always)) vlist vlist') @ cur_state0.name_params } (OLetFilter(occ)) f;
       ) cur_state;
       List.iter (fun v -> v.link <- NoLink) vlist;

       (* The else branch *)
       transl_process { cur_state with hyp_tags = LetFilterTagElse(occ) :: cur_state.hyp_tags } q
    | Event(FunApp(f,l) as lendbegin, (env_args, env), p,occ) ->
        begin
         if !Param.key_compromise == 0 then
           ()
         else
           match l with
             (Var v)::l' ->
               if !Param.key_compromise == 1 then
                 v.link <- TLink (Var comp_session_var)
               else
                 v.link <- TLink compromised_session
           | _ -> internal_error "Bad event format in queries"
        end;

        let fstatus = Pievent.get_event_status cur_state.tr_pi_state f in

        let get_occurrence_name cur_state =
          let n = Reduction_helper.get_occ_name occ in
          (* Fix now how the name [n] is displayed, to avoid different
             displays in different clauses/derivations *)
          let n_string = Display.string_of_fsymb n in
          let include_info = Reduction_helper.prepare_include_info env env_args [] in
          let name_params = cur_state.name_params in
          let npm = Reduction_helper.extract_name_params_meaning n include_info name_params in
          let np = Reduction_helper.extract_name_params n include_info name_params in
          match n.f_cat with
            | Name r ->
                let nptype = List.map Terms.get_term_type np in
                if fst n.f_type == Param.tmp_type then
                  begin
                    n.f_type <- nptype, snd n.f_type;
                    r.prev_inputs_meaning <- npm
                  end
                else if Param.get_ignore_types() then
                  begin
                    (* When we ignore types, the types of the arguments may vary,
                       only the number of arguments is preserved. *)
                    if List.length (fst n.f_type) != List.length nptype then
                      internal_error ("Name " ^ n_string ^ " has bad arity")
                  end
                else
                  begin
                    if not (Terms.eq_lists (fst n.f_type) nptype) then
                      internal_error ("Name " ^ n_string ^ " has bad type")
                  end;

                FunApp(n,np)
            | _ -> internal_error "[pitransl.ml >> transl_process] Unexpected function category in the translation of events."
        in

        begin
        (* In the specific case where an event does not have an injective status for both begin and end,
           we do not put the begin event in the hypothesis of the end clause. *)
        match fstatus.begin_status with
          | No ->
              (* Even if the event does nothing, the term lendbegin is evaluated *)
              begin_destructor_group (fun cur_state0' ->
                transl_term (
                  no_fail (fun cur_state0 pat_begin ->
                    end_destructor_group (fun cur_state1 ->
                      let cur_state_output = { cur_state1 with hyp_tags = (EventTag(occ)) :: cur_state1.hyp_tags } in
                      begin match fstatus.end_status with
                        | No -> ()
                        | WithOcc ->
                            let occ_name = get_occurrence_name cur_state_output in
                            output_rule cur_state_output (Pred(Param.inj_event_pred, [pat_begin;occ_name]))
                        | NoOcc ->
                            output_rule cur_state_output (Pred(Param.event_pred, [pat_begin]))
                      end;
                      transl_process cur_state_output p
                    ) occ cur_state0
                  )
                ) cur_state0' lendbegin
              ) cur_state
          | NoOcc ->
              begin_destructor_group (fun cur_state0' ->
                transl_term_incl_destructor (
                  no_fail (fun cur_state0 pat_begin ->
                    end_destructor_group (fun cur_state1 ->
                      let cur_state_output = { cur_state1 with hyp_tags = (EventTag(occ)) :: cur_state1.hyp_tags } in
                      begin match fstatus.end_status with
                        | No -> ()
                        | WithOcc ->
                            let occ_name = get_occurrence_name cur_state_output in
                            output_rule cur_state_output (Pred(Param.inj_event_pred, [ pat_begin;occ_name]));
                        | NoOcc ->
                            output_rule cur_state_output (Pred(Param.event_pred, [pat_begin]))
                      end;
                      let cur_state2 =
                        { cur_state_output with
                          hypothesis = Pred(Param.event_pred_block,[pat_begin]) :: cur_state_output.hypothesis;
                          hyp_tags = BeginFact :: cur_state_output.hyp_tags
                        }
                      in
                      transl_process cur_state2 p
                    ) occ cur_state0
                  )
                ) cur_state0' (OEvent(occ)) lendbegin
              ) cur_state
          | WithOcc ->
              begin_destructor_group (fun cur_state0' ->
                transl_term_incl_destructor (
                  no_fail (fun cur_state0 pat_begin ->
                    end_destructor_group (fun cur_state1 ->
                      let occ_name = get_occurrence_name cur_state1 in
                      let cur_state_output = { cur_state1 with hyp_tags = (EventTag(occ)) :: cur_state1.hyp_tags } in
                      begin match fstatus.end_status with
                        | No -> ()
                        | WithOcc -> output_rule cur_state_output (Pred(Param.inj_event_pred, [pat_begin;occ_name]))
                        | NoOcc -> output_rule cur_state_output (Pred(Param.event_pred, [pat_begin]))
                      end;
                      let cur_state2 =
                        { cur_state_output with
                          hypothesis = Pred(Param.inj_event_pred_block,[pat_begin;occ_name]) :: cur_state_output.hypothesis;
                          hyp_tags = BeginFact :: cur_state_output.hyp_tags
                        }
                      in
                      transl_process cur_state2 p
                    ) occ cur_state0
                  )
                ) { cur_state0' with is_below_begin = (env_args = None) || cur_state0'.is_below_begin } (OEvent(occ)) lendbegin
              ) cur_state
        end
    | Event(_,_,_,_) -> user_error ("Events should be function applications")
    | Insert(t,p,occ) ->
        begin_destructor_group (fun cur_state0 ->
          transl_term (no_fail (fun cur_state1 pat1 ->
            end_destructor_group (fun cur_state2 ->
	      let cur_state3 =
		{ cur_state2 with
                  hyp_tags = (InsertTag occ) :: cur_state2.hyp_tags }
	      in
              output_rule cur_state3 (table_fact cur_state2.cur_phase pat1);
	      transl_process cur_state3 p

            ) occ cur_state1
          )) cur_state0 t
        ) cur_state

    | Get(pat,t,p,q,occ) ->
        begin_destructor_group (fun cur_state0 ->
          let x = Reduction_helper.new_var_pat pat in
          transl_pat Always (fun cur_state1 pat1 ->
	    unify (fun cur_state2 ->
              transl_term (no_fail (fun cur_state3 patt ->
		unify (fun cur_state4 ->
                  let cur_state5 =
                    if cur_state4.is_below_begin || occ.precise || Param.get_precise()
                    then
                      begin
			let occ_name = get_occurrence_name_for_precise cur_state4 occ in
			let ev = Param.get_precise_event (Action (Terms.get_term_type x)) in
			Reduction_helper.add_precise_info_occ occ (Action (Terms.get_term_type x));
			add_in_precise_actions ev;
			{ cur_state4 with
                          hypothesis = (table_fact cur_state4.cur_phase x) :: (Pred(Param.event_pred_block,[FunApp(ev,[occ_name;x])])) :: cur_state4.hypothesis;
                          hyp_tags = (GetTag(occ)) :: (PreciseTag(occ)) :: cur_state4.hyp_tags
                        }
                      end
                    else
                      { cur_state4 with
                        hypothesis = (table_fact cur_state4.cur_phase x) :: cur_state4.hypothesis;
                        hyp_tags = (GetTag(occ)) :: cur_state4.hyp_tags
                      }
                  in
                  end_destructor_group (fun cur_state6 -> transl_process cur_state6 p) occ cur_state5
		) cur_state3 patt Terms.true_term
	      )) cur_state2 t
	    ) cur_state1 pat1 x
          ) cur_state0 pat
        ) cur_state;
        transl_process { cur_state with hyp_tags = GetTagElse(occ) :: cur_state.hyp_tags } q
    | Phase(n,p,_) ->
        transl_process { cur_state with
                         cur_phase = n;
                         input_pred = Param.get_pred (InputP(n));
                         output_pred = Param.get_pred (OutputP(n)) } p
    | Barrier _ | AnnBarrier _ ->
        internal_error "Barriers should not appear here (3)"
  )

(*let transl_process cur_state p = record_time time_transl_process (fun () -> transl_process cur_state p)*)

(* [rules_for_red] does not need the rewrite rules f(...fail...) -> fail
   for categories Eq and Tuple in [red_rules]. Indeed, clauses
   that come from these rewrite rules are useless:
    1/ clauses att(u1) & ... & att(fail_ti) & ... & att(un) -> att(fail)
    are subsumed by att(fail).
    2/ clauses att(u1) & ... & att(un) & testunif((u1...un), (Gu1...fail...Gun)) -> bad
    disappears because ui can be either a message or fail, and in both cases
    testunif((x1...xn), (...fail...)) is false: if ui is a message, unification
    always fails; if ui is fail, unification always succeeds, independently
    of the value of secrets. *)

let rules_for_red pi_state phase f red_rules =
  List.iter (fun red_rule ->
    let res_pred = Param.get_pred (Attacker(phase, snd f.f_type)) in
    let (hyp, concl, side_c) = Terms.copy_red red_rule in
    add_rule (List.map (att_fact phase) hyp)
      (att_fact phase concl)
      side_c
      (Apply(f, res_pred));
    if Param.is_noninterf pi_state then
      begin
      (* The definition of destructors by rules
                   g(M11...M1n) -> M1
         otherwise g(M21...M2n) -> M2
         otherwise g(M31...M3n) -> M3
         etc
         allows verifying that the same rule applies for any value of the secret
         by just testunif((x1...xn),(M11...M1n)),
                 testunif((x1...xn),(M21...M2n)),
                 testunif((x1...xn),(M31...M3n)), etc. *)
        assert (!Terms.current_bound_vars == []);
        let hyp' = List.map (Terms.generalize_vars_not_in []) hyp in
        Terms.cleanup();

        let thyp = List.map Terms.get_term_type hyp in
        let tuple_fun = Terms.get_tuple_fun thyp in
        let vlist = List.map (Terms.new_var_def_term ~may_fail:true) thyp in
        add_rule
          ((testunif_fact (FunApp(tuple_fun, vlist)) (FunApp(tuple_fun, hyp')))
           :: List.map (att_fact phase) vlist)
          (Pred(bad_pred, []))
          Terms.true_constraints
          (TestApply(f, res_pred))
      end) red_rules

let transl_attacker pi_state my_types phase =
   (* The attacker can apply all functions *)
  List.iter (Terms.clauses_for_function (rules_for_red pi_state phase)) pi_state.pi_funs;
  Hashtbl.iter (fun _ -> Terms.clauses_for_function (rules_for_red pi_state phase)) Terms.tuple_table;

  List.iter (fun t ->
    let att_pred = Param.get_pred (Attacker(phase,t)) in
    let mess_pred = Param.get_pred (Mess(phase,t)) in

    (* The attacker has any message sent on a channel he has *)
    let v = Terms.new_var_def_term t in
    let vc = Terms.new_var_def_term Param.channel_type in
    add_rule [Pred(mess_pred, [vc; v]); att_fact phase vc]
          (Pred(att_pred, [v])) Terms.true_constraints (Rl(att_pred,mess_pred));

    if (!Param.active_attacker) then
      begin
      (* The attacker can send any message he has on any channel he has *)
        let v = Terms.new_var_def_term t in
        let vc = Terms.new_var_def_term Param.channel_type in
        add_rule [att_fact phase vc; Pred(att_pred, [v])]
          (Pred(mess_pred, [vc; v])) Terms.true_constraints (Rs(att_pred, mess_pred))
      end) my_types;


  if Param.is_noninterf pi_state then
    begin
      let att_pred = Param.get_pred (Attacker(phase,Param.channel_type)) in
      let input_pred = Param.get_pred (InputP(phase)) in
      let output_pred = Param.get_pred (OutputP(phase)) in

      (* The attacker can do communications *)
      let vc = Terms.new_var_def_term Param.channel_type in
      add_rule [Pred(att_pred, [vc])] (Pred(input_pred, [vc])) Terms.true_constraints (Ri(att_pred, input_pred));
      let vc = Terms.new_var_def_term Param.channel_type in
      add_rule [Pred(att_pred, [vc])] (Pred(output_pred, [vc])) Terms.true_constraints (Ro(att_pred, output_pred));

      (* Check communications do not reveal secrets *)
      let vc = Terms.new_var_def_term Param.channel_type in
      let vc2 = Terms.new_var_def_term Param.channel_type in
      add_rule [Pred(input_pred, [vc]);
                 Pred(output_pred, [vc2]);
                 testunif_fact vc vc2]
        (Pred(bad_pred, [])) Terms.true_constraints (TestComm(input_pred, output_pred))

    end

(* Weak secrets *)

let weaksecretcst =
  Param.memo_type (fun t ->
      { f_name = Fixed "@weaksecretcst";
        f_type = [], t;
        f_private = true;
        f_options = 0;
        f_cat = Eq [];
        f_initial_cat = Eq [];
        f_record = Param.fresh_record ()
    })

let att_guess_fact t1 t2 =
  Pred(Param.get_pred (AttackerGuess(Terms.get_term_type t1)), [t1;t2])

(* [rules_for_red_guess] does not need the rewrite rules f(...fail...) -> fail
   for categories Eq and Tuple in [red_rules]. Indeed, clauses
   that come from these rewrite rules are useless:
       1/ if we use twice the same of these rewrite rules, we get
       att(u1,u1') & ... & att(fail_ti, fail_ti) & ... & att(un,un') -> att(fail, fail)
       which is subsumed by att(fail, fail)
       2/ if we use two distinct such rewrite rules, we get
       att(u1,u1') & ... & att(fail_ti, ui') & ... & att(uj, fail_tj) & ... & att(un,un') -> att(fail, fail)
       which is subsumed by att(fail, fail)
       3/ if we use one such rewrite rule and another rewrite rule, we get
       att(u1,M1) & ... & att(fail_ti, Mi) & ... & att(un, Mn) -> att(fail, M')
       which is subsumed by att(fail_ti, x) -> bad (recall that bad subsumes all conclusions)
       Mi are messages, they are not fail nor may-fail variables. *)

let rules_for_red_guess f red_rules =
  List.iter (fun red1 ->
    List.iter (fun red2 ->
      let (hyp1, concl1, side_c1) = Terms.copy_red red1 in
      let (hyp2, concl2, side_c2) = Terms.copy_red red2 in
      add_rule (List.map2 att_guess_fact hyp1 hyp2)
        (att_guess_fact concl1 concl2)
        (Terms.wedge_constraints side_c1 side_c2)
        (Apply(f, Param.get_pred (AttackerGuess(snd f.f_type))))
        ) red_rules
      ) red_rules


let weak_secret_clauses pi_state my_types w =
  add_rule [] (att_guess_fact (FunApp(w, [])) (FunApp(weaksecretcst (snd w.f_type), []))) Terms.true_constraints WeakSecr;

  (* rules_for_function_guess for each function, including tuples *)
  List.iter (Terms.clauses_for_function rules_for_red_guess) pi_state.pi_funs;
  Hashtbl.iter (fun _ -> Terms.clauses_for_function rules_for_red_guess) Terms.tuple_table;

  List.map (fun t ->
    let att_guess = Param.get_pred (AttackerGuess(t)) in

    let x = Terms.new_var_def_term t
    and fail = Terms.get_fail_term t in
    add_rule [Pred(att_guess, [x; fail])] (Pred(Param.bad_pred, [])) Terms.true_constraints (Rfail(att_guess));
    add_rule [Pred(att_guess, [fail; x])] (Pred(Param.bad_pred, [])) Terms.true_constraints (Rfail(att_guess));

    add_rule [] (Pred(att_guess, [fail;fail])) Terms.true_constraints Init;

    let v = Terms.new_var_def_term t in
    let hyp = [att_fact pi_state.pi_max_used_phase v] in
    let concl = Pred(att_guess, [v; v]) in
    let r = (t, Rule(!nrule, PhaseChange, hyp, concl, Terms.true_constraints)) in
    add_rule hyp concl Terms.true_constraints PhaseChange;

    let v1 = Terms.new_var_def_term t in
    let v2 = Terms.new_var_def_term t in
    let v3 = Terms.new_var_def_term t in
    add_rule [Pred(att_guess, [v1; v2]); Pred(att_guess, [v1; v3])]
      (Pred(Param.bad_pred, [])) (Terms.constraints_of_neq v2 v3) (TestEq(att_guess));

    let v1 = Terms.new_var_def_term t in
    let v2 = Terms.new_var_def_term t in
    let v3 = Terms.new_var_def_term t in
    add_rule [Pred(att_guess, [v2; v1]); Pred(att_guess, [v3; v1])]
      (Pred(Param.bad_pred, [])) (Terms.constraints_of_neq v2 v3) (TestEq(att_guess));

    (* adjust the selection function *)
    let v1 = Terms.new_var_def t in
    let v2 = Terms.new_var_def t in
    add_no_unif (att_guess, [FVar v1; FVar v2])
      (NoUnifValue (Selfun.never_select_weight+10)) [Hypothesis];

    r) my_types


(* Handle key_compromise *)

let comp_output_rule prev_input out_fact =
  assert (!Terms.current_bound_vars == []);
  add_rule (List.map Terms.copy_fact2 prev_input)
    (Terms.copy_fact2 out_fact) Terms.true_constraints LblComp;
  Terms.cleanup()

let comp_fact t =
  Pred(Param.get_pred (Compromise(Terms.get_term_type t)), [t])

let rec comp_transl_process = function
   Nil -> ()
 | NamedProcess(_, _, p) -> comp_transl_process p
 | Par(p,q) -> comp_transl_process p;
               comp_transl_process q
 | Repl (p,_) ->
     comp_transl_process p
 | Restr(n,_,p,_) ->
     begin
       match n.f_cat with
         Name { prev_inputs_meaning = l } ->
           let rec build_params ml tl =
             match (ml, tl) with
               [],[] -> [],[]
             | (m::l),(ty::tyl) ->
                 let (name_params, prev_input) = build_params l tyl in
                 begin
                   match m with
                     MCompSid ->
                       (compromised_session :: name_params, prev_input)
                   | _ ->
                       let v = Var (Terms.new_var ~orig:false (Reduction_helper.meaning_name m) ty) in
                       (v :: name_params, (comp_fact v) :: prev_input)
                 end
             | _ -> Parsing_helper.internal_error "bad length in comp_transl_process"
           in
           let (name_params, prev_input) = build_params l (fst n.f_type) in
           comp_output_rule prev_input
             (comp_fact (FunApp(n, name_params)));
           if List.exists (fun x -> x == compromised_session) name_params then
             comp_output_rule prev_input
               (att_fact 0 (FunApp(n, name_params)))
       | _ -> internal_error "name expected in comp_transl_process"
     end;
     comp_transl_process p
 | Test(t1,p,q,_) ->
     comp_transl_process p;
     comp_transl_process q
 | Input(tc,pat,p,_) ->
     comp_transl_process p
 | Output(tc,t,p,_) ->
     comp_transl_process p
 | Let(pat,t,p,p',_) ->
     comp_transl_process p;
     comp_transl_process p'
 | LetFilter(_,_,p,q,_) ->
     comp_transl_process p;
     comp_transl_process q
 | Event (l,_,p,_) ->
     comp_transl_process p (* TO DO *)
 | Insert (_,p,_) ->
     comp_transl_process p
 | Get (_,_,p,q,_) ->
     comp_transl_process p;
     comp_transl_process q
 | Phase _ ->
     user_error "Phases are incompatible with key compromise.\nKey compromise is itself already a phase scenario"
 | Barrier _ | AnnBarrier _ ->
     internal_error "Barriers should not appear here (4)"

let comp_rules_for_function f =
   match f.f_cat with
     Eq _ | Tuple ->
       let vars = Terms.var_gen (fst f.f_type) in
       add_rule (List.map comp_fact vars)
         (comp_fact (FunApp(f,vars))) Terms.true_constraints
         (Apply(f, Param.get_pred (Compromise(snd f.f_type))))
   | _ -> ()

(* Not declarations *)

let get_not pi_state =
  let not_set = ref [] in
  let add_not f =
    not_set := f ::(!not_set)
  in
  List.iter (function
      QFact(p,_,l,_) ->
        (* We remove not declarations that contain choice. *)
        if not (List.exists Terms.has_choice l)
        then
          begin
            (* For attacker: not declarations, the not declaration is also
               valid in previous phases, because of the implication
               attacker_p(i):x => attacker_p(i+1):x.
               A similar point holds for table. *)
            begin
              match p.p_info with
                Attacker(i,t) ->
                  for j = 0 to i-1 do
                    let att_j = Param.get_pred (Attacker(j,t)) in
                    add_not(Pred(att_j,l))
                  done
              | Table(i) ->
                  for j = 0 to i-1 do
                    let table_j = Param.get_pred (Table(j)) in
                    add_not(Pred(table_j,l))
                  done
              | _ -> ()
            end;
            add_not(Pred(p,l))
          end
    | _ -> Parsing_helper.user_error "The only allowed facts in \"not\" declarations are attacker, mess, table, and user-defined predicates."
          ) (pi_state.pi_get_not pi_state);
  !not_set

(* clauses given in the input file and elimtrue declarations *)

let get_elimtrue_initial_clauses pi_state =
  List.iter (fun (hyp1, concl1, constra1, tag1) ->
    TermsEq.close_rule_destr_eq (fun (hyp, concl, constra) ->
      add_rule hyp concl constra tag1) (hyp1, concl1, constra1))
    pi_state.pi_input_clauses;
  let elimtrue_set = ref [] in
  let add_elimtrue f =
    elimtrue_set := f ::(!elimtrue_set)
  in
  List.iter (fun fact ->
    TermsEq.close_rule_destr_eq (fun (hyp, concl, constra) ->
      (* The elimtrue optimization is ignored when the constraint is
         not empty, which may happen if the fact contains destructors
         with side conditions *)
      if Terms.is_true_constraints constra then add_elimtrue (!nrule, concl);
      add_rule hyp concl constra LblClause) ([], fact, Terms.true_constraints))
    pi_state.pi_elimtrue;
  (!elimtrue_set, !red_rules)

(* Handle non-interference *)

let rec apply_mapping_term m = function
  | FunApp(f,[]) as t ->
      begin
        try
          Var(List.assq f m)
        with Not_found -> t
      end
  | FunApp(f,args) -> FunApp(f,List.map (apply_mapping_term m) args)
  | t -> t

let rec apply_mapping_pattern m = function
  | PatTuple(f,args) -> PatTuple(f,List.map (apply_mapping_pattern m) args)
  | PatEqual t -> PatEqual(apply_mapping_term m t)
  | pat -> pat

let apply_mapping_fact m = function
  | Pred(p,args) -> Pred(p,List.map (apply_mapping_term m) args)

let rec apply_mapping_process m = function
  | Nil -> Nil
  | Par(p1,p2) -> Par(apply_mapping_process m p1, apply_mapping_process m p2)
  | Repl(p,occ) -> Repl(apply_mapping_process m p,occ)
  | Restr(n,env,p,occ) ->
      (* It's ok to not apply the mapping on the environment *)
      Restr(n,env,apply_mapping_process m p, occ)
  | Test(t,p1,p2,occ) ->
      Test(apply_mapping_term m t,
        apply_mapping_process m p1,
        apply_mapping_process m p2,
        occ)
  | Input(t,pat,p,occ) ->
      Input(apply_mapping_term m t,
        apply_mapping_pattern m pat,
        apply_mapping_process m p,
        occ)
  | Output(t1,t2,p,occ) ->
      Output(apply_mapping_term m t1,
        apply_mapping_term m t2,
        apply_mapping_process m p,
        occ)
  | Let(pat,t,p1,p2,occ) ->
      Let(apply_mapping_pattern m pat,
        apply_mapping_term m t,
        apply_mapping_process m p1,
        apply_mapping_process m p2,
        occ)
  | LetFilter(bl,f,p1,p2,occ) ->
      LetFilter(bl,
        apply_mapping_fact m f,
        apply_mapping_process m p1,
        apply_mapping_process m p2,
        occ)
  | Event(t,env,p,occ) -> Event(apply_mapping_term m t, env, apply_mapping_process m p, occ)
  | Insert(t,p,occ) -> Insert(apply_mapping_term m t, apply_mapping_process m p, occ)
  | Get(pat,t,p1,p2,occ) ->
      Get(apply_mapping_pattern m pat,
        apply_mapping_term m t,
        apply_mapping_process m p1,
        apply_mapping_process m p2,
        occ)
  | Phase(i,p,occ) -> Phase(i,apply_mapping_process m p, occ)
  | NamedProcess(s,tl,p) -> NamedProcess(s,tl,apply_mapping_process m p)
  | Barrier _ | AnnBarrier _ -> Parsing_helper.internal_error "[pitransl.ml >> apply_mapping_process] Barriers should not appear here"

let set_free_names_prev_inputs f_next pi_state =
  List.iter (fun ch ->
    match ch.f_cat with
      Name r -> r.prev_inputs <- Some (FunApp(ch, []))
    | _ -> internal_error "should be a name 1")
    pi_state.pi_freenames;

  f_next ();

  List.iter (fun ch ->
    match ch.f_cat with
      Name r -> r.prev_inputs <- None
    | _ -> internal_error "should be a name 2")
    pi_state.pi_freenames


(* Compute predicates that queries try to prove *)

(* [add p accu] adds the predicate [p] to [accu] if it is not already present *)
let add p accu =
  if List.memq p accu then accu else p::accu

let add_pred_prove_and_events_event (accu_pred,accu_ev) = function
  | QSEvent(_,_,_,_,FunApp(ev,_)) | QSEvent2(FunApp(ev,_),_) -> (accu_pred,add ev accu_ev)
  | QSEvent _ | QSEvent2 _ -> internal_error "[pitransl.ml >> add_pred_prove_and_events_for_lemmas_event] Events predicate should have an event symbol."
  | QNeq _ | QEq _ | QGeq _ | QGr _ | QIsNat _ -> (accu_pred,accu_ev)
  | QFact(p,_,_,_) ->
      match p.p_info with
      | Attacker(n,t) -> (add p accu_pred,accu_ev)
      | Table(n) -> (add p accu_pred,accu_ev)
      (* AttackerBin, AttackerGuess, TableBin cannot occur since we
	 translate a monoprocess *)
      | _ ->
	  if p.p_prop land Param.pred_BLOCKING == 0 then
	    (add p accu_pred,accu_ev)
	  else
	    (* Blocking predicates do not need to be added,
	       since we cannot resolve on them anyway. *)
	    (accu_pred,accu_ev)

let rec add_pred_prove_and_events_realquery accu = function
  | Before(_, concl) -> add_pred_prove_and_events_concl accu concl

and add_pred_prove_and_events_concl accu = function
  | QTrue | QFalse -> accu
  | QConstraints _ -> accu
  | QEvent e -> add_pred_prove_and_events_event accu e
  | NestedQuery(Before(hyp,concl)) ->
      let accu' = List.fold_left add_pred_prove_and_events_event accu hyp in
      add_pred_prove_and_events_concl accu' concl
  | QAnd(c1,c2) | QOr(c1,c2) ->
      add_pred_prove_and_events_concl (add_pred_prove_and_events_concl accu c1) c2

let add_pred_prove_and_events_query accu (q0, ext) =
  match q0 with
  | PutBegin _ -> accu
  | RealQuery(q,_) ->
      add_pred_prove_and_events_realquery accu q
  | QSecret _ ->
      Parsing_helper.internal_error "QSecret should have been encoded"

let get_pred_prove_and_events ql =
  List.fold_left add_pred_prove_and_events_query ([],[]) ql

(* Global translation *)

let reset() =
  terms_to_add_in_name_params := [];
  nrule := 0;
  red_rules := [];
  no_unif_set := [];
  current_precise_actions := [];
  Hashtbl.reset explored_occurrences


let transl pi_state =
  (* Reset the record of which occurrence are precise (needed for reconstruction) *)
  Reduction_helper.reset_occ_precise_event ();
  reset();
  let ({ proc = p }, query) = Param.get_process_query pi_state in
  Reduction_helper.reset_name_args p;
  let non_interference = Param.is_noninterf pi_state in
  let my_types = if Param.get_ignore_types() then [Param.any_type] else pi_state.pi_types in
  let (elimtrue_set, clauses_to_initialize_selfun) =
    get_elimtrue_initial_clauses pi_state
  in
  (* We will use clauses_to_initialize_selfun to initialize
     the selection function.
     In particular, when there is a predicate
       member:x,y -> member:x,cons(z,y)
     we would like nounif member:*x,y
     It is important to initialize this very early, so that
     the simplification of the initial rules is performed with
     the good selection function. *)

  for i = 0 to pi_state.pi_max_used_phase do
    transl_attacker pi_state my_types i;
    List.iter (fun t ->
      (* The attacker has fail *)
      add_rule [] (att_fact i (Terms.get_fail_term t)) Terms.true_constraints Init;

      let att_i = Param.get_pred (Attacker(i,t)) in
      let v = Terms.new_var_def t in
      add_no_unif (att_i, [FVar v]) (NoUnifValue Selfun.never_select_weight) [Hypothesis];
      if i > 0 then
        (* It is enough to transmit only messages from one phase to the next
           because the attacker already has fail in all phases. *)
        let w = Terms.new_var_def_term t in
        let att_im1 = Param.get_pred (Attacker(i-1,t)) in
        add_rule [Pred(att_im1, [w])] (Pred(att_i, [w])) Terms.true_constraints PhaseChange
          ) my_types;
    if i > 0 then
      let tbl_i = Param.get_pred (Table(i)) in
      let tbl_im1 = Param.get_pred (Table(i-1)) in
      let w = Terms.new_var_def_term Param.table_type in
      add_rule [Pred(tbl_im1, [w])] (Pred(tbl_i, [w])) Terms.true_constraints TblPhaseChange
  done;

   (* Knowing the free names and creating new names is necessary only in phase 0.
      The subsequent phases will get them by attacker_i(x) -> attacker_{i+1}(x) *)

   (* The attacker has the public free names.
      The non-interference queries have their private flag set. *)
  List.iter (fun ch ->
    if not ch.f_private then
      add_rule [] (att_fact 0 (FunApp(ch, []))) Terms.true_constraints Init) pi_state.pi_freenames;

  List.iter (fun t ->
    (* Clauses for equality *)
    let v = Terms.new_var_def_term t in
    add_rule [] (Pred(Param.get_pred (Equal(t)), [v;v])) Terms.true_constraints LblEq;

    (* The attacker can create new names *)
    let att_pred0 = Param.get_pred (Attacker(0, t)) in
    let v = Terms.new_var_def_term Param.sid_type in
    let new_name_fun = Terms.new_name_fun t in
    (* Fix now how the name [new_name_fun] is displayed, to avoid different
       displays in different clauses/derivations *)
    ignore (Display.string_of_fsymb new_name_fun);
    if non_interference then
      add_rule [att_fact 0 v] (att_fact 0 (FunApp(new_name_fun, [v])))
        Terms.true_constraints (Rn att_pred0)
    else
      add_rule [] (att_fact 0 (FunApp(new_name_fun, [v])))
        Terms.true_constraints (Rn att_pred0);

    if non_interference then
      begin
      (* Rules that derive bad from attacker are necessary only in the last phase.
         Previous phases will get them by attacker_i(x) -> attacker_{i+1}(x) *)

        let att_pred = Param.get_pred (Attacker(pi_state.pi_max_used_phase, t)) in

      (* The attacker can do all equality tests on data he has *)
        let v = Terms.new_var_def_term t in
        let vc = Terms.new_var_def_term t in
        add_rule [Pred(att_pred, [vc]); Pred(att_pred, [v]); testunif_fact vc v]
          (Pred(bad_pred, [])) Terms.true_constraints (TestEq(att_pred));

      end
        ) my_types;


  let att_rule_num =
    (* Weak secrets *)
    match query with
    | WeakSecret w -> weak_secret_clauses pi_state my_types w
    | _ -> []
  in

  (* Remove subsumed clauses and tautologies among attacker clauses,
     to avoid displaying many useless clauses. *)

  if !Param.remove_subsumed_clauses_before_display then
    begin
      Database.FeatureGenClause.initialize ();
      let tmp_rules = Database.SetClause.create () in
      (* Store in tmp_rules the rules after removing subsumed rules and tautologies *)
      List.iter (function (hyp, concl, _, _) as rule ->
        (* eliminate tautologies *)
        if List.exists (Terms.equal_facts concl) hyp then () else
        (* eliminate subsumed clauses *)
        let annot_rule = Database.FeatureGenClause.generate_feature_vector_and_subsumption_data rule in

        if Database.SetClause.implies tmp_rules annot_rule
        then ()
        else
          begin
            Database.SetClause.deactivate_implied_by () tmp_rules annot_rule;
            (* Adding the dummy fact as selected fact does not impact the subsumption. *)
            Database.SetClause.add tmp_rules annot_rule Param.dummy_fact ()
          end
      ) !red_rules;
      (* Renumber the rules *)
      red_rules := [];
      nrule := 0;
      Database.SetClause.iter (fun elt ->
        match elt.annot_clause with
        | (hyp', concl', Rule(_, tags, hyp, concl, constra), constra'),_ ->
            red_rules := (hyp', concl', Rule(!nrule, tags, hyp, concl, constra), constra') :: (!red_rules);
            incr nrule
        | _ -> Parsing_helper.internal_error "All clauses should have history Rule(...) at this point"
      ) tmp_rules
    end;

  let mapping, p' =
    match pi_state.pi_process_query with
    | SingleProcessSingleQuery(_, NonInterfQuery(secret_vars_with_sets)) ->
	let process_mapping =
	  List.map (fun (f,_) ->
	    (f,Terms.new_var ~orig:false (Terms.get_fsymb_basename f) (snd f.f_type))
	      ) secret_vars_with_sets
	in
        (* The variables in [process_mapping] replace the symbols in [p].
           But these variables must be linked (otherwise the translation of
           terms fails). Finally,to handle non-interference, we they must be linked
           to fresh variables that will themselves be linked to the secrets. *)
	let mapping =
          List.map (fun (f,x) ->
            let y = Terms.new_var ~orig:false (Terms.get_fsymb_basename f) (snd f.f_type) in
            x.link <- TLink(Var y);
            y.link <- TLink(FunApp(f,[]));
            (f,y)
              ) process_mapping
	in

	let p' = apply_mapping_process process_mapping p in
	(mapping, p')
    | _ ->
	([], p)
  in
  let cur_state_init =
    { tr_pi_state = pi_state;
      hypothesis = []; constra = Terms.true_constraints;
      last_step_unif_left = [];
      last_step_unif_right = [];
      last_step_constra = Terms.true_constraints;
      last_step_variables = [];
      neg_success_conditions = ref None;
      mapping_secret_vars = mapping;
      name_params = []; repl_count = 0; current_session_id = None;
      is_below_begin = false; cur_phase = 0;
      input_pred = Param.get_pred (InputP(0));
      output_pred = Param.get_pred (OutputP(0));
      hyp_tags = [];
      record_fun_opt = None
    }
  in

  (* Dummy translation of the process to set the arguments of bound
     names and record symbols used as features to index clauses for
     subsumption *)
  set_free_names_prev_inputs (fun () -> transl_process cur_state_init p') pi_state;

  if !Param.key_compromise > 0 then
    begin
      List.iter (fun t ->
        let v = Terms.new_var_def t in
        add_no_unif (Param.get_pred (Compromise(t)), [FVar v]) (NoUnifValue Selfun.never_select_weight) [Hypothesis]
          ) my_types;
      comp_transl_process p;
      List.iter (fun ch ->
        if not ch.f_private then
          add_rule [] (comp_fact (FunApp(ch, []))) Terms.true_constraints Init) pi_state.pi_freenames;
      List.iter comp_rules_for_function pi_state.pi_funs;
      Hashtbl.iter (fun _ -> comp_rules_for_function) Terms.tuple_table
    end;

  let tmp_nrule = !nrule in
  let tmp_current_precise_actions = !current_precise_actions in

  (* The function that will perform the real translation of the
     process into clauses *)
  let generate_process_clauses f_add =
    nrule := tmp_nrule;
    current_precise_actions := tmp_current_precise_actions;
    let cur_state = { cur_state_init with record_fun_opt = Some f_add } in
    set_free_names_prev_inputs (fun () -> transl_process cur_state p') pi_state
  in

  List.iter (function ((_,fl) as f,n,for_hyp) ->
    (* We remove nounif that contains choice. *)
    if not (List.exists Terms.has_choice_format fl)
    then
      begin
        let f = Selfun.homogeneous_format f in

        if !Param.verbose_term
        then Display.Text.display_nounif_declaration f (Selfun.weight_of_user_weight n) for_hyp;
        
        add_no_unif f n for_hyp
      end
  ) (pi_state.pi_get_nounif pi_state);

  let solver_kind =
    match query with
      WeakSecret _ ->
        Solve_WeakSecret(att_rule_num, pi_state.pi_max_used_phase)
    | NonInterfQuery secret_vars_with_sets ->
        Solve_Noninterf(secret_vars_with_sets)
    | CorrespQuery _ | CorrespQEnc _ ->
        Solve_Standard
    | _ -> Parsing_helper.internal_error "unsupported query in pitransl"
  in

  let (pred_prove,events_in_queries) =
    match query with
    | WeakSecret _ | NonInterfQuery _ -> ([],[])
    | CorrespQuery(ql,_) -> get_pred_prove_and_events ql
    | CorrespQEnc(qql,_) -> get_pred_prove_and_events (List.map snd qql)
    | _ -> Parsing_helper.internal_error "unsupported query in pitransl"
  in

  let pi_state' =
    { pi_state with
      pi_terms_to_add_in_name_params = Set (!terms_to_add_in_name_params);
      pi_precise_actions = !current_precise_actions
    }
  in
  let horn_state =
    { h_clauses = ToGenerate (List.rev (!red_rules), generate_process_clauses);
      h_equations = pi_state.pi_equations;
      h_close_with_equations = false;
      h_not = get_not pi_state;
      h_elimtrue = elimtrue_set;
      h_equiv = pi_state.pi_equivalence_clauses;
      h_nounif = !no_unif_set;
      h_clauses_to_initialize_selfun = clauses_to_initialize_selfun;
      h_solver_kind = solver_kind;
      h_lemmas = [];
      h_pred_prove = pred_prove;
      h_event_in_queries = events_in_queries
	(* lemma assumptions and assumptions of queries proved by induction
	   added in Lemma.transl_lemmas *)
    }
  in
  reset();
  horn_state, pi_state'
