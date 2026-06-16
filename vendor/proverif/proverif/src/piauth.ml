open Parsing_helper
open Types
open Pitypes
open Terms

let supplemental_info = ref []

let declared_axioms = ref []

let faulty_clauses_injective = ref []

let success_clauses = ref []

let for_biprocess = ref false

let traces_to_reconstruct = ref 0
let shown_stop = ref false

let strong_verification_att_table = ref false
   (* When proving a lemma or doing a proof by induction, we prove that
      attacker/table appear in the hypothesis of the clause, not that
      they can be derived from hypothesis of the clause.

      For proofs by induction, we can still prove that
      attacker/table can be derived from hypothesis of the clause for
      nested queries, because nested queries are not used in induction
      hypothesis. In this case, we pass strong_verif = false to the
      verification function.
      The same remark holds for the injectivity clauses, since the
      induction hypothesis does not use injectivity. *)
    
type auth_ordered_reduction = (fact * (ordering_function * int)) list * fact * history * constraints

let auth_ordered_rule_of_ordered_rule ({ rule = (hypl, concl, hist, constra); _ } as ord_rule) = match ord_rule.order_data with
  | None ->
      let hypl' = List.map (fun hyp -> (hyp,([],0))) hypl in
      ((hypl',concl,hist,constra):auth_ordered_reduction)
  | Some ord_data ->
      let hypl' = List.map2 (fun hyp data -> hyp,data) hypl ord_data in
      (hypl',concl,hist,constra)

let auth_ordered_rule_of_rule (hypl, concl, hist, constra) =
  let hypl' = List.map (fun hyp -> (hyp,([],0))) hypl in
  ((hypl',concl,hist,constra):auth_ordered_reduction)

let ordered_rule_of_auth_ordered (hypl,concl,hist,constra) =
  let (hypl',order_data) =
    List.fold_right (fun (f,ord_data) (acc_f,acc_o) ->
      f::acc_f,ord_data::acc_o
    ) hypl ([],[])
  in
  { rule = (hypl',concl,hist,constra); order_data = Some order_data }

let rule_of_auth_ordered_rule (hypl,concl,hist,constra) =
  let hypl' = List.map (fun (f,_) -> f) hypl in
  (hypl',concl,hist,constra)

let copy_auth_rule2 ((hyp, concl, hist, constra):auth_ordered_reduction) =
  let tmp_bound = !current_bound_vars in
  current_bound_vars := [];
  let r = (List.map (fun (f,ord_data) -> copy_fact2 f, ord_data) hyp, copy_fact2 concl, hist, copy_constra2 constra) in
  cleanup();
  current_bound_vars := tmp_bound;
  r

let copy_auth_rule2_no_cleanup ((hyp, concl, hist, constra):auth_ordered_reduction) =
  (List.map (fun (f,ord_data) -> copy_fact2 f, ord_data) hyp, copy_fact2 concl, hist, copy_constra2 constra)

(* Display a clause and possibly a corresponding trace
   When inj_mode = Some q, try to reconstruct a trace that falsifies injectivity
   When inj_mode = None, just try to reconstruct a trace corresponding
   to the derivation of the clause cl.
   Returns true when a trace has definitely been found.
 *)

let display_clause_trace lemmas detail recheck opt_query list_started cl =
  Display.Text.print_string "goal reachable: ";
  Display.Text.display_ordered_rule_abbrev cl;
  if !Param.html_output then
    begin
      if not (!list_started) then
        begin
          list_started := true;
          Display.Html.print_string "<UL>\n";
        end;
      Display.Html.print_string "<LI>goal reachable: ";
      Display.Html.display_ordered_rule_abbrev cl
    end;
  (* TulaFale expects a derivation after "goal reachable" *)
  if (detail || (!Param.tulafale = 1)) then
    begin
      try
        let verify_rule clause = 
          Display.auto_cleanup_display (fun () ->
            auto_cleanup (fun () ->
              let deriv = History.build_history recheck clause.rule in
              if (!traces_to_reconstruct != 0) && (!Param.reconstruct_derivation) &&
                (!Param.key_compromise == 0) 
              then 
                begin 
                  History.unify_derivation (fun new_tree ->
                    if !traces_to_reconstruct > 0 then decr traces_to_reconstruct;
                    if !for_biprocess
                    then Reduction_bipro.do_reduction opt_query !declared_axioms new_tree
                    else Reduction.do_reduction opt_query !declared_axioms new_tree
                  ) recheck deriv
                end
              else false
            )
          )
        in

        let first_result = verify_rule cl in

        if ((!traces_to_reconstruct != 0) && (!Param.reconstruct_derivation) &&
          (!Param.key_compromise == 0)) && (not first_result)
        then 
          begin 
            let second_result = 
              let (hyp,concl,hist,constra) = cl.rule in
	      
              if (constra.is_nat <> [] || constra.geq <> []) && (!traces_to_reconstruct != 0)
              then
                try
                  TermsEq.get_solution (fun () ->
                    let cl' = copy_ordered_rule2 cl in
                    Terms.auto_cleanup (fun () ->
                      (* When we try to find the attack trace, we only apply the lemmas but not the inductive lemmas. *)
                      let clauses = Rules.solving_request_rule ~apply_not:true lemmas [] cl' in
		      
                      if clauses = []
                      then false
                      else
                        begin
                          Display.Text.newline ();
                          Display.Text.print_line "Presence of natural number in the clause. We try to resolve more the clause to obtain an attack trace.";
                          if !Param.html_output
                          then Display.Html.print_line "Presence of natural number in the clause. We try to resolve more the clause to obtain an attack trace.";
			  
                          List.exists (fun cl ->
                            if !traces_to_reconstruct != 0 
                            then verify_rule cl
                            else false
		          ) clauses
                        end
                    )
                  ) constra
                with TermsEq.FalseConstraint -> false
              else false
            in
            if (not second_result) && (!traces_to_reconstruct = 0) && (!Param.reconstruct_trace > 0) && (not !shown_stop) then
              begin
                shown_stop := true;
                Display.Def.print_line "Stopping attack reconstruction attempts. To try more traces, modify the setting reconstructTrace.";
              end;
            second_result
          end
        else first_result
      with Not_found ->
        (* When the derivation could not be reconstructed *)
        cleanup ();
        false
    end
  else
    false

(* Get the number of premises, constraints and subterm excluded *)

let rec number_of_facts_in_premise = function
  | [] -> 0
  | (QNeq _ | QGeq _ | QIsNat _) :: q_ev 
  | QFact({ p_info = Subterm _; _},_,_,_) :: q_ev -> number_of_facts_in_premise q_ev
  | _ :: q_ev -> 1 + number_of_facts_in_premise q_ev

(* Link variables of a fact to new constants, of type "SpecVar" *)

let put_constants_rule (hyp, concl, hist, constra) =
  List.iter (fun (f,_) -> put_constants_fact f) hyp;
  put_constants_fact concl;
  Terms.iter_constraints put_constants constra

(* Copy a query, following links inside variables *)

let copy_query = TermsEq.copy_remove_syntactic_realquery

(* Replace constants "SpecVar" of a query with the corresponding variables *)

let rec specvar_to_var = function
    Var v -> Var v
  | FunApp({ f_cat = SpecVar v} ,[]) ->
      Var v
  | FunApp(f,l) -> FunApp(f, List.map specvar_to_var l)

let specvar_to_var_e (t,ext) = (specvar_to_var t, ext)

let specvar_to_var_occurrence = function
  | None -> None
  | Some o -> Some (specvar_to_var o)

(* The queries here have already been encoded, so they do not use
   time variables *)
let specvar_to_var_event = function
    QSEvent(b,ord_fun,occ,_,t) ->
      QSEvent(b,ord_fun,specvar_to_var_occurrence occ,None,specvar_to_var t)
  | QSEvent2(t1,t2) -> QSEvent2(specvar_to_var t1, specvar_to_var t2)
  | QFact(p,ord_fun,tl,_) ->
      QFact(p,ord_fun,List.map specvar_to_var tl,None)
  | QNeq(t1,t2) -> QNeq(specvar_to_var_e t1, specvar_to_var_e t2)
  | QEq(t1,t2) -> QEq(specvar_to_var_e t1, specvar_to_var_e t2)
  | QGeq(t1,t2) -> QGeq(specvar_to_var_e t1, specvar_to_var_e t2)
  | QIsNat t -> QIsNat(specvar_to_var t)
  | QGr _ -> Parsing_helper.internal_error "[piauth.ml >> specvar_to_var_event] Queries with strict temporal inequalities should have been encoded by now"

let rec specvar_to_var_query = function
  | Before(el,concl_q) -> Before(List.map specvar_to_var_event el, specvar_to_var_conclusion_query concl_q)

and specvar_to_var_conclusion_query = function
  | QTrue -> QTrue
  | QFalse -> QFalse
  | QConstraints q -> QConstraints (Terms.map_constraints specvar_to_var q)
  | QEvent e -> QEvent(specvar_to_var_event e)
  | NestedQuery q -> NestedQuery (specvar_to_var_query q)
  | QAnd(concl1,concl2) -> QAnd(specvar_to_var_conclusion_query concl1, specvar_to_var_conclusion_query concl2)
  | QOr(concl1,concl2) -> QOr(specvar_to_var_conclusion_query concl1, specvar_to_var_conclusion_query concl2)

let specvar_to_var_env = List.map (fun (v,t) -> (v, specvar_to_var t))

let specvar_to_var_fact = function
    Pred(p,l) -> Pred(p, List.map specvar_to_var l)

let specvar_to_var_constraints = Terms.map_constraints specvar_to_var

(* Transforms a query into a non-injective, non-nested one

   The function [Piauth.simplify_query] must provide a stronger query than
   the simplified queries produced in [Lemma.simplify_queries_for_induction],
   using [Lemma.simplify_induction_conclusion_query], because the proof of
   the query obtained by [Piauth.simplify_query] allows us to apply the
   inductive lemma.
   In particular, we simplify nested queries [e ==> concl] into conjunctions
   [e && concl] in both functions. *)

let non_inj_event = function
    QSEvent(_,ord_fun,occ,_,t) -> QSEvent(None,ord_fun,occ,None,t)
  | e -> e

let rec simplify_conclusion_query = function
  | QTrue -> QTrue
  | QFalse -> QFalse
  | QConstraints _ as q -> q (* no transformation, as no nesting/injectivity inside possible *)
  | QEvent e -> QEvent(non_inj_event e)
  | NestedQuery(Before([e],concl)) ->
      QAnd(QEvent(non_inj_event e), simplify_conclusion_query concl)
  | NestedQuery _ ->
      Parsing_helper.internal_error "[piauth.ml >> simplify_conclusion_query] Nested queries should have exactly one premise."
  | QAnd(concl1,concl2) ->
      QAnd(simplify_conclusion_query concl1, simplify_conclusion_query concl2)
  | QOr(concl1,concl2) ->
      QOr(simplify_conclusion_query concl1, simplify_conclusion_query concl2)

let simplify_query (Before(el,concl)) =
  Before(List.map non_inj_event el, simplify_conclusion_query concl)

let rec remove_nested_conclusion_query = function
  | QTrue -> QTrue
  | QFalse -> QFalse
  | QConstraints q -> QConstraints q
  | QEvent e -> QEvent e
  | NestedQuery(Before([e],_)) -> QEvent e
  | NestedQuery _ -> Parsing_helper.internal_error "[piauth.ml >> remove_nested_conclusion_query] Nested queries should have exactly one premise."
  | QAnd(concl1,concl2) -> QAnd(remove_nested_conclusion_query concl1,remove_nested_conclusion_query concl2)
  | QOr(concl1,concl2) -> QOr(remove_nested_conclusion_query concl1, remove_nested_conclusion_query concl2)

let remove_nested (Before(el,concl)) =
  Before(el,remove_nested_conclusion_query concl)

let rec is_non_nested_conclusion_query = function
  | QTrue
  | QFalse
  | QConstraints _
  | QEvent _ -> true
  | QAnd(q1,q2) | QOr(q1,q2) -> is_non_nested_conclusion_query q1 && is_non_nested_conclusion_query q2
  | NestedQuery _ -> false

let is_non_nested_query = function
  | Before(_,concl) -> is_non_nested_conclusion_query concl

let is_non_injective_event = function
    QSEvent(Some _,_,_,_,_) -> false
  | _ -> true

let rec is_non_injective_conclusion_query = function
  | QTrue
  | QFalse 
  | QConstraints _ -> true
  | QEvent e -> is_non_injective_event e
  | NestedQuery q -> is_non_injective_query q
  | QAnd(concl1,concl2)
  | QOr(concl1,concl2) -> is_non_injective_conclusion_query concl1 && is_non_injective_conclusion_query concl2

and is_non_injective_query = function
  | Before(el,concl) ->
      List.for_all is_non_injective_event el && is_non_injective_conclusion_query concl

let is_simple_query q = is_non_nested_query q && is_non_injective_query q

(* Reprogrammation of clause implication to handle implication modulo
   the equational theory
   I can be approximate in that the subsumption test may fail
   even when it is in fact true. So I do not retry all unifications
   when a future unification fails in match_facts_mod_eq,
   by raising Not_found instead of Unify when a future unification fails *)

let rec implies_ordering_function (ord_fun1:ordering_function) (ord_fun2:ordering_function) =
  match ord_fun1, ord_fun2 with
  | [], _ -> ()
  | _, [] -> raise Unify
  | (i1,_)::q1, (i2,_)::q2 when i2 > i1 -> raise Unify
  | (i1,_)::q1, (i2,_)::q2 when i2 < i1 -> implies_ordering_function ord_fun1 q2
      (* At this point, both lists start with (i,_) for the same i *)
  | (_,Less)::q1, (_,Leq)::q2 -> raise Unify
  | _::q1, _::q2 -> implies_ordering_function q1 q2

let implies_ordering_function_bool (ord_fun1:ordering_function) (ord_fun2:ordering_function) =
  try
    implies_ordering_function ord_fun1 ord_fun2;
    true
  with Unify -> false

let match_facts_mod_eq f f1 f2 = match (f1,f2) with
  | Pred(chann1, t1),Pred(chann2, t2) ->
      begin
        if chann1 != chann2 then raise Unify;
        try
          TermsEq.unify_modulo_list (fun () -> try f() with Unify -> raise Not_found) t1 t2
        with Not_found -> raise Unify
      end

let rec match_auth_hyp1_mod_eq f ((f1,(ord1,_)) as h1) = function
    [] -> raise Unify
  | ((f2,(ord2,_))::hl2) ->
        try
          implies_ordering_function ord1 ord2;
          match_facts_mod_eq f f1 f2
        with Unify ->
          match_auth_hyp1_mod_eq f h1 hl2

let rec match_auth_hyp_mod_eq f hyp1 hyp2 () =
   match hyp1 with
     [] -> f ()
   | (h1 :: hl1) -> match_auth_hyp1_mod_eq (match_auth_hyp_mod_eq f hl1 hyp2) h1 hyp2

let implies_auth_mod_eq ((hyp1, concl1, _, constr1):auth_ordered_reduction) ((hyp2, concl2, _, constr2):auth_ordered_reduction) =
  match_facts_mod_eq (fun () ->
    match_auth_hyp_mod_eq (fun () ->
      begin
        try
          let concl2' = specvar_to_var_fact (TermsEq.remove_syntactic_fact concl2) in
          let hyp2' = List.map (fun (f,_) -> specvar_to_var_fact (TermsEq.remove_syntactic_fact f)) hyp2 in
          ignore (
            TermsEq.implies_constraints_keepvars
              (concl2' :: hyp2')
              (specvar_to_var_constraints (TermsEq.remove_syntactic_constra constr2))
              (specvar_to_var_constraints (TermsEq.remove_syntactic_constra constr1))
          )
        with NoMatch -> raise Unify
      end;
    ) (Rules.reorder_ordered hyp1) hyp2 ()
  ) concl1 concl2

let implies_auth_rule_mod_eq (r1:auth_ordered_reduction) (r2:auth_ordered_reduction) =
  assert (!current_bound_vars == []);
  put_constants_rule r2;
  let r2' = copy_auth_rule2 r2 in
  cleanup();
  try
    Terms.auto_cleanup (fun () ->
      implies_auth_mod_eq r1 r2'
    );
    true
  with Unify -> false

let rec remove_subsumed_mod_eq = function
    [] -> []
  | (a::l) ->
      if List.exists (fun r1 -> implies_auth_rule_mod_eq r1 a) l then
        remove_subsumed_mod_eq l
      else
        a::(remove_subsumed_mod_eq (List.filter (fun r2 -> not (implies_auth_rule_mod_eq a r2)) l))

(* Improved verification of predicates in clauses *)

let init_clauses = ref []

let clauses_for_preds = ref None

let get_clauses_for_preds () =
  match !clauses_for_preds with
    | Some l -> l
    | None ->
        let clauses = ref [] in

        List.iter (fun (hyp1, concl1, constra1, tag1) ->
          TermsEq.close_rule_destr_eq (fun (hyp, concl, constra) ->
            clauses := (hyp, concl, Rule(-1, tag1, hyp, concl, constra), constra) :: (!clauses)
          ) (hyp1, concl1, constra1)
        ) (!Param.current_state).pi_input_clauses;

        List.iter (fun fact ->
          TermsEq.close_rule_destr_eq (fun (hyp, concl, constra) ->
            clauses := (hyp, concl, Rule(-1, LblClause, hyp, concl, constra), constra) :: (!clauses)
          ) ([], fact, Terms.true_constraints)
        ) (!Param.current_state).pi_elimtrue;

        Terms.cleanup();

        List.iter (function
          | (_,_,Rule(_,(Apply _ | Init | PhaseChange | TblPhaseChange), _,_,_), _) as cl -> clauses := cl :: (!clauses)
          | _ -> ()
        ) (!init_clauses);

        clauses_for_preds := Some (!clauses);
        !clauses

(* Generation of request rules *)

let rec split_event_constra = function 
  | [] -> [], Terms.true_constraints
  | QNeq ((t1,_),(t2,_)) :: q_evl -> 
      let constra = Terms.constraints_of_neq t1 t2 in
      let evl', constra' = split_event_constra q_evl in
      evl', Terms.wedge_constraints constra constra'
  | QGeq ((t1,_),(t2,_)) :: q_evl -> 
      let constra = Terms.constraints_of_geq t1 t2 in
      let evl', constra' = split_event_constra q_evl in
      evl', Terms.wedge_constraints constra constra'
  | QIsNat t :: q_evl -> 
      let constra = Terms.constraints_of_is_nat t in
      let evl', constra' = split_event_constra q_evl in
      evl', Terms.wedge_constraints constra constra'
  | ev :: q_evl ->
        let evl', constra' = split_event_constra q_evl in
        ev::evl', constra'

let event_to_end_fact = function
  | QSEvent(_,_,None,_,(FunApp(f,l) as param)) ->
      if (Pievent.get_event_status (!Param.current_state) f).end_status = WithOcc
      then
        let v = Var(Terms.new_var ~orig:false "endocc" Param.occurrence_type) in
        Pred(Param.inj_event_pred, [param;v])
      else
        Pred(Param.event_pred, [param])
  | QSEvent(_,_,Some occ,_,(FunApp(f,l) as param)) ->
      assert ((Pievent.get_event_status (!Param.current_state) f).end_status = WithOcc);
      Pred(Param.inj_event_pred,[param;occ])
  | QSEvent _ -> user_error ("Events should be function applications")
  | QSEvent2(t1,t2) -> Pred(Param.event2_pred,[t1;t2])
  | QFact(p,ord_fun,l,_) -> Pred(p,l)
  | QNeq _ | QEq _ | QGeq _ | QIsNat _ | QGr _-> internal_error "no Neq, Eq, Geq, Ge, IsNat queries"

let event_list_to_rule evl = 
  let evl_no_constra, constra = split_event_constra evl in
  match evl_no_constra with
  | [e] ->
      let g = event_to_end_fact e in
      ([g], g, Rule(-1, Goal, [g], g, constra), constra)
  | el ->
      let hyp = List.map event_to_end_fact el in
      let pl = List.map (function Pred(p,_) -> p) hyp
      in
      let combined_pred = Param.get_pred (Combined(pl)) in
      let args = List.concat (List.map (function Pred(_,l) -> l) hyp)
      in
      let concl = Pred(combined_pred, args) in
      (hyp, concl, Rule(-1, GoalCombined, hyp, concl, constra), constra)

let generate_initial_request_rule_no_order (Before(el,_)) =
  let ((hypl,_,_,_) as rule) = event_list_to_rule el in
  if Selfun.exists_ignored_nounif ()
  then
    let order_data = List.map (fun _ -> [],!Param.initial_nb_of_nounif_ignore) hypl in
    { rule = rule; order_data = Some order_data }
  else
    { rule = rule; order_data = None }

let generate_initial_request_rule (Before(el,_)) =
  let ((hypl,_,_,_) as rule) = event_list_to_rule el in
  let order_data =
    List.mapi (fun i hyp ->
      (* i starts at 0 but ordering function starts at 1.
         We only add ordering function on facts that can accept them. Predicates
         defined by the user do not accept ordering functions for instance. *)
      let ord_fun = Rules.create_ordered_fact [i+1,Leq] hyp in
      let init_nounif = if Selfun.exists_ignored_nounif () then !Param.initial_nb_of_nounif_ignore else 0 in
      ord_fun,init_nounif
    ) hypl
  in
  { rule = rule; order_data = Some order_data }

(* These functions should only be applied on non nested non injective queries *)
let require_order_event = function
  | QSEvent(inj,ord_fun,_,at,_) ->
      assert(at = None);
      assert(inj = None);
      ord_fun <> []
  | QFact(_,ord_fun,_,_) ->
      ord_fun <> []
  | _ -> false

let rec require_order_concl_query = function
  | QTrue | QFalse | QConstraints _ -> false
  | QEvent ev -> require_order_event ev
  | NestedQuery _ -> Parsing_helper.internal_error "[piauth.ml >> require_order_concl_query] Unexpected nested query"
  | QAnd(concl1,concl2)
  | QOr(concl1,concl2) -> require_order_concl_query concl1 || require_order_concl_query concl2

let require_order (Before(_,concl)) = require_order_concl_query concl

(* Generation of occurrence and hypothesis from the conclusion *)

module IntComp =
  struct
    type t = int
    let compare = compare
  end

module IntMap = Map.Make(IntComp)

type injective_data =
  {
    list_predicates : predicate list;
    arguments : term list;
    occurrences : term list
  }

(* An index of the collector corresponds to the occurrence of an event [evq] in the query.
  To each index is associated a list of tuples (ev,clause,occ_concl) where:
  - [ev] is the event of the hypothesis of [clause] matching [evq]
  - [clause] is the clause being checked (typically obtain by [resolve_hyp])
  - [occ_concl] are the occurrences of events in the conclusion of [clause] that are
    matched with injective events from the premise of the query.
*)
let current_inj_collector = ref IntMap.empty

let add_in_inj_collector clause occ_concl occ_list inj_data =
  List.iter (fun (i,ev) ->
    try
      let l = IntMap.find i !current_inj_collector in
      current_inj_collector := IntMap.add i ((ev,clause,occ_concl,inj_data)::l) !current_inj_collector
    with Not_found ->
      current_inj_collector := IntMap.add i [ev,clause,occ_concl,inj_data] !current_inj_collector
    (* Only valid in version 4.06.0 of OCaml
      current_inj_collector :=
      IntMap.update i (function
        | None -> Some [ev,clause,occ_concl,inj_data]
        | Some l -> Some ((ev,clause,occ_concl,inj_data)::l)
      ) !current_inj_collector*)
  ) occ_list

let rec occurrence_of_conclusion_predicate_rec initial_nb_premise n evl args = match evl with
  | [] ->
      if args = []
      then [],[]
      else Parsing_helper.internal_error "[piauth.ml >> occurrence_of_conclusion_predicate_rec] Conclusion does not match the query."
  | QSEvent(inj,_,_,_,(FunApp(f,_)))::evl' ->
      begin match (Pievent.get_event_status (!Param.current_state) f).end_status, args with
        | WithOcc, ev::occ::args_q ->
            (* In such a case, the end predicate is injective *)
            let (hypl,occ_concl) = occurrence_of_conclusion_predicate_rec initial_nb_premise (n-1) evl' args_q in
            let hypl' = match (Pievent.get_event_status (!Param.current_state) f).begin_status with
              | No -> hypl
              | NoOcc -> (n,(Pred(Param.event_pred_block,[ev]),[-n,Leq])) :: hypl
              | WithOcc -> (n,(Pred(Param.inj_event_pred_block,[ev; occ]),[-n,Leq])) :: hypl
            in
            if inj = None || (-n) > initial_nb_premise
            then (hypl',occ_concl)
            else (hypl',occ::occ_concl)
        | NoOcc, ev::args_q ->
            (* In such a case, the end predicate is non injective.
               Moreover, the begin status can only be No or NoOcc. *)
            let (hypl,occ_concl) = occurrence_of_conclusion_predicate_rec initial_nb_premise (n-1) evl' args_q in
            let hypl' = match (Pievent.get_event_status (!Param.current_state) f).begin_status with
              | No -> hypl
              | NoOcc -> (n,(Pred(Param.event_pred_block,[ev]),[-n,Leq])) :: hypl
              | _ -> Parsing_helper.internal_error "[piauth.ml >> occurrence_of_conclusion_predicate_rec] Cannot be WithOcc status."
            in
            (hypl',occ_concl)
        | _ -> Parsing_helper.internal_error "[piauth.ml >> occurrence_of_conclusion_predicate_rec] The predicate cannot have a No end_status while being in the premise of the query."
      end
  | QSEvent2(t1,t2)::evl' ->
      let args_p', rest_args = split_list 2 args in
      let (hypl,occ_concl) = occurrence_of_conclusion_predicate_rec initial_nb_premise (n-1) evl' rest_args in
      ((n,(Pred(Param.event2_pred_block,[t1;t2]),[-n,Leq]))::hypl,occ_concl)
  | QFact(p,_,args_p,_)::evl' ->
      let nb_args = List.length args_p in
      let args_p', rest_args = split_list nb_args args in
      let fact = Pred(p,args_p') in
      let ord_fun = Rules.create_ordered_fact [-n,Leq] fact in
      let (hypl,occ_concl) = occurrence_of_conclusion_predicate_rec initial_nb_premise (n-1) evl' rest_args in
      ((n,(fact,ord_fun))::hypl,occ_concl)
  | _ -> internal_error "[piauth.ml >> occurrence_of_conclusion_predicate_rec] Unexpected case."

(* [occurrence_and_hyp_of_conclusion_predicate evl pred] returns a pair of list [hyp_ev], [occ_concl] where
    - [hyp_ev] are the non-injective events and predicates from the conclusion that will be added in the hypotheses of the clause.
    - [occ_concl] are the occurrences of events in the conclusion of [clause] that are
      matched with injective events from the premise of the query.
   When we want to prove a trivial query such as event(A) ==> event(A), the clause generated by proverif does not
   contain begin(A) -> end(A) but only -> end(A). This is why we need to add begin(A) to the hypotheses of clause.
   This is however not the case when events are injective (hence the distinction in [occurrence_of_conclusion_predicate_rec]).

   [occ_concl] corresponds to the function occ_n(C)\sigma from the technical report where
     - n = initial_nb_premise
     - \sigma is the substitution of the solution.
*)
let occurrence_and_hyp_of_conclusion_predicate initial_nb_premise evl = function
  | Pred({ p_info = Combined _; _}, args) ->
      occurrence_of_conclusion_predicate_rec initial_nb_premise (-1) evl args
  | Pred(p,[FunApp(f,_) as ev;occ]) when p == Param.inj_event_pred ->
      assert(initial_nb_premise = 1);
      let hypl = match (Pievent.get_event_status (!Param.current_state) f).begin_status with
        | No -> []
        | NoOcc -> [(-1,(Pred(Param.event_pred_block,[ev]),[1,Leq]))]
        | WithOcc -> [(-1,(Pred(Param.inj_event_pred_block,[ev; occ]),[1,Leq]))]
      in
      let occ_concl =  match evl with
        | [QSEvent(None,_,_,_,(FunApp(_,_)))] -> []
        | _ -> [occ]
      in
      hypl,occ_concl
  | Pred(p,[FunApp(f,_) as ev]) when p == Param.event_pred ->
      assert(initial_nb_premise = 1);
      let hypl = match (Pievent.get_event_status (!Param.current_state) f).begin_status with
        | No -> []
        | _ -> [(-1,(Pred(Param.event_pred_block,[ev]),[1,Leq]))]
      in
      hypl,[]
  | Pred(p,[FunApp(f,_) as ev1;ev2]) when p == Param.event2_pred ->
      assert(initial_nb_premise = 1);
      let hypl = match (Pievent.get_event_status (!Param.current_state) f).begin_status with
        | No -> []
        | _ -> [(-1,(Pred(Param.event2_pred_block,[ev1;ev2]),[1,Leq]))]
      in
      hypl,[]
  | ev ->
      assert(initial_nb_premise = 1);
      [-1,(ev,Rules.create_ordered_fact [1,Leq] ev)],[]

exception InjectivityUnverifiable

let get_sid n args =
  let rec get_sid_rec args pim = match args, pim with
    | [],[] -> None
    | [], _ | _, [] -> Parsing_helper.internal_error "[piauth.ml >> get_sid] Unexpected argument."
    | sid::_,(MSid _)::_ -> Some sid
    | _::pi_q, _::pim_q -> get_sid_rec pi_q pim_q
  in
  get_sid_rec args n.prev_inputs_meaning

let generate_constra_occ constra_l occ_concl1 occ_concl2 =
  try
    let constra_neq_disj =
      List.fold_left2 (fun acc occ1 occ2 -> match occ1, occ2 with
        | FunApp({ f_cat = Name n1; _} as f1,args1), FunApp( {f_cat = Name n2; _} as f2,args2) ->
            if f1 == f2
            then
              match get_sid n1 args1, get_sid n2 args2 with
                | None, None -> acc
                | Some sid1, Some sid2 -> (sid1,sid2) :: acc
                | _ -> Parsing_helper.internal_error "[generate_constra_occ] Should always have the same sid pattern"
            else raise Unify
        | _ -> Parsing_helper.internal_error "[generate_constra_occ] Should always be names."
      ) [] occ_concl1 occ_concl2
    in
    if constra_neq_disj = []
    then raise TermsEq.FalseConstraint
    else { constra_l with neq = constra_neq_disj::constra_l.neq }
  with
    | TermsEq.FalseConstraint -> raise Unify
    | Unify -> constra_l

let generate_injective_data evl =
  let is_inj = ref false in

  let l_pred_occ =
    List.map (function
      | QSEvent(inj,_,_,_,FunApp(f,_)) ->
          let need_occ =
            if inj = None
            then false
            else (is_inj := true; true)
          in
          if (Pievent.get_event_status (!Param.current_state) f).end_status = WithOcc
          then Param.inj_event_pred, need_occ
          else Param.event_pred, need_occ
      | QSEvent2 _ -> Param.event2_pred, false
      | QFact(p,_,_,_) -> p,false
      | _ -> internal_error "[piauth.ml >> generate_injective_data] Unexpected case."
    ) evl
  in

  if !is_inj
  then
    let l_pred = List.map (fun (p,_) -> p) l_pred_occ in
    let (args,occs) =
      List.fold_right (fun (p,b) (acc_args,acc_occ) ->
        if p == Param.inj_event_pred
        then
          let x_occ = Var(Terms.new_var ~orig:false "endocc" Param.occurrence_type) in
          let x_ev = Terms.new_var_def_term Param.event_type in
          if b
          then (x_ev::x_occ::acc_args, x_occ::acc_occ)
          else (x_ev::x_occ::acc_args, acc_occ)
        else
          ((List.fold_right (fun t acc -> (Terms.new_var_def_term t)::acc) p.p_type acc_args),acc_occ)
      ) l_pred_occ ([],[])
    in
    Some { list_predicates = l_pred; arguments = args; occurrences = occs }
  else None

let copy_injective_data inj_data =
  Terms.auto_cleanup (fun () ->
    { inj_data with
      arguments = List.map Terms.copy_term inj_data.arguments;
      occurrences = List.map Terms.copy_term inj_data.occurrences }
  )

(* [compare_two_clauses ((n1,ev1),rule1,occ_concl1,injdata1) ((n2,ev2),rule2,occ_concl2,injdata2)] checks that the two clauses
  satisfies injectivity with respect to an injective event [ev] in the conclusion of the query.
    - [ni] is the position of [evi] in the hypotheses [rulei] matching [ev].
    - [occ_concli] are the occurrences of events in the conclusion of [rulei] that are matched with injective events from the premise of the query
    - [inj_datai] is the injectivity information generated by [generate_injective_data].
  The function generate a clause combining [rule1] and [rule2] that unifies [ev1] and [ev2] and adds the disequality [occ_concl1 <> occ_concl2].
  If the hypotheses of the resulting clause do not yield a contradiction by normalisation, then the injectivity cannot be proved.
*)
let compare_two_clauses lemmas ((n1,ev1),(hyp1,concl1,hist1,constra1),occ_concl1,inj_data1) ((n2,ev2),(hyp2,concl2,hist2,constra2),occ_concl2,inj_data2) =
  try
    Terms.auto_cleanup (fun () ->
      Terms.unify_facts ev1 ev2;
      let inj_data1 = copy_injective_data inj_data1 in
      let inj_data2 = copy_injective_data inj_data2 in
      let pred_combined = Param.get_pred (Combined(inj_data1.list_predicates @ inj_data2.list_predicates)) in
      let rule_combined =
        let simple_pred1 = match inj_data1.list_predicates with
          | [p] -> p
          | _ -> Param.get_pred (Combined inj_data1.list_predicates)
        in
        let simple_pred2 = match inj_data2.list_predicates with
          | [p] -> p
          | _ -> Param.get_pred (Combined inj_data2.list_predicates)
        in
        let hyp = [Pred(simple_pred1,inj_data1.arguments);Pred(simple_pred2,inj_data2.arguments)]
        and concl = Pred(pred_combined,inj_data1.arguments@inj_data2.arguments)
        and constra = { neq = [List.map2 (fun t1 t2 -> (t1,t2)) inj_data1.occurrences inj_data2.occurrences]; is_nat = []; is_not_nat = []; geq = [] } in
        Rule(-1,GoalInjective,hyp,concl,constra)
      in

      let constra_combined = generate_constra_occ (Terms.wedge_constraints constra1 constra2) occ_concl1 occ_concl2 in
      let concl_combined = match concl1,concl2 with
        | Pred(p1,args1), Pred(p2,args2) -> Pred(pred_combined,args1@args2)
      in

      let hist_combined =
        let inj =
          Terms.auto_cleanup (fun () ->
            if n1 >= 0 && n2 >= 0
            then DoubleIndex(n1,n2 + (List.length hyp1))
            else if n1 >= 0
            then SingleIndex(copy_fact2 concl_combined, copy_fact2 ev2, n1)
            else if n2 >= 0
            then SingleIndex(copy_fact2 concl_combined, copy_fact2 ev1, n2 + (List.length hyp1))
            else NoIndex(copy_fact2 concl_combined)
          )
        in

        HInjectivity(inj,Resolution(hist1,0,(Resolution(hist2,1,rule_combined))))
      in

      let clause = (hyp1@hyp2,concl_combined,hist_combined,constra_combined) in
      let clause' = copy_rule2 clause in
      let ord_rule = { rule = clause'; order_data = None } in

      auto_cleanup (fun () ->
        let clauses = Rules.solving_request_rule ~close_equation:false ~apply_not:true lemmas [] ord_rule in
        if clauses != []
        then
          begin
            faulty_clauses_injective := clauses @ !faulty_clauses_injective;
            raise InjectivityUnverifiable
          end
      )
    )
  with
    | Unify -> ()
    | InjectivityUnverifiable -> raise Unify

let check_injectivity restwork lemmas injectivity_data_op positive_clause = match injectivity_data_op,positive_clause with
  | None,_
  | Some _, None -> restwork () (* It can happen that there is injectivity_data but no positive clause. Eg : inj-A ==> inj-B || attacker *)
  | Some injectivity_data, Some (auth_clause,occ_list,occ_concl) ->
      let old_inj_collector = !current_inj_collector in
      let clause = rule_of_auth_ordered_rule auth_clause in
      try
        (* We make a copy of the clause (because we need to check a clause vs herself) *)
        let (clause2, occ_list2, occ_concl2) =
          Terms.auto_cleanup (fun () ->
            let clause = copy_rule2_no_cleanup clause in
            let occ_concl = List.map copy_term2 occ_concl in
            let occ_list = List.map (fun (i,(n,ev)) -> (i,(n,copy_fact2 ev))) occ_list in
            clause,occ_list, occ_concl
          )
        in

        (* We add this copy to the collector and we will do the tests with the first one. *)
        add_in_inj_collector clause2 occ_concl2 occ_list2 injectivity_data;
        let unify_found = ref false in
        (* We now compare the clause with the collector *)
        List.iter (fun (i1,ev1) ->
          let stored_clauses_list = IntMap.find i1 !current_inj_collector in
          (* Cannot raise Not_Found since the first copy was added in the collector *)
          List.iter (fun (ev2,cl2,occ_cl2,inj_data2) ->
            try
              compare_two_clauses lemmas (ev1,clause,occ_concl,injectivity_data) (ev2,cl2,occ_cl2,inj_data2)
            with Unify -> unify_found := true
          ) stored_clauses_list
        ) occ_list;
        if !unify_found
        then raise Unify
        else restwork ();
        current_inj_collector := old_inj_collector
      with Unify ->
        current_inj_collector := old_inj_collector;
        raise Unify

(* Matching functions *)

(* Note that for bievents, we do not need to check ordering functions since queries on bitraces
   do not contain ordering constraints. Hence conditions on ordering functions are trivially satisfied. *)
let rec match_event2 restwork (ev1_query,ev2_query) = function
  | [] -> raise Unify
  | (ev1,ev2)::q ->
      try
        TermsEq.unify_modulo_list restwork [ev1;ev2] [ev1_query;ev2_query]
      with Unify -> match_event2 restwork (ev1_query,ev2_query) q

let rec match_event2_list restwork ev_l hypl = match ev_l with
  | [] -> restwork ()
  | ev::q ->
      match_event2 (fun () ->
        match_event2_list restwork q hypl
      ) ev hypl

let rec match_event restwork ev_query ord_fun_query occ_query = function
  | [] -> raise Unify
  | ((_,(Pred(pred,args),ord_fun)) as p) ::q ->
      if pred != Param.event_pred_block && pred != Param.inj_event_pred_block
      then Parsing_helper.internal_error "[piauth.ml >> match_event] The list should only contain events.";

      begin
        try
          implies_ordering_function ord_fun_query ord_fun;
          let list_query,list_event = match occ_query with
            | Some occ ->
                if pred == Param.inj_event_pred_block
                then [ev_query;occ], args
                else
                  (* All events with an occurrence in the query have the status WithOcc. Hence
                     if the predicate is event_pred_block then we know the two events cannot unify. *)
                  raise Unify
            | _ -> [ev_query], [List.hd args]
          in

          TermsEq.unify_modulo_list (fun () ->
            restwork p
          ) list_event list_query
        with Unify -> match_event restwork ev_query ord_fun_query occ_query q
      end

let match_premise (restwork:unit->unit) (premise:fact) (concl:fact) = match premise,concl with
  | Pred(chann1, args1),Pred(chann2, args2) ->
      if chann1 != chann2 then Parsing_helper.internal_error "[piauth.ml >> match_premise] Should have the same predicate.";
      TermsEq.unify_modulo_list restwork args1 args2

(* The function restwork takes as input a list of (k,ev,occ) where k is the injective index *)
let rec match_event_list restwork ev_l hypl = match ev_l with
  | [] -> restwork []
  | (None,ord_fun,occ,ev)::q_ev ->
      match_event (fun _ ->
        match_event_list (fun ind_occ_l  ->
          restwork ind_occ_l
        ) q_ev hypl
      ) ev ord_fun occ hypl
  | (Some k,ord_fun,occ,ev)::q_ev ->
      match_event (fun (i,(ev_hyp,_)) ->
        match_event_list (fun ind_occ_l ->
          restwork ((k,(i,ev_hyp))::ind_occ_l)
        ) q_ev hypl
      ) ev ord_fun occ hypl

let rec match_premise_nested_query restwork g_nested hypl = match g_nested with
  | [] -> restwork [] []
  | ((None,g_ord_fun,g_occ,g_ev),nested_concl)::q_ev ->
      match_event (fun (i,(ev,ord_fun)) ->
        match_premise_nested_query (fun ind_occ_l matching_nested ->
          restwork ind_occ_l ((None,i,ev,ord_fun,g_ord_fun,nested_concl)::matching_nested)
        ) q_ev hypl
      ) g_ev g_ord_fun g_occ hypl
  | ((Some k,g_ord_fun,g_occ,g_ev),nested_concl)::q_ev ->
      match_event (fun (i,(ev,ord_fun)) ->
        match_premise_nested_query (fun ind_occ_l matching_nested ->
          restwork ((k,(i,ev))::ind_occ_l) ((Some k,i,ev,ord_fun,g_ord_fun,nested_concl)::matching_nested)
        ) q_ev hypl
      ) g_ev g_ord_fun g_occ hypl

let rec match_predicate (restwork:int -> unit) ((p,args,ord_fun_query): predicate * term list * ordering_function ) = function
  | [] -> raise Unify
  | (n,(Pred(p',args'),ord_fun'))::q ->
      if p == Terms.unblock_predicate p'
      then
        try
          implies_ordering_function ord_fun_query ord_fun';
          TermsEq.unify_modulo_list (fun () ->
            restwork n
          ) args args'
        with Unify -> match_predicate restwork (p,args,ord_fun_query) q
      else match_predicate restwork (p,args,ord_fun_query) q

(* The function restwork takes as input a list of non-blocking predicates to check *)
let rec match_predicate_list restwork pred_l hypl = match pred_l with
  | [] -> restwork []
  | (Pred(p,args),ord_fun)::q ->
      begin
        try
          (* Try to see if the predicate is already included in the hypotheses *)
          match_predicate (fun _ ->
            match_predicate_list (fun pred_nonblock_to_check ->
              restwork pred_nonblock_to_check
            ) q hypl
          ) (p,args,ord_fun) hypl
        with Unify ->
          if p.p_prop land Param.pred_BLOCKING != 0
          then raise Unify
          else
            match_predicate_list (fun pred_nonblock_to_check ->
              restwork ((Pred(p,args),ord_fun)::pred_nonblock_to_check)
            ) q hypl
      end

let rec match_predicate_block restwork (p,args) = function
  | [] -> raise Unify
  | Pred(p',args')::q when p.p_prop land Param.pred_BLOCKING != 0 ->
      if p == p'
      then
        try
          TermsEq.unify_modulo_list (fun () ->
              restwork ()
          ) args args'
        with Unify -> match_predicate_block restwork (p,args) q
      else match_predicate_block restwork (p,args) q
  | _::q -> match_predicate_block restwork (p,args) q

let rec match_predicate_block_list pred_l hypl = match pred_l with
  | [] -> ()
  | Pred(p,args)::q when p.p_prop land Param.pred_BLOCKING != 0 ->
      match_predicate_block (fun () ->
        match_predicate_block_list q hypl
      ) (p,args) hypl
  | _ -> raise Unify

(* g_constra only contains the disequalities that cannot be negated and thus should be checked.
   Since we will negate the predicate in [g_pred_block_to_negate], we check the unblock predicate
   as if the predicates in [g_pred_block_to_negate] are in the hypotheses of the clause. *)
let match_unblock_predicates_same_ord_fun lemmas g_pred_unblock g_constra pred_unblock_cl pred_block_cl =
  assert (g_pred_unblock <> []);

  Terms.auto_cleanup (fun () ->
    let bad_fact = Pred(Param.bad_pred, []) in
    let pred_unblock_cl' = List.map Terms.copy_fact2 pred_unblock_cl in
    let pred_block_cl' = List.map Terms.copy_fact2 pred_block_cl in
    let g_pred_unblock' = List.map Terms.copy_fact2 g_pred_unblock in
    let g_constra' = Terms.copy_constra2 g_constra in
    Terms.cleanup();
    (* Let sigma_0 the substitution that replaces all variables by
       distinct constants. Let H => C the clause found by ProVerif.
       We show that we can prove an instance of the hypothesis of the query
       from \sigma_0 H. We should prove an instance of the hypothesis of the query
       from any instance of H. The derivation obtained using \sigma_0 H
       can converted into a derivation using \sigma H by replacing the
       constants with other terms. All steps remain valid except that
       the inequalities may no longer be true. Hence, we collect inequalities
       used in the derivation and further check that they are implied by
       the inequalities in H, by passing them to the function f. *)
    let unblocked_predicate_clauses =
      List.fold_left (fun acc fact -> match fact with
        | Pred(p,_) when p == Param.event2_pred_block || p == Param.event_pred_block || p == Param.inj_event_pred_block -> assert false
        | Pred({p_info = Block p;_},args) ->
            ([], Pred(p,args), Rule(-1, LblNone, [], Pred(p,args), Terms.true_constraints), Terms.true_constraints) :: acc
        | _ -> acc
      ) [] pred_block_cl'
    in
    let clauses =
       (g_pred_unblock', bad_fact, Rule(-1, LblNone, g_pred_unblock', bad_fact, g_constra'), g_constra') ::
       (get_clauses_for_preds()) @
       (List.map (fun fact -> ([], fact, Rule(-1, LblNone, [], fact, Terms.true_constraints), Terms.true_constraints)) pred_unblock_cl') @
       unblocked_predicate_clauses
    in
    Display.auto_cleanup_display (fun () ->
      Display.Text.display_inside_query g_pred_unblock' g_constra' pred_block_cl' pred_unblock_cl';
      incr Param.inside_query_number;
      let inums = string_of_int (!Param.inside_query_number) in

      if !Param.html_output then
        begin
          Display.LangHtml.openfile ((!Param.html_dir) ^ "/inside" ^ inums ^ ".html") ("ProVerif: inside query " ^ inums);
          Display.Html.display_inside_query g_pred_unblock' g_constra' pred_block_cl' g_pred_unblock'
        end;
      (* the resolution prover must be _sound_ for this call
         while for other calls it must be _complete_.
         The function sound_bad_derivable is sound provided the clause
         do not contain "any_name" and contain unary attacker predicates,
         which is the case here. *)
      let cl = Rules.sound_bad_derivable lemmas clauses in
      try
        let (hyp, concl, hist, constra) =
          List.find (function
            | (hyp, _, _, c) when Terms.is_true_constraints c ->
                begin
                  try
                    match_predicate_block_list hyp pred_block_cl';
                    true
                  with Unify -> false
                end
            | _ -> false) cl
        in
        (* Should I try other clauses in cl in case of subsequent failure?
           It may help, but that would be just by chance, since the clauses
           that use different inequalities on constants of \sigma_0 H
           in their derivation are typically removed by subsumption.
           Only clauses that have different hypotheses are kept. *)

        (* collect all inequalities in the derivation of cl_found *)
        let derivation = History.build_fact_tree hist in
        let g_constra'' = Reduction_helper.collect_constraints derivation in
        Reduction_helper.close_constraints g_constra'';
        begin
          (* Success: managed to prove the facts in hyp1_preds' *)
          Display.Text.display_inside_query_success g_constra'';

          if !Param.html_output
          then
            begin
              Display.Html.display_inside_query_success g_constra'';
              Display.LangHtml.close ();
              Display.Html.print_line ("<A HREF=\"inside" ^ inums ^ ".html\">Inside query: proof succeeded</A>")
            end;

          map_constraints (fun t -> specvar_to_var (TermsEq.remove_syntactic_term t)) g_constra''
        end
      with Not_found ->
        begin
          (* Failure: could not prove some fact in hyp1_preds' *)
          Display.Text.print_line "Inside query: proof failed";

          if !Param.html_output then
            begin
            Display.Html.print_line "Inside query: proof failed";
            Display.LangHtml.close();
            Display.Html.print_line ("<A HREF=\"inside" ^ inums ^ ".html\">Inside query: proof failed</A>")
            end;

          raise Unify
        end
    )
  )

let match_unblock_predicates restwork lemmas g_pred_unblock g_constra pred_unblock_cl pred_block_cl =
  if g_pred_unblock = []
  then restwork (map_constraints (fun t -> specvar_to_var (TermsEq.remove_syntactic_term t)) g_constra)
  else
    (* We prove user-defined predicates by groups that have the same ordering function.
       [g_pred_unblock_partition] is a list of (ord_fun, predicates that have that ord_fun)
       in [g_pred_unblock]. *)

    let compare_g_pred (_,ord_fun1) (_,ord_fun2) = compare ord_fun1 ord_fun2 in
    let g_pred_unblock_sorted = List.sort compare_g_pred g_pred_unblock in

    let rec partition_g_pred cur_ord_fun cur_g_pred_acc = function
      | [] -> [cur_ord_fun,cur_g_pred_acc]
      | (fact,ord_fun)::q when ord_fun = cur_ord_fun -> partition_g_pred cur_ord_fun (fact::cur_g_pred_acc) q
      | (fact,ord_fun)::q -> (cur_ord_fun,cur_g_pred_acc)::(partition_g_pred ord_fun [fact] q)
    in

    let (fact,ord_fun) = List.hd g_pred_unblock_sorted in
    let g_pred_unblock_partition = partition_g_pred ord_fun [fact] (List.tl g_pred_unblock_sorted) in

    let rec prove_through_g_pred = function
      | [] -> true_constraints
      | (g_ord_fun,g_preds)::q ->
          let pred_unblock_cl' =
            List.fold_left (fun acc (_,(f,ord_fun)) ->
              if implies_ordering_function_bool g_ord_fun ord_fun then f::acc else acc
            ) [] pred_unblock_cl
          in
          let pred_block_cl' =
            List.fold_left (fun acc (_,(f,ord_fun)) ->
              if implies_ordering_function_bool g_ord_fun ord_fun then f::acc else acc
            ) [] pred_block_cl
          in
          let constra = match_unblock_predicates_same_ord_fun lemmas g_preds g_constra pred_unblock_cl' pred_block_cl' in
          wedge_constraints constra (prove_through_g_pred q)
    in

    let constra = prove_through_g_pred g_pred_unblock_partition in
    restwork constra

(* [negate_predicate_constra] generates new clauses by negating the disequalities and inequalities.
   To obtain the correct history, we use HCaseDistinction to indicate how to obtain the negated disequalities and inequalities.
   We assume here that there is no disjunction of disequalities. Moreover we assume that there is no is_not_nat predicate
   to negate.
   Note: the constraints [g_constra_to_negate] are closed under the equational theory before calling this function.
 *)

let add_ordered_rules ord_rules accu =
  let new_clauses =
    List.fold_left (fun acc ord_rule ->
      (auth_ordered_rule_of_ordered_rule ord_rule) :: acc
    ) !accu ord_rules
  in
  accu := new_clauses

let negate_predicate_constra lemmas ind_lemmas (hypl,concl,hist,constra) g_constra_to_negate =
  assert (g_constra_to_negate.is_not_nat == []);

  let accu = ref [] in
  let (hypl,ord_data,need_ord_data) =
    List.fold_right (fun (hyp,(ord_fun,i)) (acc_hyp,acc_ord,need_ord_data) ->
      (hyp::acc_hyp,(ord_fun,i)::acc_ord,need_ord_data || (ord_fun != []) || i <> 0)
    ) hypl ([],[],false)
  in
  let order_data_op = if need_ord_data then Some ord_data else None in

  List.iter (fun t ->
    let t' = specvar_to_var (TermsEq.remove_syntactic_term t) in

    let hist' =
      Terms.auto_cleanup (fun () ->
        let concl'' = Terms.copy_fact2 concl in
        let hypl'' = List.map Terms.copy_fact2 hypl in
        let t'' = Terms.copy_term2 t' in
        HCaseDistinction(concl'',hypl'',[],(Terms.constraints_of_is_not_nat t''), hist)
      )
    in
    let clause1 = (hypl,concl, hist', { constra with is_not_nat = t'::constra.is_not_nat }) in
    let clause2 = copy_rule2 clause1 in
    let ord_rule = { rule = clause2; order_data = order_data_op } in

    Terms.auto_cleanup (fun () ->
      let ord_rules = Rules.solving_request_rule ~close_equation:false ~apply_not:true lemmas ind_lemmas ord_rule in
      add_ordered_rules ord_rules accu
    )
  ) g_constra_to_negate.is_nat;

  List.iter (fun (t1,n,t2) ->
    let t1' = specvar_to_var (TermsEq.remove_syntactic_term t1) in
    let t2' = specvar_to_var (TermsEq.remove_syntactic_term t2) in

    (* We generate the histories of the three cases.
        - hist1 is the history when t1 is not a natural number
        - hist2 is the history when t2 is not a natural number
        - hist3 is the history where t1 + n < t2, i.e. t2 - n - 1 >= t1 *)
    let (hist1, hist2, hist3) =
      Terms.auto_cleanup (fun () ->
        let concl'' = Terms.copy_fact2 concl in
        let hypl'' = List.map Terms.copy_fact2 hypl in
        let t1'' = Terms.copy_term2 t1' in
        let t2'' = Terms.copy_term2 t2' in
        HCaseDistinction(concl'',hypl'',[],(Terms.constraints_of_is_not_nat t1''), hist),
        HCaseDistinction(concl'',hypl'',[],(Terms.constraints_of_is_not_nat t2''), hist),
        HCaseDistinction(concl'',hypl'',[],{ neq = []; is_nat = []; is_not_nat = []; geq = [t2'',(-n-1),t1'']}, hist)
      )
    in

    let clause1 = (hypl,concl, hist1, { constra with is_not_nat = t1'::constra.is_not_nat }) in
    let clause2 = (hypl,concl, hist2, { constra with is_not_nat = t2'::constra.is_not_nat }) in
    let clause3 = (hypl,concl, hist3, { constra with geq = (t2',(-n-1),t1')::constra.geq }) in

    List.iter (fun cl ->
      let cl' = copy_rule2 cl in
      let ord_rule = { rule = cl'; order_data = order_data_op } in
      Terms.auto_cleanup (fun () ->
        let ord_rules = Rules.solving_request_rule ~close_equation:false ~apply_not:true lemmas ind_lemmas ord_rule in
        add_ordered_rules ord_rules accu
      )
    ) [clause1;clause2;clause3]
  ) g_constra_to_negate.geq;

  List.iter (function
    | [t,t'] ->
        (* [t] and [t'] are both ground. The variables specvar are the free variables of
           [concl] or [hypl] *)
        let t1 = specvar_to_var (TermsEq.remove_syntactic_term t) in
        let t1' = specvar_to_var (TermsEq.remove_syntactic_term t') in

        (* Retreive the free variables. They should be contained the variables of [concl] and [hypl]. *)
        let free_vars = ref [] in
        Terms.get_vars free_vars t1;
        Terms.get_vars free_vars t1';

        begin
          try
            TermsEq.unify_modulo (fun () ->
              (* Retrieve the substitution *)
              let subst =
                List.fold_left (fun acc x -> match x.link with
                  | NoLink -> acc
                  | TLink t -> (x,TermsEq.remove_syntactic_term t)::acc
                  | _ -> Parsing_helper.internal_error "[piauth.ml >> negate_predicate_constra] Unexpected link."
                ) [] !free_vars
              in

              (* Remove the link to copy the history *)
              List.iter (fun (x,_) -> x.link <- NoLink) subst;
              let hist' =
                Terms.auto_cleanup (fun () ->
                  let concl' = Terms.copy_fact2 concl in
                  let hypl' = List.map Terms.copy_fact2 hypl in
                  let subst' = List.map (fun (x,t) -> Terms.copy_term2 (Var x), Terms.copy_term2 t) subst in
                  HCaseDistinction(concl',hypl',subst',Terms.true_constraints,hist)
                )
              in
              (* Relink the variables *)
              List.iter (fun (x,t) -> x.link <- TLink t) subst;

              let clause1 = (hypl,concl,hist',constra) in
              let clause2 = copy_rule2 clause1 in
              let ord_rule = { rule = clause2; order_data = order_data_op } in
              Terms.auto_cleanup (fun () ->
                let ord_rules = Rules.solving_request_rule ~close_equation:false ~apply_not:true lemmas ind_lemmas ord_rule in
                add_ordered_rules ord_rules accu;
                (* We raise Unify to ensure that all substitutions are applied *)
                raise Unify
              )
            ) t1 t1'
          with Unify ->
            (* Unify is always raised. *)
            ()
        end
    | _ -> Parsing_helper.internal_error "[piauth.ml >> negate_predicate_constra] Disequalities should not contain disjunction at this point."
  ) g_constra_to_negate.neq;

  !accu

(* We distinguish cases depending on whether [g_constra_to_add] are true or not.

   [generate_positive_clauses clause occ_concl occ_list g_constra_to_add] returns either [None] or [Some(clause')],
   where [clause'] is [clause] with the disequalities [g_constra_to_add] added
   in the hypothesis.
    The function raises [Unify] when no clause can be generated, i.e. hypotheses are false.
    The function returns [None] when there is no injectivity to check. This
    is due to the fact that we do not need to store the positive clause when there is no injectivity to check.

    Notes:
    - the constraints [g_constra_to_add] are closed under the equational theory before calling this function.
    - [negate_predicate_constra] deals with the other case by negating the constraints. *)
let generate_positive_clauses ((hypl,concl,hist,constra):auth_ordered_reduction) occ_concl occ_list g_constra_to_add =
  let g_constra_to_add1 = Terms.map_constraints (fun t -> specvar_to_var (TermsEq.remove_syntactic_term t)) g_constra_to_add in
  let occ_list1 = List.map (fun (i,(n,ev)) -> (i,(n,specvar_to_var_fact (TermsEq.remove_syntactic_fact ev)))) occ_list in
  let occ_concl1 = List.map (fun t -> specvar_to_var (TermsEq.remove_syntactic_term t)) occ_concl in
  let hypl' = List.map (fun (f,_) -> f) hypl in

  (* Check if the hypotheses of the new clause are satisfiable *)
  if not (Terms.is_true_constraints g_constra_to_add)
  then
    Terms.auto_cleanup (fun () ->
      (* Check if the hypotheses of the new clause are satisfiable *)
      let clause = (hypl',concl,hist,Terms.wedge_constraints constra g_constra_to_add1) in
      if Rules.is_hypothesis_unsatisfiable clause
      then raise Unify
    );

  if occ_list = []
  then None
  else
    let hist' =
      if Terms.is_true_constraints g_constra_to_add
      then hist
      else
        Terms.auto_cleanup (fun () ->
          let concl' = Terms.copy_fact2 concl in
          let hypl' = List.map Terms.copy_fact2 hypl' in
          let constra' = Terms.copy_constra2 g_constra_to_add1 in
          HCaseDistinction(concl',hypl',[],constra',hist)
        )
    in

    let clause1 = (hypl,concl,hist',Terms.wedge_constraints constra g_constra_to_add1) in

    Terms.auto_cleanup (fun () ->
      let clause = copy_auth_rule2_no_cleanup clause1 in
      let occ_concl = List.map copy_term2 occ_concl1 in
      let occ_list = List.map (fun (i,(n,ev)) -> (i,(n,copy_fact2 ev))) occ_list1 in
      Some (clause,occ_list, occ_concl)
    )

(* Generation of instantiated nested queries and the associated rules *)

let apply_ordering_function_on_event ord_fun = function
  | QSEvent(inj_op,ord_fun',occ,_,ev) ->
      QSEvent(inj_op,Rules.inter_ordering_fun ord_fun' ord_fun,occ,None,ev)
  | QFact(p,ord_fun',args,_) ->
      if Rules.can_pred_have_ordering_fun p
      then QFact(p,Rules.inter_ordering_fun ord_fun' ord_fun,args,None)
      else QFact(p,[],args,None)
  | g_ev -> g_ev

let conclusion_query_of_constra constra =
  let concl1 =
    List.fold_left (fun acc_q neq_l -> match neq_l with
      | [t1,t2] -> Reduction_helper.make_qand acc_q (QEvent(QNeq((t1, Parsing_helper.dummy_ext),(t2, Parsing_helper.dummy_ext))))
      | _ -> Parsing_helper.internal_error "[piauth.ml >> conclusion_query_of_constra] The constraint obtained from the query should not have disjunctions of inequalities."
    ) QTrue constra.neq
  in
  let concl2 =
    List.fold_left (fun acc_q (t1,i,t2) ->
      Reduction_helper.make_qand acc_q (QEvent(QGeq((sum_nat_term t1 i, Parsing_helper.dummy_ext),(t2, Parsing_helper.dummy_ext))))
    ) concl1 constra.geq
  in
  let concl3 =
    List.fold_left (fun acc_q t ->
      Reduction_helper.make_qand acc_q (QEvent(QIsNat t))
    ) concl2 constra.is_nat
  in
  concl3

let rec apply_ordering_function_on_conclusion ord_fun = function
  | QTrue -> QTrue
  | QFalse -> QFalse
  | QConstraints _ as q -> q (* this deals with ordering, hence irrelevant for the constraints *)
  | QEvent(ev) -> QEvent(apply_ordering_function_on_event ord_fun ev)
  | NestedQuery(Before([ev],concl)) ->
      NestedQuery(Before([apply_ordering_function_on_event ord_fun ev],concl))
  | NestedQuery _ -> Parsing_helper.internal_error "[piauth.ml >> apply_ordering_function_on_conclusion] Nested queries should have exactly one event in their premise."
  | QAnd(concl1,concl2) ->
      QAnd(apply_ordering_function_on_conclusion ord_fun concl1,apply_ordering_function_on_conclusion ord_fun concl2)
  | QOr(concl1,concl2) ->
      QOr(apply_ordering_function_on_conclusion ord_fun concl1,apply_ordering_function_on_conclusion ord_fun concl2)

let generate_nested_query_and_rule g_premise g_ev g_constra_to_check g_constra_to_add g_pred matching_nested ((hypl,concl,hist,constra):auth_ordered_reduction) =

  (* We build  the query *)
  let (g_premise_no_constra,g_premise_constra) = 
    List.partition (function
      | QNeq _ | QGeq _ | QIsNat _ -> false
      | _ -> true
    ) g_premise
  in

  let nb_fact_in_premise = List.length g_premise_no_constra in

  let premise_from_nested =
    List.map (fun (_,_,ev,_,_,_) -> match ev with
      | Pred(f,[evt;occ]) when f == Param.inj_event_pred_block -> QSEvent(None,[],Some occ,None,evt)
      | Pred(f,[evt]) -> QSEvent(None,[],None,None,evt)
      | _ -> Parsing_helper.internal_error "[piauth.ml >> generate_nested_query_and_rule] Expecting an event or injective event."
    ) matching_nested
  in
  let new_g_premise = g_premise_no_constra @ premise_from_nested @ g_premise_constra in

  let new_q_concl1 =
    List.fold_left (fun acc_q (inj_op,ord_fun,occ,ev) ->
      Reduction_helper.make_qand acc_q (QEvent(QSEvent(inj_op,ord_fun,occ,None,ev)))
    ) QTrue g_ev
  in
  (* Difference with respect to the paper: we add the matched events also to the
     conclusion of the query that we generate. That uniformizes the verification
     of injectivity, which looks only at the conclusion of the query. *)
  let new_q_concl2 =
    List.fold_left (fun acc_q (inj_op,_,ev,_,ord_fun_query,_) -> match ev with
      | Pred(f,[evt;occ]) when f == Param.inj_event_pred_block -> Reduction_helper.make_qand acc_q (QEvent(QSEvent(inj_op,ord_fun_query,Some occ,None,evt)))
      | Pred(f,[evt]) ->
          assert(inj_op = None);
          Reduction_helper.make_qand acc_q (QEvent(QSEvent(None,ord_fun_query,None,None,evt)))
      | _ -> Parsing_helper.internal_error "[piauth.ml >> generate_nested_query_and_rule] Expecting an event or injective event."
    ) new_q_concl1 matching_nested
  in
  let new_q_concl3 =
    List.fold_left (fun acc_q (Pred(p,args),ord_fun) ->
      Reduction_helper.make_qand acc_q (QEvent(QFact(p,ord_fun,args,None)))
    ) new_q_concl2 g_pred
  in
  let (new_q_concl4,_) =
    List.fold_left (fun (acc_q,i) (_,_,ev,_,ord_fun_query,concl_nested) ->
      let ord_fun_query' = ord_fun_query @ [i,Leq] in
      let concl_nested' = apply_ordering_function_on_conclusion ord_fun_query' concl_nested in
      let acc_q' = Reduction_helper.make_qand acc_q concl_nested' in
      (acc_q',i+1)
    ) (new_q_concl3,nb_fact_in_premise + 1) matching_nested
  in
  let new_q_concl5 = Reduction_helper.make_qand new_q_concl4 (conclusion_query_of_constra g_constra_to_check) in

  let new_query =
    Terms.auto_cleanup (fun () ->
      let q1 = Before(new_g_premise,new_q_concl5) in
      let q2 = copy_query q1 in
      specvar_to_var_query q2
    )
  in

  (* We build the clause *)

  let g_constra_to_add1 = Terms.map_constraints (fun t -> specvar_to_var (TermsEq.remove_syntactic_term t)) g_constra_to_add in

  let init_nounif = if Selfun.exists_ignored_nounif () then !Param.initial_nb_of_nounif_ignore else 0 in

  let fact_for_hyp =
    List.mapi (fun i (_,_,fact,ord_fun_hyp,_,_) ->
      let fact' =
        match fact with
        | Pred(f,[ev;occ]) when f == Param.inj_event_pred_block -> Pred(Param.inj_event_pred,[ev;occ])
        | Pred(_,args) -> Pred(Param.event_pred,args)
      in
      (specvar_to_var_fact (TermsEq.remove_syntactic_fact fact'),(ord_fun_hyp@[i+nb_fact_in_premise+1,Leq],init_nounif))
    ) matching_nested
  in
  let new_hypl = hypl @ fact_for_hyp in

  let (pred_for_concl,args_for_concl) =
    List.fold_right (fun (Pred(p,args),_) (acc_p,acc_a)->
      (p::acc_p,args@acc_a)
    ) fact_for_hyp ([],[])
  in

  let (new_concl,nb_fact_in_orig_concl) = match concl with
    | Pred({ p_info = Combined p_list; _}, args) ->
        let new_combined_pred = Param.get_pred (Combined (p_list@pred_for_concl)) in
        Pred(new_combined_pred,args@args_for_concl), List.length p_list
    | Pred(p,args) ->
        let new_combined_pred = Param.get_pred (Combined (p::pred_for_concl)) in
        Pred(new_combined_pred,args@args_for_concl), 1
  in

  (* Clause used for generating the history *)
  let rule_nested =
    let (old_concl_pred,args_old_concl_pred) = match concl with
      | Pred(p,_) -> p, List.map Terms.new_var_def_term p.p_type
    in
    let (fresh_fact_for_hyp, args_for_hyp) =
      List.fold_right (fun (Pred(p,_),_) (acc_f,acc_a) ->
        let args = List.map Terms.new_var_def_term p.p_type in
        Pred(p,args)::acc_f, args@acc_a
      ) fact_for_hyp ([],[])
    in
    let concl_rule = match new_concl with
      | Pred(p,_) -> Pred(p,args_old_concl_pred@args_for_hyp)
    in
    let hyp_rule = Pred(old_concl_pred,args_old_concl_pred)::fresh_fact_for_hyp in

    Rule(-1,GenerationNested,hyp_rule,concl_rule,Terms.true_constraints)
  in

  let new_hist1 =
    if Terms.is_true_constraints g_constra_to_add
    then hist
    else
      Terms.auto_cleanup (fun () ->
        let concl' = Terms.copy_fact2 concl in
        let hypl' = List.map (fun (f,_) -> Terms.copy_fact2 f) hypl in
        let constra' = Terms.copy_constra2 g_constra_to_add1 in
        HCaseDistinction(concl',hypl',[],constra',hist)
      )
  in
  let new_hist2 = HNested(List.map (fun (_,i,_,_,_,_) -> i) matching_nested, nb_fact_in_orig_concl, Resolution(new_hist1,0,rule_nested)) in
  let new_clause = copy_auth_rule2 (new_hypl,new_concl,new_hist2,Terms.wedge_constraints constra g_constra_to_add1) in

  (new_query,new_clause)

(* val eval_gather : events -> Nested queries -> disequalities -> predicates  -> () -> .... *)
(* We assume that the matching has been done on the premise of the query *)

let rec eval_gather_event restwork = function
  | QEq((t1,_),(t2,_)) ->
      TermsEq.unify_modulo (fun () ->
        restwork [] [] Terms.true_constraints [] []
      ) t1 t2
  | QGeq((t1,_),(t2,_)) -> restwork [] [] (Terms.constraints_of_geq t1 t2) [] []
  | QIsNat t -> restwork [] [] (Terms.constraints_of_is_nat t) [] []
  | QNeq((t1,_),(t2,_)) -> restwork [] [] (Terms.constraints_of_neq t1 t2) [] []
  | QSEvent(inj_op,ord_fun,occ,_,ev) -> restwork [inj_op,ord_fun,occ,ev] [] Terms.true_constraints [] []
  | QSEvent2(ev1,ev2) -> restwork [] [] Terms.true_constraints [] [ev1,ev2]
  | QFact(p,ord_fun,args,_) -> restwork [] [] Terms.true_constraints [Pred(p,args),ord_fun] []
  | QGr _ -> Parsing_helper.internal_error "[piauth.ml >> eval_gather_event] Queries with strict inequalities should be encoded by now."

and eval_gather_conclusion restwork = function
  | QTrue -> restwork [] [] Terms.true_constraints [] []
  | QFalse -> raise Unify
  | QConstraints q -> restwork [] [] q [] []
  | QEvent(ev) -> eval_gather_event restwork ev
  | NestedQuery(Before([QSEvent(inj_op,ord_fun,occ,_,ev)],concl)) -> restwork [] [(inj_op,ord_fun,occ,ev),concl] Terms.true_constraints [] []
  | NestedQuery _ -> internal_error "[piauth.ml >> eval_gather_conclusion] Nested query should have exactly one event in their premise."
  | QAnd(concl1,concl2) ->
      eval_gather_conclusion (fun g_ev1 g_nested1 g_constra1 g_pred1 g_bi_ev1 ->
        eval_gather_conclusion (fun g_ev2 g_nested2 g_constra2 g_pred2 g_bi_ev2 ->
          restwork (g_ev1@g_ev2) (g_nested1@g_nested2) (Terms.wedge_constraints g_constra1 g_constra2) (g_pred1@g_pred2) (g_bi_ev1@g_bi_ev2)
        ) concl2
      ) concl1
  | QOr(concl1,concl2) ->
      try
        eval_gather_conclusion restwork concl1
      with Unify ->
        eval_gather_conclusion restwork concl2

let rec clause_match_realquery restwork strong_verif lemmas ind_lemmas initial_nb_premise (((hyp,concl,_,constra) as clause):auth_ordered_reduction) = function
  | Before(evl_premise,concl_q) ->
      let evl_premise_no_constra = 
        List.filter (function
          | QNeq _ | QGeq _ | QIsNat _ -> false
          | _ -> true
        ) evl_premise
      in

      (* Replace all variables in the clause with constants "SpecVar" *)
      assert (!current_bound_vars == []);
      put_constants_rule clause;
      let (hypl',concl',hist',constra') as clause' = copy_auth_rule2 clause in
      cleanup ();

      let constra_cl_for_implies = map_constraints TermsEq.remove_syntactic_term constra in
      let facts_for_implies =
        (TermsEq.remove_syntactic_fact concl) ::
        List.map (fun (f,_) -> TermsEq.remove_syntactic_fact f) hyp
      in

      (* To prove the events and blocking predicates of the query (hyp1_events), we
         show that they match the events and blocking predicates of the clause (hyp2_events).
         These predicates cannot be derived from clauses.
         To prove the non-blocking predicate of the query (hyp1_preds), we
         show that they are derivable from any predicates (blocking or not) of the clause
         (hyp2_preds, hyp2_preds_block).
         These predicates cannot be directly in the clause since they are not blocking.

         Index in the list starts at 0.*)
      let (hyp_events,hyp_preds,hyp_preds_block,hyp_events2,_) =
        List.fold_left (fun (evl,pl,pbl,ev2l,n) -> function
          | (Pred(p,args) as fact,(ord_fun,_))  when p == Param.event_pred_block || p == Param.inj_event_pred_block ->
              (n,(fact,ord_fun))::evl, pl, pbl, ev2l, n+1
          | (Pred(p,[ev1;ev2]),_) when p == Param.event2_pred_block ->
              evl,pl,pbl,(ev1,ev2)::ev2l,n+1
          | (Pred(p,args) as fact,(ord_fun,_)) when p.p_prop land Param.pred_BLOCKING != 0 ->
              evl,pl,(n,(fact,ord_fun))::pbl, ev2l, n+1
          | (pred,(ord_fun,_)) ->
              evl,(n,(pred,ord_fun))::pl,pbl,ev2l, n+1
        ) ([],[],[],[],0) hypl'
      in

      (* Adding the events and predicates of the conclusion *)
      let to_add_in_hypl, occ_concl = occurrence_and_hyp_of_conclusion_predicate initial_nb_premise evl_premise_no_constra concl' in

      let (to_add_in_hypl_events,to_add_in_hypl_preds,to_add_in_hypl_events2) =
        List.fold_left (fun (evl,pl,ev2l) -> function
          | (_,(Pred(p,_),_)) as nev when p == Param.event_pred_block || p == Param.inj_event_pred_block -> nev::evl, pl, ev2l
          | (_,(Pred(p,[ev1;ev2]),_)) when p == Param.event2_pred_block -> evl,pl,(ev1,ev2)::ev2l
          | pred -> evl,pred::pl,ev2l
        ) ([],[],[]) to_add_in_hypl
      in

      (* Retrieve the combined predicate for the premise *)

      let (_,premise,_,_) = event_list_to_rule evl_premise_no_constra in
      let injectivity_data = generate_injective_data evl_premise_no_constra in

      try
        (* Unification of the conclusion of the clause with the premise of the query. *)
        match_premise (fun () ->
          (* Gather the different elements of the query *)
          eval_gather_conclusion (fun g_ev g_nested g_constra g_pred g_ev2 ->
            (* Match the events of biprocess *)
            match_event2_list (fun () ->
              (* Match the events *)
              match_event_list (fun occ_l_ev ->
                (* [occ_l_ev] is the list of (k,(n,ev)) where k is the injective index, ev the matched event
                   (including its occurrence name), n its position in the clause, for injective events *)
                match_premise_nested_query (fun occ_l_nested matching_nested ->
                  (* [occ_l_nested] is the list of (k,(n,ev)) where k is the injective index, ev the matched event
                     (including its occurrence name), n its position in the clause, for injective events
                     [matching_nested] is the list of (n,ev,ord_fun_hyp,ord_fun_query,concl_nested)
                     ([n] is an in [occ_l_nested] above)
                  *)
                  let occ_l = List.rev_append occ_l_nested occ_l_ev in

                  (* Match the predicates *)
                  match_predicate_list (fun g_pred_unblock_to_check ->
                    if strong_verif && List.exists (fun (fact,_) -> match fact with
                      | Pred({ p_info = Attacker _ | AttackerBin _ | Table _ | TableBin _ },_) -> true
                      | _ -> false
                      ) g_pred_unblock_to_check
                    then raise Unify;

                    (* Close the gathered constraints modulo the equational theory, i.e. the inequalities and is_nat
                       predicates *)
                    TermsEq.close_constraints_eq_synt (fun g_constra2 ->
                      (* Split the disequalities that can be negated. When a disequality only contains
                         variables of the clause, it should be in fact ground at this stage since all
                         variables of the clause have been replaced by constants. *)
                      let filter_neq = List.exists (fun (t1,t2) -> Termslinks.has_vars t1 || Termslinks.has_vars t2) in
                      let filter_geq (t1,_,t2) = Termslinks.has_vars t1 || Termslinks.has_vars t2 in

                      let implies_constraints g_constra3 =
                        let g_constra4 = map_constraints (fun t -> specvar_to_var (TermsEq.remove_syntactic_term t)) g_constra3 in
                        try
                          TermsEq.implies_constraints_keepvars facts_for_implies constra_cl_for_implies g_constra4;
                          true
                        with NoMatch -> false
                      in

                      let (g_constra_to_check, g_constra_to_negate) =
                        let (neq_check,neq_negate) = List.partition filter_neq g_constra2.neq in
                        let neq_negate' = List.filter (fun neq -> not (implies_constraints { neq = [neq]; is_nat = []; is_not_nat = []; geq = []})) neq_negate in
                        let (is_nat_check,is_nat_negate) = List.partition Termslinks.has_vars g_constra2.is_nat in
                        let is_nat_negate' = List.filter (fun is_nat -> not (implies_constraints { neq = []; is_nat = [is_nat]; is_not_nat = []; geq = []})) is_nat_negate in
                        let (geq_check,geq_negate) = List.partition filter_geq g_constra2.geq in
                        let geq_negate' = List.filter (fun geq -> not (implies_constraints { neq = []; is_nat = []; is_not_nat = []; geq = [geq]})) geq_negate in
                        { neq = neq_check; is_nat = is_nat_check; is_not_nat = []; geq = geq_check },
                        { neq = neq_negate'; is_nat = is_nat_negate'; is_not_nat = []; geq = geq_negate' }
                      in

                      let positive_clause_op = generate_positive_clauses clause occ_concl occ_l g_constra_to_negate in

                      (* Check injectivity conditions: We need check injectivity on the clause with
                         the disequalities and predicates that can be negated. We apply this test before checking unblock predicates
                         and nested queries. It should be faster than to do it later on. Moreover, it is sound because the check
                         of nested queries and unblock predicates do not modify the clause nor does it add disequalities or blocking
                         predicates to negate. *)
                      check_injectivity (fun () ->
                        (* Match the non blocking predicate *)
                        match_unblock_predicates (fun g_constra_to_check' ->
                          begin
                            try
                              let implying_constra = wedge_constraints (map_constraints (fun t -> specvar_to_var (TermsEq.remove_syntactic_term t)) g_constra_to_negate) constra_cl_for_implies in

                              TermsEq.simplify_constraints (fun c ->
                                TermsEq.implies_constraints_keepvars facts_for_implies c g_constra_to_check'
                              ) (fun c ->
                                let facts'' = List.map copy_fact4 facts_for_implies in
                                TermsEq.implies_constraints_keepvars4 facts'' c g_constra_to_check'
                              ) facts_for_implies implying_constra
                            with NoMatch | TermsEq.FalseConstraint -> raise Unify
                          end;

                          let new_clauses_to_check = negate_predicate_constra lemmas ind_lemmas clause g_constra_to_negate in

                          (* Instantiate the nested queries with the value given by the clause *)
                          if matching_nested = []
                          then Terms.auto_cleanup (fun () -> restwork new_clauses_to_check)
                          else
                            let (nested_query,request_clause) = generate_nested_query_and_rule evl_premise g_ev g_constra_to_check g_constra_to_negate g_pred matching_nested clause in

                            if injectivity_data = None
                            then
                              if Terms.auto_cleanup (fun () -> True = check_query ~close_equation:false ~contain_nested:true None false lemmas [] initial_nb_premise (ordered_rule_of_auth_ordered request_clause) nested_query)
                              then Terms.auto_cleanup (fun () -> restwork new_clauses_to_check)
                              else raise Unify
                            else
                              if True != Terms.auto_cleanup (fun () -> check_inj_query ~close_equation:false ~contain_nested:true (fun () -> restwork new_clauses_to_check) (fun _ -> DontKnow) lemmas initial_nb_premise (ordered_rule_of_auth_ordered request_clause) nested_query)
                              then raise Unify
                        ) lemmas g_pred_unblock_to_check g_constra_to_check hyp_preds hyp_preds_block
                      ) lemmas injectivity_data positive_clause_op
                    ) g_constra
                  ) g_pred (hyp_preds_block@hyp_preds@to_add_in_hypl_preds)
                ) g_nested (hyp_events@to_add_in_hypl_events)
              ) g_ev (hyp_events@to_add_in_hypl_events)
            ) g_ev2 (hyp_events2@to_add_in_hypl_events2)
          ) concl_q;
        ) premise concl';
        true
      with Unify -> false

and check_non_inj_clauses display_attack_opt strong_verif query lemmas ind_lemmas initial_nb_premise clauses =
  let queue = ref clauses in
  let final_result = ref True in
  let rec verify_queue () = match !queue with
    | [] -> !final_result
    | cl::q ->
        if clause_match_realquery (fun clauses' -> queue := clauses' @ q) strong_verif lemmas ind_lemmas initial_nb_premise cl query
        then verify_queue ()
        else
                match display_attack_opt with
                | None -> DontKnow
                | Some display_attack ->
              let result_display = display_attack cl in
              if result_display = DontKnow
              then
                    begin
                      final_result := DontKnow;
                      queue := q;
                      if (!traces_to_reconstruct != 0) && (!Param.reconstruct_derivation) then
                    verify_queue ()
                  else
                    DontKnow
                    end
              else result_display
  in
  verify_queue ()

and check_query ?(close_equation=true) ?(contain_nested=false) display_attack_opt strong_verif lemmas ind_lemmas initial_nb_premise request_rule query =
  let solved_rules = Rules.solving_request_rule ~close_equation:close_equation ~apply_not:true lemmas ind_lemmas request_rule in
  let auth_rules = List.rev_map auth_ordered_rule_of_ordered_rule solved_rules in
  let auth_rules' =
    (* Remove clauses subsumed modulo equational theory, when the query is not nested.
       (When it is nested, we keep them to generate enough clauses in sub-queries.) *)
    if !Param.simpeq_final && TermsEq.hasEquations() && not contain_nested then
      remove_subsumed_mod_eq auth_rules
    else
      auth_rules
  in

  let result = check_non_inj_clauses display_attack_opt strong_verif query lemmas ind_lemmas initial_nb_premise auth_rules' in
  if result = True
  then success_clauses := auth_rules' @ (!success_clauses);

  result

and check_inj_clauses restwork query lemmas initial_nb_premise clauses =
  let query' = Terms.auto_cleanup (fun () -> copy_query query) in
  match clauses with
    | [] ->
        begin
          try
            restwork ();
            true
          with Unify -> false
        end
    | cl::cll ->
        (* For injective queries, it is important that the [additional_clauses]
           generated by [clause_match_realquery] are checked in the [restwork] part
           of [clause_match_realquery]. *)
        clause_match_realquery (fun additional_clauses ->
          Terms.auto_cleanup (fun () ->
            if not (check_inj_clauses restwork query lemmas initial_nb_premise (additional_clauses@cll))
            then raise Unify
          )
        ) false lemmas [] initial_nb_premise cl query'

and check_inj_query ?(close_equation=true) ?(contain_nested=false) restwork display_attack lemmas initial_nb_premise request_rule query =
  let solved_rules = Rules.solving_request_rule ~close_equation:close_equation ~apply_not:true lemmas [] request_rule in
  let auth_rules = List.rev_map auth_ordered_rule_of_ordered_rule solved_rules in
  let auth_rules' =
    (* Remove clauses subsumed modulo equational theory, when the query is not nested.
       (When it is nested, we keep them to generate enough clauses in sub-queries.) *)
    if !Param.simpeq_final && TermsEq.hasEquations() && not (contain_nested) then
      remove_subsumed_mod_eq auth_rules
    else
      auth_rules
  in

  if check_inj_clauses restwork query lemmas initial_nb_premise auth_rules'
  then
    begin
      success_clauses := auth_rules' @ (!success_clauses);
      True
    end
  else
    display_attack auth_rules'

(* Main verification functions *)

let verify_inj_query display_when_true nested list_started all_lemmas (Before(evl,_) as query) =
  assert (!current_bound_vars == []);
  let request_rule = generate_initial_request_rule query in

  let initial_nb_premise = number_of_facts_in_premise evl in

  let display_attack clauses =
    let tmp_faulty_clauses = !faulty_clauses_injective in
    faulty_clauses_injective := [];

    if tmp_faulty_clauses = []
    then
      begin
        (* The query is false due to the nested queries *)
        if is_non_nested_query query
        then Parsing_helper.internal_error "[piauth.ml >> verify_inj_query] Should not happen since we already proved that the query is true without injectivity.";

        let clauses =
          (* Remove clauses subsumed modulo equational theory, when not already done,
             i.e. the query is nested. *)
          if !Param.simpeq_final && TermsEq.hasEquations() && nested then
            remove_subsumed_mod_eq clauses
          else
            clauses
        in
        let rec explore_clauses all_true = function
          | [] ->
              if all_true
              then Parsing_helper.internal_error "[piauth.ml >> verify_inj_query] If all are true then it would imply that the query is false due to injectivity";
              DontKnow
          | cl::q_cl ->
              success_clauses := [];
              let sub_res = check_inj_clauses (fun () -> ()) query all_lemmas initial_nb_premise [cl] in
              success_clauses := [];
              if not sub_res
              then
                begin
                  if display_clause_trace all_lemmas true (Some (fun _ -> false)) (Some query) list_started (ordered_rule_of_auth_ordered cl)
                  then False
                  else if (!traces_to_reconstruct != 0) && (!Param.reconstruct_derivation)
                  then explore_clauses false q_cl
                  else DontKnow
                 end
              else explore_clauses all_true q_cl
        in
        explore_clauses true  clauses
      end
    else
      let first_try = ref true in
      let res_att =
        List.exists (fun cl ->
          if !first_try
          then first_try := false
          else Display.Text.print_line "Trying to find a trace falsifying the query on another derivation.";

          (* I do not use recheck of the clause. It is not clear how I can check that
             a "double" clause does not satisfy the query. *)
          display_clause_trace all_lemmas true (Some (fun _ -> false)) (Some query) list_started cl
        ) tmp_faulty_clauses
      in

      if res_att
      then False
      else
        if List.length clauses = 1
        then DontKnow
        else
          begin
            (* We try with other clauses *)
            success_clauses := [];
            List.iter (fun cl -> ignore (check_inj_clauses (fun () -> ()) query all_lemmas initial_nb_premise [cl])) clauses;
            success_clauses := [];
            let res_att =
              List.exists (fun cl ->
                Display.Text.print_line "Trying to find a trace falsifying the query on another derivation.";

                (* I do not use recheck of the clause. It is not clear how I can check that
                   a "double" clause does not satisfy the query. *)
                display_clause_trace all_lemmas true (Some (fun _ -> false)) (Some query) list_started cl
              ) !faulty_clauses_injective
            in
            faulty_clauses_injective := [];
            if res_att
            then False
            else DontKnow
          end
  in

  success_clauses := [];
  let res = check_inj_query ~contain_nested:nested (fun () -> ()) display_attack all_lemmas initial_nb_premise request_rule query in
  let clauses = !success_clauses in
  success_clauses := [];
  if display_when_true && res = True then
    begin
      let clauses =
        (* Remove clauses subsumed modulo equational theory, when not already done,
           i.e. the query is nested. *)
        if !Param.simpeq_final && TermsEq.hasEquations() && nested then
          remove_subsumed_mod_eq clauses
        else
          clauses
      in
      if !Param.verbose_goal_reachable
      then  List.iter (fun cl -> ignore (display_clause_trace all_lemmas false None None list_started (ordered_rule_of_auth_ordered cl))) clauses
      else
        begin
          Display.Text.print_line ("Number of goals reachable: "^(string_of_int (List.length clauses)))
        end
    end;
  res

let verify_non_inj_query strong_verif display_when_true nested list_started lemmas ind_lemmas (Before(evl,_) as query) =
  assert (!current_bound_vars == []);
  let request_rule =
    if ind_lemmas = [] && not nested && not (require_order query)
    then
      (* Since there is no inductive lemmas and nested queries, we don't need to
         order the rules. *)
      generate_initial_request_rule_no_order query
    else generate_initial_request_rule query
  in

  let initial_nb_premise = number_of_facts_in_premise evl in

  let display_attack cl =
    let recheck_fun cl =
      success_clauses := [];
      let res = check_non_inj_clauses None strong_verif query lemmas [] initial_nb_premise [auth_ordered_rule_of_rule cl] in
      success_clauses := [];
      res = True
    in
    if display_clause_trace lemmas true (Some recheck_fun) (Some query) list_started (ordered_rule_of_auth_ordered cl)
    then False
    else DontKnow
  in

  success_clauses := [];
  let res = check_query ~contain_nested:nested (Some display_attack) strong_verif lemmas ind_lemmas initial_nb_premise request_rule query in
  let clauses = !success_clauses in
  success_clauses := [];
  if display_when_true && res = True then
    begin
      let clauses =
        (* Remove clauses subsumed modulo equational theory, when not already done,
           i.e. the query is nested. *)
        if !Param.simpeq_final && TermsEq.hasEquations() && nested then
          remove_subsumed_mod_eq clauses
        else
          clauses
      in
      if !Param.verbose_goal_reachable
      then List.iter (fun cl -> ignore (display_clause_trace lemmas false None None list_started (ordered_rule_of_auth_ordered cl))) clauses
      else
        begin
          Display.Text.print_line ("Number of goals reachable: "^(string_of_int (List.length clauses)))
        end
    end;
  res

let verify_query display_query lemmas ind_lemmas qdisp (Before(el, _) as q) =
  Display.auto_cleanup_display (fun () ->
    Display.Text.print_string "Starting query ";
    Display.Text.display_corresp_secret_putbegin_query qdisp;
    Display.Text.newline();
    if (!Param.html_output) && display_query
    then
      begin
        Display.Html.print_string "<LI><span class=\"query\">Query ";
        Display.Html.display_corresp_secret_putbegin_query qdisp;
        Display.Html.print_string "</span><br>\n"
      end
        );
  traces_to_reconstruct := !Param.reconstruct_trace;
  shown_stop := false;
  assert (!current_bound_vars == []);

  let list_started = ref false in
  let result =
    let q' = copy_query q in
    cleanup();

    (* Check whether the query is non-nested && non_injective *)
    let is_simple = is_simple_query q' in

    if is_simple
    then verify_non_inj_query !strong_verification_att_table true false list_started lemmas ind_lemmas q'
    else
      begin
        (* We simplify the query *)
        let simple_q = simplify_query q' in
        let result_simple = verify_non_inj_query !strong_verification_att_table false false list_started lemmas ind_lemmas simple_q in
        supplemental_info := [simple_q, result_simple];
        (* If the simplified query cannot be proved, then q cannot be proved either.
           If we could reconstruct a trace against the simplified query, then q is false *)
        if result_simple <> True
        then result_simple
        else
          (* Otherwise we check the query q' itself *)
          let all_lemmas = lemmas@ind_lemmas in
          if is_non_injective_query q'
          then
            (* The query [q'] is not simple and it is non-injective, so it is nested *)
            verify_non_inj_query false true true list_started all_lemmas [] q'
          else
            if is_non_nested_query q'
            then verify_inj_query true false list_started all_lemmas q'
            else
              begin
                (* We look at the simplified non-nested but injective query first *)
                let non_nested_q = remove_nested q' in
                let result_non_nested = verify_inj_query false false list_started all_lemmas non_nested_q in
                match result_non_nested with
                  | True ->
                      supplemental_info := [non_nested_q, result_non_nested];
                      (* When the simplified non-nested query is true, look at the real query *)
                      verify_inj_query true true list_started all_lemmas q'
                  | DontKnow ->
                      supplemental_info := (non_nested_q, result_non_nested) :: !supplemental_info;
                      DontKnow
                  | False ->
                      supplemental_info := [non_nested_q, result_non_nested];
                      False
              end
      end
  in

  if (!Param.html_output) && (!list_started)
  then Display.Html.print_string "</UL>\n";

  result

(* Prove *)

let do_query ?(partial=false) display_query lemmas ind_lemmas result_solve_queries index
    (solve_status,((qorig,_) as qorig_e), ((qencoded,_) as qencoded_e)) =
  match qencoded with
  | PutBegin _ -> ()
  | RealQuery (Before(el, concl_q) as q, []) ->
      faulty_clauses_injective := [];
      let r =
        if !for_biprocess && Rules.bad_in_saturated_database ()
        then DontKnow
        else verify_query display_query lemmas ind_lemmas qorig q
      in
      Display.Text.display_result_and_supplemental ~partial qorig qencoded r (!supplemental_info);
      if !Param.html_output
      then Display.Html.display_result_and_supplemental ~partial qorig qencoded r (!supplemental_info);

      supplemental_info := [];

      let r_query =
        if qorig != qencoded
        then CorrespQEnc([qorig_e,qencoded_e],solve_status)
        else CorrespQuery([qorig_e],solve_status)
      in
      result_solve_queries := (r,r_query,index) :: !result_solve_queries
  | RealQuery _ | QSecret _ ->
      Parsing_helper.internal_error "Query secret and queries with public variables should have been encoded before Piauth.do_query"

(* Main function *)

let display_final_result list_results =
  Display.Text.display_final_result list_results;
  if !Param.html_output then
    Display.Html.display_final_result list_results

let solve_auth horn_state pi_state =
  let result_solve_queries = ref [] in
  let (queries, max_subset, induction) = match pi_state.pi_process_query with
    | SingleProcessSingleQuery(p_desc, CorrespQuery (ql,solve_status)) ->
        for_biprocess := p_desc.bi_pro;
        List.map (fun q -> (solve_status,q,q)) ql, solve_status.s_max_subset, solve_status.s_induction
    | SingleProcessSingleQuery(p_desc, CorrespQEnc (qql,solve_status)) ->
        for_biprocess := p_desc.bi_pro;
        List.map (fun (qorig, qencoded) -> (solve_status,qorig,qencoded)) qql, solve_status.s_max_subset, solve_status.s_induction
    | _ ->
       Parsing_helper.internal_error "Unexpected process-query in piauth.ml"
  in
  strong_verification_att_table := induction || pi_state.pi_originally_lemma;
  List.iter (fun (_,_, query) -> Lemma.verify_conditions_query query) queries;
  init_clauses :=
    begin match horn_state.h_clauses with
      | Given rl -> rl
      | ToGenerate(rl,_) -> rl
    end;
  clauses_for_preds := None;
  declared_axioms := pi_state.pi_original_axioms;
  Rules.corresp_initialize horn_state;

  if !for_biprocess
  then
    begin match Rules.bad_in_saturated_database_opt () with
      | None -> ()
      | Some cl ->
          Terms.auto_cleanup (fun () ->
            Display.auto_cleanup_display (fun () ->
              Display.Text.print_string "goal reachable: ";
              Display.Text.display_rule_abbrev cl;
              if !Param.html_output then
                begin
                  Display.Html.print_string "goal reachable: ";
                  Display.Html.display_rule_abbrev cl
                end;
              let deriv = History.build_history None cl in
              if !Param.reconstruct_trace != 0 && !Param.reconstruct_derivation then
              ignore(Reduction_bipro.do_reduction ~bad_reached_in_lemmas:true None pi_state.pi_original_axioms deriv)
            )
          )
    end;

  let (lemmas,inductive_lemmas) =
    List.fold_left (fun (acc_lem,acc_ind) lem ->
      if lem.l_verif_app = LANone
      then (acc_lem,acc_ind)
      else
        if lem.l_induction = None
        then (lem::acc_lem,acc_ind)
        else (acc_lem,lem::acc_ind)
    ) ([],[]) horn_state.h_lemmas
  in

  if max_subset && induction && inductive_lemmas <> [] && List.length queries > 1
  then
    begin
      if !Param.html_output then Display.Html.print_string "<UL>\n";
      Display.Text.print_line "Starting proving a group of queries by induction.";
      let i_queries = List.mapi (fun i q -> (i,q)) queries in
      let rec verify_queries ind_lemmas verified_queries to_verify =
        List.iter (fun (i,q) -> do_query ~partial:true true lemmas ind_lemmas result_solve_queries i q) to_verify;

        (* We look for queries that are false and that were proven by induction *)
        let verify_again = ref false in
        let new_ind_lemmas =
          List.filter (fun lem -> match lem.l_induction with
            | None -> internal_error "[piauth.ml >> solve_auth] Inductive lemmas should have a correspond index for a query"
            | Some i ->
                if List.exists (fun (r,_,j) -> i = j && r <> True) !result_solve_queries
                then (verify_again := true; false)
                else true
          ) ind_lemmas
        in
        if !verify_again
        then
          begin
            let new_to_verify = List.filter (fun (i,q) -> List.exists (fun (r,_,j) -> i = j && r <> False) !result_solve_queries) to_verify in
            let new_verified = List.filter (fun (r,_,_) -> r = False) !result_solve_queries in

            result_solve_queries := [];
            Display.Text.print_line "Some inductive lemmas could not be verified.";
            if new_to_verify <> []
            then Display.Text.print_line "Restarting verification of queries without these inductive lemmas.";
            verify_queries new_ind_lemmas (verified_queries@new_verified) new_to_verify
          end
        else verified_queries @ !result_solve_queries
      in

      let results = List.rev_map (fun (r,r_query,_) -> r,r_query) (verify_queries inductive_lemmas [] i_queries) in
      if !Param.html_output then Display.Html.print_string "</UL>\n";
      display_final_result results;
      results
    end
  else
    match queries with
      | [q] ->
          (* Since there is only one query, we do not need to display partial result. *)
          do_query false lemmas inductive_lemmas result_solve_queries 0 q;
          List.map (fun (r,r_query,_) -> r,r_query) !result_solve_queries
      | _ ->
          let partial = not max_subset && induction in

          if !Param.html_output then Display.Html.print_string "<UL>\n";
          List.iteri (do_query ~partial:partial true lemmas inductive_lemmas result_solve_queries) queries;
          if !Param.html_output then Display.Html.print_string "</UL>\n";

          let results = List.rev_map (fun (r,r_query,_) -> r,r_query) !result_solve_queries in
          let results' =
            if partial
            then
              begin
                let final_results =
                  if List.for_all (function True,_ -> true | _,_ -> false) results
                  then results
                  else List.map (function (True,q) -> (DontKnow,q) | r -> r) results
                in
                display_final_result final_results;
                final_results
              end
            else results
          in
          results'
