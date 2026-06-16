open Parsing_helper
open Types
open Pitypes

let for_equivalence = ref true

(* Information computed by [transl], to add to the [pi_state] *)

let terms_to_add_in_name_params = ref []
let min_choice_phase = ref max_int

(* Variables local to this module, used to store elements of the t_horn_state we are going to return *)

(** Indicate the number of rules created *)
let nrule = ref 0

(** List of the rules created *)
let red_rules = ref ([] : reduction list)

let no_unif_set = ref ([] : (fact_format * nounif_value * nounif_op) list)

let current_precise_actions = ref ([] : funsymb list)

let add_in_precise_actions ev =
  if List.memq ev !current_precise_actions
  then ()
  else current_precise_actions := ev :: !current_precise_actions

let add_no_unif f n for_hyp =
  no_unif_set := (f,n,for_hyp) ::(!no_unif_set)

(*********************************************
          Function For Rules
**********************************************)

let mergelr = function
    Pred(p,[t1;t2]) as x ->
      begin
	match p.p_info with
	  | AttackerBin(i,t) ->
	      if i >= (!min_choice_phase) then x else
	      let att1_i = Param.get_pred (Attacker(i,t)) in
	      Terms.unify t1 t2;
	      Pred(att1_i, [t1])
	  | TableBin(i) ->
	      if i >= (!min_choice_phase) then x else
	      let tbl1_i = Param.get_pred (Table(i)) in
	      Terms.unify t1 t2;
	      Pred(tbl1_i, [t1])
	  | InputPBin(i) ->
	      if i >= (!min_choice_phase) then x else
	      let input1_i = Param.get_pred (InputP(i)) in
	      Terms.unify t1 t2;
	      Pred(input1_i, [t1])
	  | OutputPBin(i) ->
	      if i >= (!min_choice_phase) then x else
	      let output1_i = Param.get_pred (OutputP(i)) in
	      Terms.unify t1 t2;
	      Pred(output1_i, [t1])
	  | _ -> x
      end
  | Pred(p,[t1;t2;t3;t4]) as x ->
      begin
	match p.p_info with
	  | MessBin(i,t) ->
	      if i >= (!min_choice_phase) then x else
	      let mess1_i = Param.get_pred (Mess(i,t)) in
	      Terms.unify t1 t3;
	      Terms.unify t2 t4;
	      Pred(mess1_i, [t1;t2])
	  | _ -> x
      end
  | x -> x

let nb_rule_total = ref 0

let add_and_record rule =
  Database.record_from_rule rule;
  red_rules := rule :: !red_rules

let add_and_follow f_next rule =
  f_next rule;
  incr nrule

let add_rule_follow f_next hyp concl constra tags =
  if !min_choice_phase > 0 then
    begin
      assert (!Terms.current_bound_vars == []);
      try
        let hyp' = List.map mergelr hyp in
        let concl' = mergelr concl in
        let hyp'' = List.map Terms.copy_fact2 hyp' in
        let concl'' = Terms.copy_fact2 concl' in
        let constra'' = Terms.copy_constra2 constra in
        let tags'' =
          match tags with
            ProcessRule(hsl, nl) -> ProcessRule(hsl, List.map Terms.copy_term2 nl)
          | x -> x
        in
        Terms.cleanup();

        begin
          try
            TermsEq.simplify_constraints (fun constra1 ->
              add_and_follow f_next (hyp'',concl'',Rule (!nrule, tags'', hyp'', concl'', constra1),constra1)
            ) (fun constra1 ->
              let hyp1 = List.map Terms.copy_fact4 hyp'' in
              let concl1 = Terms.copy_fact4 concl'' in
              let tags1 =
                match tags'' with
                  ProcessRule(hsl, nl) -> ProcessRule(hsl, List.map Terms.copy_term4 nl)
                | x -> x
              in
              add_and_follow f_next (hyp1,concl1,Rule (!nrule, tags1, hyp1, concl1, constra1),constra1)
            ) (concl''::hyp'') constra''
          with TermsEq.FalseConstraint -> ()
        end
      with Terms.Unify ->  Terms.cleanup ()
    end
  else
    try
      TermsEq.simplify_constraints (fun constra1 ->
        let constra1 = TermsEq.remove_caught_fail constra1 in
        add_and_follow f_next (hyp,concl,Rule (!nrule, tags, hyp, concl, constra1),constra1)
      ) (fun constra1 ->
        let hyp1 = List.map Terms.copy_fact4 hyp in
        let concl1 = Terms.copy_fact4 concl in
        let constra1 = TermsEq.remove_caught_fail constra1 in
        let tags1 =
          match tags with
            ProcessRule(hsl, nl) -> ProcessRule(hsl, List.map Terms.copy_term4 nl)
          | x -> x
        in
        add_and_follow f_next (hyp1,concl1,Rule (!nrule, tags1, hyp1, concl1, constra1),constra1)
      ) (concl::hyp) constra
    with TermsEq.FalseConstraint -> ()

let add_rule hyp concl constra tags =
  add_rule_follow add_and_record hyp concl constra tags

(*********************************************
           Preliminary functions
**********************************************)

type transl_state =
  { tr_pi_state : t_pi_state; (* [pi_state] received as input *)

    hypothesis : fact list; (* Current hypotheses of the rule *)
    constra : constraints; (* Current constraints of the rule *)

    name_params : name_param_info list; (* List of parameters of names *)
    name_params_types : typet list;
    repl_count : int; (* Counter for replication *)

    input_pred : predicate;
    output_pred : predicate;
    cur_phase : int; (* Current phase *)

    hyp_tags : hypspec list;
    record_fun_opt : (reduction -> unit) option
      (* When [None], we do not really generate clauses, we just initialize the
         information for the arguments of names created by restrictions
	 and record symbols for features used to index clauses for subsumption.
         When [Some record_fun], we generate the clauses and pass each
         generated clause to the function [record_fun]. *)
  }

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

let display_transl_state cur_state =
   Printf.printf "\n--- Display current state ---\n";
   Printf.printf "\nHypothesis:\n";
   Display.Text.display_list (Display.Text.WithLinks.fact) " ; " cur_state.hypothesis;
   Printf.printf "\nConstraint:\n";
   Display.Text.WithLinks.constraints cur_state.constra

(* Tools *)

let get_type_from_pattern = function
  | PatVar(v) -> v.btype
  | PatTuple(f,_) -> snd f.f_type
  | PatEqual(t) -> Terms.get_term_type t

(* Creation of fact of attacker', mess' and table. *)

let att_fact phase t1 t2 =
  Pred(Param.get_pred (AttackerBin(phase, Terms.get_term_type t1)), [t1; t2])

let mess_fact phase tc1 tm1 tc2 tm2 =
  Pred(Param.get_pred (MessBin(phase, Terms.get_term_type tm1)), [tc1;tm1;tc2;tm2])

let table_fact phase t1 t2 =
  Pred(Param.get_pred (TableBin(phase)), [t1;t2])

(* Outputing a rule *)

let output_rule cur_state out_fact = match cur_state.record_fun_opt with
  | None -> List.iter Database.record_from_fact (out_fact::cur_state.hypothesis)
  | Some f_rule ->
      Terms.auto_cleanup (fun _ ->
        (* Apply the unification *)
        let hyp = List.map Terms.copy_fact2 cur_state.hypothesis in
        let concl = Terms.copy_fact2 out_fact in
        let constra = Terms.copy_constra2 cur_state.constra in
        let name_params = List.map Terms.copy_term2 (Reduction_helper.extract_name_params_noneed cur_state.name_params) in
        Terms.cleanup();

        add_rule_follow f_rule hyp concl constra (ProcessRule(cur_state.hyp_tags, name_params))
      )

(* Decide when to optimize mess(c,M) into attacker(M) *)

let rec get_term_side get_left = function
  | Var({ link = TLink t; _}) ->  get_term_side get_left t
  | FunApp({ f_cat = Choice; _},[t1;t2]) -> if get_left then get_term_side get_left t1 else get_term_side get_left t2
  | t -> t

let optimize_mess cur_state tc =
  let rec is_public_term = function
    | FunApp({ f_cat = Name _; f_private = false },_) -> true
    | FunApp({ f_cat = Eq _; f_private = false; _ }, args)
    | FunApp({ f_cat = Tuple; _}, args) -> List.for_all is_public_term args
    | _ -> false
  in

  let is_same_public_term () =
    let tc1 = get_term_side true tc in
    if is_public_term tc1
    then
      let tc2 = get_term_side false tc in
      Terms.equal_terms tc1 tc2
    else false
  in
  !Param.active_attacker &&
  (is_same_public_term ()) &&
  ((not (!Param.allow_private_comm_on_public_terms)) ||
   (not (Reduction_helper.prove_att_phase cur_state.tr_pi_state cur_state.cur_phase)))

(*********************************************
               Translate Terms
**********************************************)

let rec retrieve_rw_rules_at_pos acc_c acc_e pos = function
  | (ToCheck(i,_),_) as s :: q when i = pos ->
      retrieve_rw_rules_at_pos (s::acc_c) acc_e pos q
  | (ToExecute i,rw) :: q when i = pos ->
      retrieve_rw_rules_at_pos acc_c (rw::acc_e) pos q
  | q -> acc_c, acc_e, q

let rec transl_rewrite_rules_one_side next_f cur_state do_left check_c transl_t to_transl pos rules =
  if List.for_all (function
    ToExecute i, _ when pos < i -> true
    | _ -> false
    ) rules
  then transl_rewrite_rules_one_side_execute next_f cur_state do_left check_c transl_t to_transl pos rules
  else
    match rules with
      | [] -> ()
      | (ToCheck(i,_),_)::_
      | (ToExecute i, _):: _ when pos > i -> Parsing_helper.internal_error "[pitranslweak.ml >> transl_rewrite_rules] Should have been handled before";
      | (ToCheck(i,_),_)::_
      | (ToExecute i,_)::_ when pos < i ->
          (* All rules require to translate the next argument *)
          let t = List.hd to_transl in
          transl_term_one_side (fun cur_state1 t1 ->
            transl_rewrite_rules_one_side next_f cur_state1 do_left check_c (transl_t@[t1]) (List.tl to_transl) (pos+1) rules
          ) cur_state do_left t
      | _ ->
          let check, execute, others = retrieve_rw_rules_at_pos [] [] pos rules in
          let others1 = ref others in

          (* Check and execute when needed *)
          List.iter (function
            | ToCheck(i,j),(l,r,c) when i = j ->
                Terms.auto_cleanup (fun () ->
                  try
                    List.iter2 Terms.unify transl_t (Reduction_helper.get_until_pos pos l);
                    let cur_state' =
                      if check_c
                      then { cur_state with constra = TermsEq.simple_simplify_constraints (Terms.wedge_constraints c cur_state.constra) }
                      else cur_state
                        (* check is false only for tuples and constructor that does not have any equational theory.
                           Hence the side conditions c_left and c_right are true. Moreover, we don't check
                           that the unification satisfies the previous constraint since they rarely do in these case. *)
                    in
                    next_f cur_state' r
                  with Terms.Unify | TermsEq.FalseConstraint -> ()
                )
            | ToCheck(i,j),((l,r,c) as rw)->
                Terms.auto_cleanup (fun () ->
                  try
                    List.iter2 Terms.unify transl_t (Reduction_helper.get_until_pos pos l);
                    if check_c
                    then TermsEq.check_constraints (Terms.wedge_constraints c cur_state.constra);
                    others1 := Terms.add_in_sorted_status (ToExecute j,rw) !others1
                  with Terms.Unify | TermsEq.FalseConstraint -> ()
                )
            | _ -> Parsing_helper.internal_error "[pitranslweak.ml >> transl_rewrite_rules_one_side] should only contain ToCheck"
          ) check;

          (* Execute *)
          List.iter (fun (l,r,c) ->
            Terms.auto_cleanup (fun () ->
              try
                List.iter2 Terms.unify transl_t (Reduction_helper.get_until_pos pos l);
                let cur_state1 = { cur_state with constra = Terms.wedge_constraints c cur_state.constra } in
                (* We don't check the constraints since the check of constraints
                   was done when handling ToCheck(i,j). We could still check the constraints
                   too but i think it is superfleous. *)
                next_f cur_state1 r
              with Terms.Unify | TermsEq.FalseConstraint -> ()
            )
          ) execute;

          (* Translate the next position *)
          transl_rewrite_rules_one_side next_f cur_state do_left check_c transl_t to_transl pos !others1

and transl_rewrite_rules_one_side_execute next_f cur_state do_left check_c transl_t to_transl pos rules = match rules with
  | [] -> ()
  | (ToExecute i,_)::q ->
      let check, execute, other = retrieve_rw_rules_at_pos [] [] i rules in
      if check <> []
      then Parsing_helper.internal_error "[pitranslweak.ml >> transl_rewrite_rules_one_side_execute] The list should not contain ToCheck.";

      let t_to_translate = List.nth to_transl (i-pos-1) in
      transl_term_one_side (fun cur_state1 t1 ->
        List.iter (fun (left_list,right,side_c) ->
          let left_list_to_check = Reduction_helper.get_until_pos pos left_list in
          Terms.auto_cleanup (fun () ->
            try
              List.iter2 Terms.unify (t1::transl_t) (right::left_list_to_check);
              let cur_state2 = { cur_state with constra = Terms.wedge_constraints side_c cur_state1.constra } in
              (* We don't check the constraints since the check of constraints
                 was done when handling ToCheck(i,j). We could still check the constraints
                 too but i think it is superfleous. *)
              next_f cur_state2 t1
            with Terms.Unify | TermsEq.FalseConstraint -> ()
          )
        ) execute
      ) cur_state do_left t_to_translate;

      transl_rewrite_rules_one_side_execute next_f cur_state do_left check_c transl_t to_transl pos other
  | _ -> Parsing_helper.internal_error "[pitranslweak.ml >> transl_rewrite_rules_one_side_execute] Unexpected case."

and transl_term_one_side next_f cur_state do_left = function
  | Var v ->
      begin
        match  v.link with
          | TLink (FunApp(_,[t1;t2])) ->
              next_f cur_state (if do_left then t1 else t2)
          | _ -> internal_error "unexpected link in translate_term (1)"
      end
  | FunApp(f,args) ->
      let transl_red check =
        if args = []
        then
          (* In such a case, all rules are of the form f -> a *)
          let red_rules = Terms.red_rules_fun f in
          List.iter (fun (_,t,_) -> next_f cur_state t) red_rules
        else transl_rewrite_rules_one_side next_f cur_state do_left check [] args 0 (Terms.get_all_rewrite_rules_status f)
      in
      match f.f_cat with
        Name n ->
          begin
            match n.prev_inputs with
              Some t -> next_f cur_state t
            | _ -> internal_error "unexpected prev_inputs in transl_term_one_side"
          end
      | Tuple | Eq [] | Failure -> transl_red false
      | Red _ | Eq _ -> transl_red true
      | Choice ->
          begin
            match args with
              | [t1;t2] ->
                  transl_term_one_side next_f cur_state do_left
		    (if do_left then t1 else t2)
              | _ -> Parsing_helper.internal_error "Choice should have two arguments"
          end
      | ChoiceFst ->
          begin
            match args with
              | [t] ->
                  transl_term_one_side next_f cur_state true t
              | _ -> Parsing_helper.internal_error "Choice-fst should have one argument"
          end
      | ChoiceSnd ->
          begin
            match args with
              | [t] ->
                  transl_term_one_side next_f cur_state false t
              | _ -> Parsing_helper.internal_error "Choice-snd should have one argument"
          end
      | _ -> Parsing_helper.internal_error "function symbols of these categories should not appear in input terms (pitranslweak)"


(* [transl_term : (transl_state -> Types.terms -> Types.terms -> unit) -> transl_state -> Types.term -> unit
[transl_term f cur t] represent the translation of [t] in the current state [cur]. The two patterns that [f]
accepts as argument reprensent the result of the evalution
on open term on the left part and right part of [t].

Invariant : All variables should be linked with two closed terms when applied on the translation (due to closed processes)
*)
let transl_term next_f cur_state term =
  if cur_state.record_fun_opt = None
  then next_f cur_state term term
  else
    if cur_state.cur_phase < !min_choice_phase
    then
      transl_term_one_side (fun cur_state1 t ->
        next_f cur_state1 t t
        ) cur_state true term
    else
      transl_term_one_side (fun cur_state1 t_left ->
        transl_term_one_side (fun cur_state2 t_right ->
          next_f cur_state2 t_left t_right
        ) cur_state1 false term
      ) cur_state true term

(* next_f takes a state and two lists of patterns as parameter *)
let rec transl_term_list next_f cur_state = function
    [] -> next_f cur_state [] []
  | (a::l) ->
      transl_term (fun cur_state1 p1 p2 ->
        transl_term_list (fun cur_state2 patlist1 patlist2 ->
          next_f cur_state2 (p1::patlist1) (p2::patlist2)) cur_state1 l) cur_state a

let get_var_link cur_state v =
  match v.link with
  | TLink t ->
      if cur_state.cur_phase < !min_choice_phase then
	match t with
	| FunApp({ f_cat = Choice }, [t1;t2]) -> t1
	| _ -> internal_error "variable should be linked to choice"
      else
	t
  | _ -> internal_error "unexpected link in translate_term (4)"

let make_name_param_entry cur_state t1 t2 =
  let t =
    if cur_state.cur_phase < !min_choice_phase then
      t1
    else
      let type_t = Terms.get_term_type t1 in
      FunApp(Param.choice_fun type_t,[t1;t2])
  in
  (MUnknown, t, Always)

let transl_term_incl_destructor next_f cur_state occ term =
  let may_have_several_patterns = Reduction_helper.transl_check_several_patterns terms_to_add_in_name_params occ term in
  transl_term (fun cur_state1 term1 term2 ->
    if may_have_several_patterns
    then
      next_f { cur_state1 with
          name_params = (make_name_param_entry cur_state1 term1 term2)::cur_state1.name_params;
          name_params_types = (Terms.get_term_type term1) (* this type may not be accurate when types are ignored
					(a type conversion function may have been removed); we
					don't use it since it is not associated to a variable *)
                                     :: cur_state1.name_params_types
        } term1 term2
    else
      next_f cur_state1 term1 term2
  ) cur_state term

let transl_term_list_incl_destructor next_f cur_state occ tl =
  let may_have_several_patterns = List.exists (Reduction_helper.transl_check_several_patterns terms_to_add_in_name_params occ) tl in
  transl_term_list (fun cur_state1 tl_left tl_right ->
    if may_have_several_patterns
    then
      next_f { cur_state1 with
          name_params = (List.map2 (make_name_param_entry cur_state1) tl_left tl_right) @ cur_state1.name_params;
          name_params_types = (List.map Terms.get_term_type tl_left) @ cur_state1.name_params_types
        } tl_left tl_right
    else next_f cur_state1 tl_left tl_right
  ) cur_state tl

(*********************************************
              Translate Facts
**********************************************)

let transl_fact next_f cur_state occ = function
  | Pred(p,args) ->
      transl_term_list_incl_destructor (fun cur_state1 args_left args_right ->
        next_f cur_state1 (Pred(p,args_left)) (Pred(p,args_right))
      ) cur_state occ args

(*********************************************
              Translate Patterns
**********************************************)

let rec transl_pat next_f cur_state under_choice pattern =
  match pattern with
  | PatVar b ->
      let x_pair =
	if cur_state.cur_phase < !min_choice_phase || under_choice then
	  let x = Var (Terms.copy_var b) in
	  [x;x]
	else
	  [Var (Terms.copy_var b); Var (Terms.copy_var b)]
      in
      b.link <- TLink (FunApp(Param.choice_fun b.btype, x_pair));
      next_f cur_state (Var b) [b];
      b.link <- NoLink
  | PatTuple(fsymb,pat_list) when fsymb.f_cat = Choice ->
      (* Nested choice patterns are forbidden *)
      assert (under_choice = false);
      if cur_state.cur_phase < !min_choice_phase then
	Parsing_helper.user_error ("diff or choice pattern in phase "^(string_of_int cur_state.cur_phase)^
				   if !min_choice_phase = max_int && cur_state.tr_pi_state.pi_max_used_phase < max_int
				   then " but there are no diff/choice terms"
				   else " but diff/choice terms occur only in phase at least "^(string_of_int (!min_choice_phase)));
      transl_pat_list (fun cur_state2 term_list binder_list ->
        next_f cur_state2 (FunApp(fsymb,term_list)) binder_list
      ) cur_state true pat_list
  | PatTuple(fsymb,pat_list) ->
      transl_pat_list (fun cur_state2 term_list binder_list ->
        next_f cur_state2 (FunApp(fsymb,term_list)) binder_list
      ) cur_state under_choice pat_list
  | PatEqual t -> next_f cur_state t []

and transl_pat_list next_f cur_state under_choice = function
  | [] -> next_f cur_state [] []
  | pat::q ->
      transl_pat (fun cur_state2 term binders2 ->
        transl_pat_list (fun cur_state3 term_list binders3  ->
          next_f cur_state3 (term::term_list) (binders2@binders3)
        ) cur_state2 under_choice q
      ) cur_state under_choice pat

let transl_pat next_f cur_state pattern =
  transl_pat next_f cur_state false pattern

(*********************************************
        Equation of success or failure
**********************************************)

exception Failure_Unify

(* Unify term t with a message variable.
   Raises Unify in case t is fail. *)

let unify_var t =
  let x = Terms.new_var_def_term (Terms.get_term_type t) in
  Terms.unify t x

(* Unify term t with fail *)

let unify_fail t =
  let fail = Terms.get_fail_term (Terms.get_term_type t) in
  Terms.unify fail t

let unify_list f_next cur_state l1 l2 =
  if cur_state.record_fun_opt = None
  then f_next ()
  else
    Terms.auto_cleanup (fun () ->
      try
        List.iter2 Terms.unify l1 l2;
        f_next ()
      with Terms.Unify -> ()
    )

let transl_both_side_succeed nextf cur_state list_left list_right  =
  if cur_state.record_fun_opt = None
  then nextf cur_state
  else
    Terms.auto_cleanup (fun _ ->
      try
        List.iter unify_var list_left;
        List.iter unify_var list_right;
        nextf cur_state
      with Terms.Unify -> ()
    )

let transl_both_side_fail nextf cur_state list_left list_right  =
  if cur_state.record_fun_opt = None
  then nextf cur_state
  else
    List.iter (fun t_left ->
      List.iter (fun t_right ->
        Terms.auto_cleanup (fun _ ->
          try
            unify_fail t_left;
            unify_fail t_right;
            nextf cur_state
          with Terms.Unify -> ()
              )
        ) list_right;
    ) list_left

let transl_one_side_fails nextf cur_state list_failure list_success  =
  if cur_state.record_fun_opt = None
  then nextf cur_state
  else
    List.iter (fun t ->
      Terms.auto_cleanup (fun _ ->
        try
          List.iter unify_var list_success;
          unify_fail t;
          nextf cur_state
        with Terms.Unify -> ()
  	  )
    ) list_failure

(**********************************************************
        Generation of pattern with universal variables
***********************************************************)

let generate_pattern_with_uni_var binders_list term_pat_left term_pat_right =
  let var_pat_l,var_pat_r =
    List.split (
      List.map (fun b ->
        match b.link with
          | TLink(FunApp(_,[Var(x1);Var(x2)])) -> (x1,x2)
          | _ -> internal_error "unexpected link in translate_term (2)"
      ) binders_list
    ) in

  (* TO DO this code may cause internal errors in the presence of patterns
     let (b, =g(b)) = .... when b gets unified with a term that is not a variable.
     However, such patterns are forbidden, so this is not a problem. *)

  let new_var_pat_l = List.map (fun v ->
    match Terms.follow_link (fun b -> Var b) (Var v) with
      |Var v' -> v'
      |_ -> internal_error "unexpected term in translate_process (3)") var_pat_l

  and new_var_pat_r = List.map (fun v ->
    match Terms.follow_link (fun b -> Var b) (Var v) with
      |Var v' -> v'
      |_ -> internal_error "unexpected term in translate_process (4)") var_pat_r in

  let new_term_pat_left = Terms.follow_link (fun b -> Var b) term_pat_left
  and new_term_pat_right = Terms.follow_link (fun b -> Var b) term_pat_right in

  let gen_pat_l = Terms.auto_cleanup (fun _ -> Terms.generalize_vars_in new_var_pat_l new_term_pat_left)
  and gen_pat_r = Terms.auto_cleanup (fun _ -> Terms.generalize_vars_in new_var_pat_r new_term_pat_right) in

  gen_pat_l,gen_pat_r

(*********************************************
              Translate Process
**********************************************)

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
  verify_explored_occurrence cur_state process (fun () ->
    (* DEBUG mode *)

    (*Printf.printf "\n\n**********************\n\n";
    Display.Text.display_process_occ "" process;
    display_transl_state cur_state;
    flush_all ();*)

    match process with
    | Nil -> ()
    | Par(proc1,proc2) ->
        transl_process cur_state proc1;
        transl_process cur_state proc2
    | Repl(proc,occ) ->
        (* Always introduce session identifiers ! *)
        let var = Terms.new_var ~orig:false "@sid" Param.sid_type in
        let sid_meaning = MSid (cur_state.repl_count + 1) in
        let cur_state' =
          {
            cur_state with
            repl_count = cur_state.repl_count + 1;
            name_params = (sid_meaning, Var var, Always)::cur_state.name_params;
            name_params_types = Param.sid_type ::cur_state.name_params_types;
            hyp_tags = (ReplTag(occ, Reduction_helper.count_name_params cur_state.name_params)) :: cur_state.hyp_tags
          } in
        transl_process cur_state' proc
    | Restr(name,(args,env),proc,occ) ->
        begin
          match name.f_cat with
            | Name r ->
                let need_list = Reduction_helper.get_need_vars cur_state.tr_pi_state name in
                let include_info = Reduction_helper.prepare_include_info env args need_list in
                let npm = Reduction_helper.extract_name_params_meaning name include_info cur_state.name_params in
                let np = Reduction_helper.extract_name_params name include_info cur_state.name_params in
                let name_prev_type = Reduction_helper.extract_name_params_types name include_info cur_state.name_params cur_state.name_params_types in
                if Terms.eq_lists (fst name.f_type) Param.tmp_type
                then
                  begin
	            (* The arguments of names should all be set in the first dummy translation *)
		    assert (cur_state.record_fun_opt = None);
                    name.f_type <- name_prev_type, snd name.f_type;
                    r.prev_inputs_meaning <- npm
                  end
                else if Param.get_ignore_types() then
                  begin
                    (* When we ignore types, the types of the arguments may vary,
                       only the number of arguments is preserved. *)
                    if List.length (fst name.f_type) != List.length name_prev_type then
                      internal_error ("Name " ^ (Display.string_of_fsymb name) ^ " has bad arity")
                  end
                else
                  begin
                    if not (Terms.eq_lists (fst name.f_type) name_prev_type) then
                      internal_error ("Name " ^ (Display.string_of_fsymb name) ^ " has bad type")
                  end;
                if List.length r.prev_inputs_meaning <> List.length np
                then internal_error "prev_inputs_meaning and np should have the same size";

                r.prev_inputs <- Some (FunApp(name, np));
                transl_process cur_state proc;
                r.prev_inputs <- None

            | _ -> internal_error "A restriction should have a name as parameter"
        end
    | Test(term1,proc_then,proc_else,occ) ->
        (* This case is equivalent to :
           Let z = equals(condition,True) in proc_then else proc_else *)

        if proc_else == Nil then
          (* We optimize the case q == Nil.
             In this case, the adversary cannot distinguish the situation
             in which t fails from the situation in which t is false. *)
          transl_term_incl_destructor (fun cur_state1 term1_left term1_right ->
              (* Branch THEN (both sides are true) *)
              unify_list (fun () ->
                transl_process { cur_state1 with hyp_tags = (TestTag occ)::cur_state1.hyp_tags } proc_then
              ) cur_state1 [term1_left;term1_right] [Terms.true_term;Terms.true_term];

              if !for_equivalence
              then
                begin
                  (* BAD (Left is true / Right is false) *)
                  unify_list (fun () ->
                    output_rule { cur_state1 with
                                  constra = { cur_state1.constra with neq = [term1_right,Terms.true_term]::cur_state1.constra.neq };
                                  hyp_tags = (TestUnifTag2 occ)::cur_state1.hyp_tags
                                } (Pred(Param.bad_pred, []))
                  ) cur_state1 [term1_left;term1_right] [Terms.true_term;Terms.new_var_def_term (Terms.get_term_type term1_right)];

                  (* BAD (Left is true / Right fails) *)
                  unify_list (fun () ->
                    output_rule { cur_state1 with
                                  hyp_tags = (TestUnifTag2 occ)::cur_state1.hyp_tags
                                } (Pred(Param.bad_pred, []));
                  ) cur_state1 [term1_left;term1_right] [Terms.true_term;Terms.get_fail_term (Terms.get_term_type term1_right)];

                  (* BAD (Left is false / Right is true) *)
                  unify_list (fun () ->
                    output_rule { cur_state1 with
                                  constra = { cur_state1.constra with neq = [term1_left,Terms.true_term]::cur_state1.constra.neq };
                                  hyp_tags = (TestUnifTag2 occ)::cur_state1.hyp_tags
                                } (Pred(Param.bad_pred, []))
                  ) cur_state1 [term1_left;term1_right] [Terms.new_var_def_term (Terms.get_term_type term1_right);Terms.true_term];

                  (* BAD (Left fails / Right is true) *)
                  unify_list (fun () ->
                    output_rule { cur_state1 with
                                  hyp_tags = (TestUnifTag2 occ)::cur_state1.hyp_tags
                                } (Pred(Param.bad_pred, []))
                  ) cur_state1 [term1_left;term1_right] [Terms.get_fail_term (Terms.get_term_type term1_right);Terms.true_term]
                end
          ) cur_state (OTest(occ)) term1
        else
          transl_term_incl_destructor (fun cur_state1 term1_left term1_right ->
            (* Case both sides succeed *)
            transl_both_side_succeed (fun cur_state2 ->
              (* Branch THEN *)
              unify_list (fun () ->
                transl_process { cur_state2 with
                                 hyp_tags = (TestTag occ)::cur_state2.hyp_tags
                               } proc_then
              ) cur_state2 [term1_left;term1_right] [Terms.true_term;Terms.true_term];

              (* Branch ELSE *)
              transl_process { cur_state2 with
                constra = { cur_state2.constra with neq = [term1_left,Terms.true_term]::[term1_right,Terms.true_term]::cur_state2.constra.neq };
                hyp_tags = (TestTag occ)::cur_state2.hyp_tags
              } proc_else;

              if !for_equivalence
              then
                begin
                  (* BAD (Left ok / Right ko) *)
                  unify_list (fun () ->
                    output_rule { cur_state2 with
                                  constra = { cur_state2.constra with neq = [term1_right,Terms.true_term]::cur_state2.constra.neq };
                                  hyp_tags = (TestUnifTag2 occ)::cur_state2.hyp_tags
                                } (Pred(Param.bad_pred, []))
                  ) cur_state2 [term1_left] [Terms.true_term];

                  (* BAD (Left ko / Right ok) *)
                  unify_list (fun () ->
                    output_rule { cur_state2 with
                                  constra = { cur_state2.constra with neq = [term1_left,Terms.true_term]::cur_state2.constra.neq };
                                  hyp_tags = (TestUnifTag2 occ)::cur_state2.hyp_tags
                                } (Pred(Param.bad_pred, []))
                  ) cur_state2 [term1_right] [Terms.true_term]
                end
            ) cur_state1 [term1_left] [term1_right];

            if !for_equivalence
            then
              begin
                (* Case left side succeed and right side fail *)
                transl_one_side_fails (fun cur_state2 ->
                  (* BAD *)
                  output_rule { cur_state2 with
                    hyp_tags = TestUnifTag2(occ)::cur_state2.hyp_tags
                  } (Pred(Param.bad_pred, []));
                ) cur_state1 [term1_right] [term1_left];

                (* Case right side succeed and left side fail *)
                transl_one_side_fails (fun cur_state2 ->
                  (* BAD *)
                  output_rule { cur_state2 with
                    hyp_tags = TestUnifTag2(occ)::cur_state2.hyp_tags
                  } (Pred(Param.bad_pred, []));
                ) cur_state1 [term1_left] [term1_right]
              end
          ) cur_state (OTest(occ)) term1
    | Let(pat,term,proc_then,proc_else, occ) ->

        transl_term_incl_destructor (fun cur_state1 term_left term_right ->
          transl_pat (fun cur_state2 term_pattern binders_list ->
            transl_term (fun cur_state3 term_pat_left term_pat_right ->
              (* Generate the pattern with universal_variable *)
              let gen_pat_l, gen_pat_r = generate_pattern_with_uni_var binders_list term_pat_left term_pat_right in

              (* Case both sides succeed *)
              transl_both_side_succeed (fun cur_state4 ->
                (* Branch THEN *)
                unify_list (fun () ->
                  transl_process { cur_state4 with
                    name_params = (List.rev_map
                        (fun b -> (MVar(b, None), get_var_link cur_state4 b, IfQueryNeedsIt)
                            ) binders_list) @ cur_state4.name_params;
                    name_params_types = (List.rev_map (fun b -> b.btype) binders_list)@cur_state4.name_params_types;
                    hyp_tags = (LetTag occ)::cur_state4.hyp_tags
                  } proc_then
                ) cur_state4 [term_left;term_right] [term_pat_left;term_pat_right];

                (* Branch ELSE *)
                transl_process { cur_state4 with
                  constra = { cur_state4.constra with neq = [gen_pat_l,term_left]::[gen_pat_r,term_right]::cur_state4.constra.neq };
                  hyp_tags = (LetTag occ)::cur_state4.hyp_tags
                } proc_else;

                if !for_equivalence
                then
                  begin
                    (* BAD (Left ok / Right ko) *)
                    unify_list (fun () ->
                      output_rule { cur_state4 with
                        constra = { cur_state4.constra with neq = [gen_pat_r,term_right]::cur_state4.constra.neq };
                        hyp_tags = TestUnifTag2(occ)::cur_state4.hyp_tags
                      } (Pred(Param.bad_pred, []))
                    ) cur_state4 [term_left] [term_pat_left];

                    (* BAD (Left ko / Right ok) *)
                    unify_list (fun () ->
                      output_rule { cur_state4 with
                        constra = { cur_state4.constra with neq = [gen_pat_l,term_left]::cur_state4.constra.neq };
                        hyp_tags = TestUnifTag2(occ)::cur_state4.hyp_tags
                      } (Pred(Param.bad_pred, []))
                    ) cur_state4 [term_right] [term_pat_right]
                  end
              ) cur_state3 [term_pat_left;term_left] [term_pat_right;term_right];

              (* Case both sides fail *)
              transl_both_side_fail (fun cur_state4 ->
                transl_process { cur_state4 with
                  hyp_tags = (LetTag occ)::cur_state4.hyp_tags
                } proc_else
              ) cur_state3 [term_pat_left;term_left] [term_pat_right;term_right];

              (* Case left side succeed and right side fail *)
              transl_one_side_fails (fun cur_state4 ->
                (* Branch ELSE *)
                transl_process { cur_state4 with
                  constra = { cur_state4.constra with neq = [gen_pat_l,term_left]::cur_state4.constra.neq };
                  hyp_tags = (LetTag occ)::cur_state4.hyp_tags
                } proc_else;

                if !for_equivalence
                then
                  (* BAD (Left ok) *)
                  unify_list (fun () ->
                    output_rule { cur_state4 with
                      hyp_tags = TestUnifTag2(occ)::cur_state4.hyp_tags
                    } (Pred(Param.bad_pred, []))
                  ) cur_state4 [term_left] [term_pat_left]
              ) cur_state3 [term_pat_right;term_right] [term_pat_left;term_left];

              (* Case right side succeed and left side fail *)
              transl_one_side_fails (fun cur_state4 ->
                (* Branch ELSE *)
                transl_process { cur_state4 with
                  constra = { cur_state4.constra with neq = [gen_pat_r,term_right]::cur_state4.constra.neq };
                  hyp_tags = (LetTag occ)::cur_state4.hyp_tags
                } proc_else;

                if !for_equivalence
                then
                  (* BAD (Left ko) *)
                  unify_list (fun () ->
                    output_rule { cur_state4 with
                      hyp_tags = TestUnifTag2(occ)::cur_state4.hyp_tags
                    } (Pred(Param.bad_pred, []))
                  ) cur_state4 [term_right] [term_pat_right]
              ) cur_state3 [term_pat_left;term_left] [term_pat_right;term_right]
            ) cur_state2 term_pattern
          ) cur_state1 pat
        ) cur_state (OLet(occ)) term
    | LetFilter(_,_,_,_,_) -> user_error "Predicates are currently incompatible with proofs of equivalences."
    | Input(tc,pat,proc,occ) ->
        if optimize_mess cur_state tc then
          begin
            transl_pat (fun cur_state1 term_pattern binders ->
              transl_term (fun cur_state2 term_pat_left term_pat_right ->
                (* Generate the basic pattern variables *)
                let x_right = Terms.new_var_def_term (Terms.get_term_type term_pat_right)
                and x_left = Terms.new_var_def_term (Terms.get_term_type term_pat_left) in

                (* Generate the pattern with universal_variable *)
                let gen_pat_l, gen_pat_r = generate_pattern_with_uni_var binders term_pat_left term_pat_right in

		let precise_ev_name =
		  if occ.precise || Param.get_precise()
		  then
		    begin
                      let occ_name = get_occurrence_name_for_precise cur_state2 occ in
                      let precise_info = Action (Terms.get_term_type term_pat_left) in
                      let ev = Param.get_precise_event precise_info in
                      Reduction_helper.add_precise_info_occ occ precise_info;
                      add_in_precise_actions ev;
 		      Some (ev, occ_name)
		    end
		  else
		    None
		in

		let build_hyp term_pat_left term_pat_right cur_state =
                  let fact1 = att_fact cur_state.cur_phase term_pat_left term_pat_right in
                  let tag1 = InputTag occ in
		  match precise_ev_name with
		  | Some(ev, occ_name) ->
                      (fact1::Pred(Param.event2_pred_block,[FunApp(ev,[occ_name;term_pat_left]);FunApp(ev,[occ_name;term_pat_right])])::cur_state.hypothesis,
                       tag1  :: PreciseTag(occ) ::cur_state.hyp_tags
                          )
		  | None ->
                      (fact1::cur_state.hypothesis, tag1::cur_state.hyp_tags)
                in

                  (* Case both sides succeed *)
                  transl_both_side_succeed (fun cur_state3 ->

                    let (hypothesis,hyp_tags) = build_hyp term_pat_left term_pat_right cur_state3 in
                    (* Pattern satisfied in both sides *)
                    transl_process { cur_state3 with
                      name_params = (List.rev_map
                        (fun b -> (MVar(b,None), get_var_link cur_state3 b, Always)
                            ) binders) @ cur_state3.name_params;
                      name_params_types = (List.rev_map (fun b -> b.btype) binders)@cur_state3.name_params_types;
                      hypothesis = hypothesis;
                      hyp_tags = hyp_tags
                    } proc;

                    if !for_equivalence
                    then
                      begin
                        (* Pattern satisfied only on left side *)
			let (hypothesis_l,hyp_tags_l) = build_hyp term_pat_left x_right cur_state3 in
                        output_rule { cur_state3 with
                          constra = { cur_state3.constra with neq = [gen_pat_r,x_right]::cur_state3.constra.neq };
                          hypothesis = hypothesis_l;
                          hyp_tags = TestUnifTag2(occ)::hyp_tags_l
                        } (Pred(Param.bad_pred, []));

                        (* Pattern satisfied only on right side *)
			let (hypothesis_r,hyp_tags_r) = build_hyp x_left term_pat_right cur_state3 in
                        output_rule { cur_state3 with
                          constra = { cur_state3.constra with neq = [gen_pat_l,x_left]::cur_state3.constra.neq };
                          hypothesis = hypothesis_r;
                          hyp_tags = TestUnifTag2(occ)::hyp_tags_r
                        } (Pred(Param.bad_pred, []))
                      end
                  ) cur_state2 [term_pat_left] [term_pat_right];

                  if !for_equivalence
                  then
                    begin
                      (* Case left side succeed and right side fail *)
                      transl_one_side_fails (fun cur_state3 ->
			let (hypothesis_l,hyp_tags_l) = build_hyp term_pat_left x_right cur_state3 in
                        output_rule { cur_state3 with
                          hypothesis = hypothesis_l;
                          hyp_tags = (TestUnifTag2 occ)::hyp_tags_l
                        } (Pred(Param.bad_pred, []))
                      ) cur_state2 [term_pat_right] [term_pat_left];

                      (* Case right side succeed and left side fail *)
                      transl_one_side_fails (fun cur_state3 ->
			let (hypothesis_r,hyp_tags_r) = build_hyp x_left term_pat_right cur_state3 in
                        output_rule { cur_state3 with
                          hypothesis = hypothesis_r;
                          hyp_tags = (TestUnifTag2 occ)::hyp_tags_r
                        } (Pred(Param.bad_pred, []))
                      ) cur_state2 [term_pat_left] [term_pat_right]
                    end
                ) cur_state1 term_pattern
              ) cur_state pat
          end
        else
          begin

            transl_term_incl_destructor (fun cur_state1 channel_left channel_right ->
              (* Case both channel succeed *)
              transl_both_side_succeed (fun cur_state2 ->
                transl_pat (fun cur_state3 term_pattern binders ->
                  transl_term (fun cur_state4 term_pat_left term_pat_right ->
                    (* Generate the basic pattern variables *)
                    let x_right = Terms.new_var_def_term (Terms.get_term_type term_pat_right)
                    and x_left = Terms.new_var_def_term (Terms.get_term_type term_pat_left) in

                    (* Generate the pattern with universal_variable *)
                    let gen_pat_l, gen_pat_r = generate_pattern_with_uni_var binders term_pat_left term_pat_right in

		    let precise_ev_name =
		      if occ.precise || Param.get_precise()
		      then
			begin
			  let occ_name = get_occurrence_name_for_precise cur_state4 occ in
			  let precise_info = Action (Terms.get_term_type term_pat_left) in
			  let ev = Param.get_precise_event precise_info in
			  Reduction_helper.add_precise_info_occ occ precise_info;
			  add_in_precise_actions ev;
 			  Some (ev, occ_name)
			end
		      else
			None
		    in

		    let build_hyp term_pat_left term_pat_right cur_state =
                      let fact1 = mess_fact cur_state.cur_phase channel_left term_pat_left channel_right term_pat_right in
                      let tag1 = InputTag occ in
		      match precise_ev_name with
		      | Some(ev, occ_name) ->
			  (fact1::Pred(Param.event2_pred_block,[FunApp(ev,[occ_name;term_pat_left]);FunApp(ev,[occ_name;term_pat_right])])::cur_state.hypothesis,
			   tag1  :: PreciseTag(occ) ::cur_state.hyp_tags
                          )
		      | None ->
			  (fact1::cur_state.hypothesis, tag1::cur_state.hyp_tags)
                    in

                    (* Case where both pattern succeed *)

                    transl_both_side_succeed (fun cur_state5 ->
                      let (hypothesis,hyp_tags) = build_hyp term_pat_left term_pat_right cur_state5 in

                      (* Pattern satisfied in both sides *)
                      transl_process { cur_state5 with
                        name_params = (List.rev_map
                          (fun b -> (MVar(b, None), get_var_link cur_state5 b, Always)
                              ) binders) @ cur_state5.name_params;
                        name_params_types = (List.rev_map (fun b -> b.btype) binders)@cur_state5.name_params_types;
                        hypothesis = hypothesis;
                        hyp_tags = hyp_tags
                      } proc;

                      if !for_equivalence
                      then
                        begin
                          output_rule { cur_state5 with
                            hyp_tags = (InputPTag occ) :: cur_state5.hyp_tags
                          } (Pred(cur_state5.input_pred, [channel_left; channel_right]));

                          (* Pattern satisfied only on left side *)
			  let (hypothesis_l, hyp_tags_l) = build_hyp term_pat_left x_right cur_state5 in
                          output_rule { cur_state5 with
                            constra = { cur_state5.constra with neq = [gen_pat_r,x_right]::cur_state5.constra.neq };
                            hypothesis = hypothesis_l;
                            hyp_tags = TestUnifTag2(occ)::hyp_tags_l
                          } (Pred(Param.bad_pred, []));

                          (* Pattern satisfied only on right side *)
			  let (hypothesis_r, hyp_tags_r) = build_hyp x_left term_pat_right cur_state5 in
                          output_rule { cur_state5 with
                            constra = { cur_state5.constra with neq = [gen_pat_l,x_left]::cur_state5.constra.neq };
                            hypothesis = hypothesis_r;
                            hyp_tags = TestUnifTag2(occ)::hyp_tags_r
                          } (Pred(Param.bad_pred, []))
                        end

                    ) cur_state4  [term_pat_left] [term_pat_right];

                    if !for_equivalence
                    then
                      begin
                        (*  Case with left pattern succeed but right fail *)

                        transl_one_side_fails (fun cur_state5 ->
			  let (hypothesis_l, hyp_tags_l) = build_hyp term_pat_left x_right cur_state5 in
                          output_rule { cur_state5 with
                            hypothesis = hypothesis_l;
                            hyp_tags = TestUnifTag2(occ)::hyp_tags_l
                          } (Pred(Param.bad_pred, []))
                        ) cur_state4 [term_pat_right] [term_pat_left];

                        (*  Case with right pattern succeed but left fail *)

                        transl_one_side_fails (fun cur_state5 ->
 			  let (hypothesis_r, hyp_tags_r) = build_hyp x_left term_pat_right cur_state5 in
                          output_rule { cur_state5 with
                            hypothesis = hypothesis_r;
                            hyp_tags = TestUnifTag2(occ)::hyp_tags_r
                          } (Pred(Param.bad_pred, []))
                        ) cur_state4 [term_pat_left] [term_pat_right]
                      end
                  ) cur_state3 term_pattern
                ) cur_state2 pat
              ) cur_state1 [channel_left] [channel_right];

              if !for_equivalence
              then
                begin
                  (* Case left channel succeed and right channel fail *)
                  transl_one_side_fails (fun cur_state2 ->
                    output_rule { cur_state2 with
                      hyp_tags = (TestUnifTag2 occ)::cur_state2.hyp_tags
                    } (Pred(Param.bad_pred, []))
                  ) cur_state1 [channel_right] [channel_left];

                  (* Case right side succeed and left side fail *)
                  transl_one_side_fails (fun cur_state2 ->
                    output_rule { cur_state2 with
                      hyp_tags = (TestUnifTag2 occ)::cur_state2.hyp_tags
                    } (Pred(Param.bad_pred, []))
                  ) cur_state1 [channel_left] [channel_right]
                end
            ) cur_state (OInChannel(occ)) tc
          end
    | Output(term_ch, term, proc, occ) ->
        if optimize_mess cur_state term_ch then
          begin
               transl_term (fun cur_state1 term_left term_right ->
                  (* Case both sides succeed *)
                  transl_both_side_succeed (fun cur_state2 ->
                    transl_process { cur_state2 with
                        hyp_tags = (OutputTag occ)::cur_state2.hyp_tags
                      } proc;

                    output_rule { cur_state2 with
                        hyp_tags = (OutputTag occ)::cur_state2.hyp_tags
                      } (att_fact cur_state2.cur_phase term_left term_right)
                  ) cur_state1 [term_left] [term_right];

                  if !for_equivalence
                  then
                    begin
                      (* Case left side succeed and right side fail *)
                      transl_one_side_fails (fun cur_state2 ->
                        output_rule { cur_state2 with
                          hyp_tags = (TestUnifTag2 occ)::cur_state2.hyp_tags
                        } (Pred(Param.bad_pred, []))
                      ) cur_state1 [term_right] [term_left];

                      (* Case right side succeed and left side fail *)
                      transl_one_side_fails (fun cur_state2 ->
                        output_rule { cur_state2 with
                          hyp_tags = (TestUnifTag2 occ)::cur_state2.hyp_tags
                        } (Pred(Param.bad_pred, []))
                      ) cur_state1 [term_left] [term_right]
                    end
                 ) cur_state term
          end
        else
          begin
                transl_term (fun cur_state1 channel_left channel_right ->
                  transl_term (fun cur_state2 term_left term_right ->
                    (* Case both sides succeed *)
                    transl_both_side_succeed (fun cur_state3 ->
                      transl_process { cur_state3 with
                          hyp_tags = (OutputTag occ)::cur_state3.hyp_tags
                        } proc;

                      if !for_equivalence
                      then
                        output_rule { cur_state3 with
                            hyp_tags = (OutputPTag occ) :: cur_state3.hyp_tags
                          } (Pred(cur_state3.output_pred, [channel_left; channel_right]));

                      output_rule { cur_state3 with
                          hyp_tags = (OutputTag occ)::cur_state3.hyp_tags
                        } (mess_fact cur_state3.cur_phase channel_left term_left channel_right term_right)
                    ) cur_state2 [channel_left;term_left] [channel_right;term_right];

                    if !for_equivalence
                    then
                      begin
                        (* Case left side succeed and right side fail *)
                        transl_one_side_fails (fun cur_state3 ->
                          output_rule { cur_state3 with
                            hyp_tags = (TestUnifTag2 occ)::cur_state3.hyp_tags
                          } (Pred(Param.bad_pred, []))
                        ) cur_state2 [channel_right;term_right] [channel_left;term_left];

                        (* Case right side succeed and left side fail *)
                        transl_one_side_fails (fun cur_state3 ->
                          output_rule { cur_state3 with
                            hyp_tags = (TestUnifTag2 occ)::cur_state3.hyp_tags
                          } (Pred(Param.bad_pred, []))
                        ) cur_state2 [channel_left;term_left] [channel_right;term_right]
                      end
                  ) cur_state1 term
                ) cur_state term_ch
          end
    | Event(FunApp(f,_) as t,_,p,occ) ->
        let fstatus = Pievent.get_event_status cur_state.tr_pi_state f in

        (* Even if the event does nothing, the term t is evaluated *)
        transl_term (fun cur_state1 term_left term_right ->
          (* Case both sides succeed *)
          begin match fstatus.begin_status with
            | No ->
                transl_both_side_succeed (fun cur_state2 ->
                  if not !for_equivalence
                  then
                    begin match fstatus.end_status with
                      | No -> ()
                      | NoOcc ->
                          output_rule { cur_state2 with
                            hyp_tags = EventTag(occ) :: cur_state2.hyp_tags
                          } (Pred(Param.event2_pred, [term_left;term_right]));
                      | WithOcc -> Parsing_helper.internal_error "[pitranslweak.ml >> transl_process] Status of event should not be injective for equivalence queries."
                    end;
                  transl_process { cur_state2 with hyp_tags = (EventTag(occ)) :: cur_state2.hyp_tags } p
                ) cur_state1 [term_left] [term_right];
            | NoOcc ->
                transl_both_side_succeed (fun cur_state2 ->
                  if not !for_equivalence
                  then
                    begin match fstatus.end_status with
                      | No -> ()
                      | NoOcc ->
                          output_rule { cur_state2 with
                            hyp_tags = EventTag(occ) :: cur_state2.hyp_tags
                          } (Pred(Param.event2_pred, [term_left;term_right]));
                      | WithOcc -> Parsing_helper.internal_error "[pitranslweak.ml >> transl_process] Status of event should not be injective for equivalence queries."

                    end;
                  let cur_state3 =
                    { cur_state2 with
                      hypothesis = Pred(Param.event2_pred_block,[term_left;term_right]) :: cur_state2.hypothesis;
                      hyp_tags = BeginFact :: (EventTag(occ)) :: cur_state2.hyp_tags
                    }
                  in
                  transl_process cur_state3 p
                ) cur_state1 [term_left] [term_right];
            | WithOcc -> Parsing_helper.internal_error "[pitranslweak.ml >> transl_process] Status of event should not be injective for equivalence queries."
          end;

          if !for_equivalence
          then
            begin
              (* Case left side succeeds and right side fails *)
              transl_one_side_fails (fun cur_state2 ->
                output_rule { cur_state2 with
                  hyp_tags = (TestUnifTag2 occ)::cur_state2.hyp_tags
                  } (Pred(Param.bad_pred, []))
              ) cur_state1 [term_right] [term_left];

              (* Case right side succeeds and left side fails *)
              transl_one_side_fails (fun cur_state2 ->
                output_rule { cur_state2 with
                  hyp_tags = (TestUnifTag2 occ)::cur_state2.hyp_tags
                  } (Pred(Param.bad_pred, []))
              ) cur_state1 [term_left] [term_right]
            end
        ) cur_state t
    | Event(_,_,_,_) -> user_error ("Events should be function applications")
    | Insert(term,proc,occ) ->
        transl_term (fun cur_state1 term_left term_right ->
          (* Case both sides succeed *)
          transl_both_side_succeed (fun cur_state2 ->
            output_rule { cur_state2 with
              hyp_tags = (InsertTag occ) :: cur_state2.hyp_tags
            } (table_fact cur_state2.cur_phase term_left term_right);

            transl_process { cur_state2 with
              hyp_tags = (InsertTag occ) :: cur_state2.hyp_tags
            } proc;
          ) cur_state1 [term_left] [term_right];

          if !for_equivalence
          then
            begin
              (* Case left side succeeds and right side fails *)
              transl_one_side_fails (fun cur_state2 ->
                output_rule { cur_state2 with
                  hyp_tags = (TestUnifTag2 occ)::cur_state2.hyp_tags
                  } (Pred(Param.bad_pred, []))
              ) cur_state1 [term_right] [term_left];

              (* Case right side succeeds and left side fails *)
              transl_one_side_fails (fun cur_state2 ->
                output_rule { cur_state2 with
                  hyp_tags = (TestUnifTag2 occ)::cur_state2.hyp_tags
                  } (Pred(Param.bad_pred, []))
              ) cur_state1 [term_left] [term_right]
            end
        ) cur_state term
    | Get(pat,term,proc,proc_else,occ) ->
        transl_pat (fun cur_state1 term_pattern binders ->
          transl_term (fun cur_state2 term_pat_left term_pat_right ->

            let x_right = Terms.new_var_def_term (Terms.get_term_type term_pat_right)
            and x_left = Terms.new_var_def_term (Terms.get_term_type term_pat_right) in

            (* Generate the pattern with universal_variable *)
            let gen_pat_l, gen_pat_r = generate_pattern_with_uni_var binders term_pat_left term_pat_right in

            transl_term (fun cur_state3 term_left term_right ->

	      let precise_ev_name =
		if occ.precise || Param.get_precise()
		then
		  begin
                    let occ_name = get_occurrence_name_for_precise cur_state3 occ in
                    let precise_info = Action (Terms.get_term_type term_pat_left) in
                    let ev = Param.get_precise_event precise_info in
                    Reduction_helper.add_precise_info_occ occ precise_info;
                    add_in_precise_actions ev;
 		    Some (ev, occ_name)
		  end
		else
		  None
	      in

	      let build_hyp term_pat_left term_pat_right cur_state =
		let fact1 = table_fact cur_state.cur_phase term_pat_left term_pat_right in
                let tag1 = GetTag(occ) in
		match precise_ev_name with
		| Some(ev, occ_name) ->
                    (fact1::Pred(Param.event2_pred_block,[FunApp(ev,[occ_name;term_pat_left]);FunApp(ev,[occ_name;term_pat_right])])::cur_state.hypothesis,
                     tag1  :: PreciseTag(occ) :: cur_state.hyp_tags
                        )
		| None ->
                    (fact1::cur_state.hypothesis, tag1::cur_state.hyp_tags)
	      in

              (* Case both sides succeed *)
              transl_both_side_succeed (fun cur_state4 ->
                let (hypothesis,hyp_tags) = build_hyp term_pat_left term_pat_right cur_state4 in
                (* Success *)
                unify_list (fun () ->
                  transl_process { cur_state4 with
                    name_params = (List.rev_map
                      (fun b -> (MVar(b,None), get_var_link cur_state4 b, Always)
                          ) binders) @ cur_state4.name_params;
                    name_params_types = (List.rev_map (fun b -> b.btype) binders)@cur_state4.name_params_types;
                    hypothesis = hypothesis;
                    hyp_tags = hyp_tags;
                  } proc
                ) cur_state4 [term_left;term_right] [Terms.true_term;Terms.true_term];

                if !for_equivalence
                then
                  begin
                    (* BAD (Left ok / Right ko) *)
                    unify_list (fun () ->
                      output_rule { cur_state4 with
                        hypothesis = hypothesis;
                        constra = { cur_state4.constra with neq = [term_right,Terms.true_term]::cur_state4.constra.neq };
                        hyp_tags = TestUnifTag2(occ)::hyp_tags
                      } (Pred(Param.bad_pred, []));

		      let (hypothesis_l, hyp_tags_l) = build_hyp term_pat_left x_right cur_state4 in
                      output_rule { cur_state4 with
                        hypothesis = hypothesis_l;
                        constra = { cur_state4.constra with neq = [x_right,gen_pat_r]::cur_state4.constra.neq };
                        hyp_tags = TestUnifTag2(occ)::hyp_tags_l
                      } (Pred(Param.bad_pred, []))
                    ) cur_state4 [term_left] [Terms.true_term];

                    (* BAD (Left ko / Right ok) *)
                    unify_list (fun () ->
                      output_rule { cur_state4 with
                        hypothesis = (table_fact cur_state4.cur_phase term_pat_left term_pat_right) :: cur_state4.hypothesis;
                        constra = { cur_state4.constra with neq = [term_left,Terms.true_term]::cur_state4.constra.neq };
                        hyp_tags = TestUnifTag2(occ)::(GetTag(occ))::cur_state4.hyp_tags
                      } (Pred(Param.bad_pred, []));

		      let (hypothesis_r, hyp_tags_r) = build_hyp x_left term_pat_right cur_state4 in
                      output_rule { cur_state4 with
                        hypothesis = hypothesis_r;
                        constra = { cur_state4.constra with neq = [x_left,gen_pat_l]::cur_state4.constra.neq };
                        hyp_tags = TestUnifTag2(occ)::hyp_tags_r
                      } (Pred(Param.bad_pred, []))
                    ) cur_state4 [term_right] [Terms.true_term]
                  end
              ) cur_state3 [term_pat_left;term_left] [term_pat_right;term_right];

              if !for_equivalence
              then
                begin
                  (* Case left side succeed and right side fail *)
                  transl_one_side_fails (fun cur_state4 ->
                    (* BAD *)
                    unify_list (fun () ->
		      let (hypothesis_l, hyp_tags_l) = build_hyp term_pat_left x_right cur_state4 in
                      output_rule { cur_state4 with
                        hypothesis = hypothesis_l;
                        hyp_tags = TestUnifTag2(occ)::hyp_tags_l
                      } (Pred(Param.bad_pred, []))
                    ) cur_state4 [term_left] [Terms.true_term]
                  ) cur_state3 [term_pat_right;term_right] [term_pat_left;term_left];

                  (* Case right side succeed and left side fail *)
                  transl_one_side_fails (fun cur_state4 ->
                    (* BAD *)
                    unify_list (fun () ->
		      let (hypothesis_r, hyp_tags_r) = build_hyp x_left term_pat_right cur_state4 in
                      output_rule { cur_state4 with
                        hypothesis = hypothesis_r;
                        hyp_tags = TestUnifTag2(occ)::hyp_tags_r
                      } (Pred(Param.bad_pred, []))
                    ) cur_state3 [term_right] [Terms.true_term]
                  ) cur_state3 [term_pat_left;term_left] [term_pat_right;term_right]
                end

            ) cur_state2 term
         ) cur_state1 term_pattern
       ) cur_state pat;
       transl_process { cur_state with hyp_tags = GetTagElse(occ) :: cur_state.hyp_tags } proc_else
    | Phase(n,proc,_) ->
        transl_process { cur_state with
                        input_pred = Param.get_pred (InputPBin(n));
                        output_pred = Param.get_pred (OutputPBin(n));
                        cur_phase = n } proc
    | NamedProcess(_,_,p) ->
        transl_process cur_state p
    | Barrier _ | AnnBarrier _ ->
        internal_error "Barriers should not appear here (7)"
  )

(***********************************
	The attacker clauses
************************************)


(* Clauses corresponding to an application of a function

   [rules_Rf_for_red] does not need the rewrite rules f(...fail...) -> fail
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

let rules_Rf_for_red phase f_symb red_rules =
  let result_predicate = Param.get_pred (AttackerBin(phase, snd f_symb.f_type)) in
  if phase < !min_choice_phase then
    (* Optimize generation when no choice in the current phase *)
    List.iter (fun red_rule ->
      let (hyp1, concl1, side_c1) = Terms.copy_red red_rule in

      add_rule (List.map (fun t1 -> att_fact phase t1 t1) hyp1)
      	(att_fact phase concl1 concl1)
      	side_c1
      	(Apply(f_symb, result_predicate))
        ) red_rules
  else
    List.iter (fun red_rule1 ->
      List.iter (fun red_rule2 ->
        let (hyp1, concl1, side_c1) = Terms.copy_red red_rule1
        and (hyp2, concl2, side_c2) = Terms.copy_red red_rule2 in

        add_rule (List.map2 (fun t1 t2 -> att_fact phase t1 t2) hyp1 hyp2)
          (att_fact phase concl1 concl2)
          (Terms.wedge_constraints side_c1 side_c2)
          (Apply(f_symb, result_predicate))

      	  ) red_rules
      	) red_rules

let transl_attacker pi_state my_types phase =

  (* The attacker can apply all functions, including tuples *)
  List.iter (Terms.clauses_for_function (rules_Rf_for_red phase)) pi_state.pi_funs;
  Hashtbl.iter (fun _ -> Terms.clauses_for_function (rules_Rf_for_red phase)) Terms.tuple_table;

  List.iter (fun t ->
    let att_pred = Param.get_pred (AttackerBin(phase,t)) in
    let mess_pred = Param.get_pred (MessBin(phase,t)) in

    (* The attacker has any message sent on a channel he has (Rule Rl)*)
    let v1 = Terms.new_var_def_term t in
    let vc1 = Terms.new_var_def_term Param.channel_type in
    let v2 = Terms.new_var_def_term t in
    let vc2 = Terms.new_var_def_term Param.channel_type in
    add_rule [Pred(mess_pred, [vc1; v1; vc2; v2]); att_fact phase vc1 vc2]
      (Pred(att_pred, [v1; v2])) Terms.true_constraints (Rl(att_pred, mess_pred));

    if (!Param.active_attacker) then
      begin
        (* The attacker can send any message he has on any channel he has (Rule Rs) *)
      	let v1 = Terms.new_var_def_term t in
      	let vc1 = Terms.new_var_def_term Param.channel_type in
      	let v2 = Terms.new_var_def_term t in
      	let vc2 = Terms.new_var_def_term Param.channel_type in
      	add_rule [att_fact phase vc1 vc2; Pred(att_pred, [v1; v2])]
          (Pred(mess_pred, [vc1; v1; vc2; v2])) Terms.true_constraints (Rs(att_pred, mess_pred))
      end;

    (* Clauses for equality *)
    let v = Terms.new_var_def_term t in
    add_rule [] (Pred(Param.get_pred (Equal(t)), [v;v])) Terms.true_constraints LblEq;

    (* Check for destructor failure (Rfailure) *)

    if phase >= !min_choice_phase
    then
      begin
        let x = Terms.new_var_def_term t
        and fail = Terms.get_fail_term t in

        add_rule [Pred(att_pred, [x; fail])] (Pred(Param.bad_pred, [])) Terms.true_constraints (Rfail(att_pred));
        add_rule [Pred(att_pred, [fail; x])] (Pred(Param.bad_pred, [])) Terms.true_constraints (Rfail(att_pred))
      end;

    ) my_types;

  if phase >= !min_choice_phase && !for_equivalence then
    begin
      let att_pred = Param.get_pred (AttackerBin(phase,Param.channel_type)) in
      let input_pred = Param.get_pred (InputPBin(phase)) in
      let output_pred = Param.get_pred (OutputPBin(phase)) in

      (* The attacker can do communications (Rule Ri and Ro)*)
      let vc1 = Terms.new_var_def_term Param.channel_type in
      let vc2 = Terms.new_var_def_term Param.channel_type in
      add_rule [Pred(att_pred, [vc1; vc2])] (Pred(input_pred, [vc1;vc2])) Terms.true_constraints (Ri(att_pred, input_pred));
      let vc1 = Terms.new_var_def_term Param.channel_type in
      let vc2 = Terms.new_var_def_term Param.channel_type in
      add_rule [Pred(att_pred, [vc1; vc2])] (Pred(output_pred, [vc1; vc2])) Terms.true_constraints (Ro(att_pred, output_pred));

      (* Check communications do not reveal secrets (Rule Rcom and Rcom')*)
      let vc = Terms.new_var_def_term Param.channel_type in
      let vc1 = Terms.new_var_def_term Param.channel_type in
      let vc2 = Terms.new_var_def_term Param.channel_type in
      add_rule [Pred(input_pred, [vc; vc1]);
      		 Pred(output_pred, [vc; vc2])]
      	 (Pred(Param.bad_pred, [])) (Terms.constraints_of_neq vc1 vc2)
      	 (TestComm(input_pred, output_pred));

      let vc = Terms.new_var_def_term Param.channel_type in
      let vc1 = Terms.new_var_def_term Param.channel_type in
      let vc2 = Terms.new_var_def_term Param.channel_type in
      add_rule [Pred(input_pred, [vc1; vc]);
      		 Pred(output_pred, [vc2; vc])]
      	(Pred(Param.bad_pred, [])) (Terms.constraints_of_neq vc1 vc2)
      	(TestComm(input_pred, output_pred))

     end

(* Convert terms (possibly with choice) to one term or to
   a pair of terms.
   You need to cleanup links after calling convert_to_1 and
   convert_to_2. *)

let rec convert_to_2 = function
    Var x ->
      begin
	match x.link with
	  TLink (FunApp(_,[t1;t2])) -> (t1,t2)
	| NoLink -> (Var x, Var x)
	| _ -> assert false
      end
  | FunApp(f, [t1;t2]) when f.f_cat == Choice ->
      let (t1',_) = convert_to_2 t1 in
      let (_,t2') = convert_to_2 t2 in
      (t1', t2')
  | FunApp(f, l) ->
      match f.f_cat with
	Name { prev_inputs_meaning = pim } ->
	  let l' = List.map2 (fun t m ->
	    match m with
	      MSid _ | MCompSid | MAttSid ->
		begin
		try
		  convert_to_1 t
		with Terms.Unify ->
		  user_error "In not declarations, session identifiers should be variables."
		end
	    | _ ->
	        (* The arguments of names are always choice, except for session identifiers *)
		let (t1,t2) = convert_to_2 t in
		FunApp(Param.choice_fun (Terms.get_term_type t1), [t1;t2])
	      ) l pim
	  in
	  (FunApp(f, l'), FunApp(f, l'))
      |	_ ->
	  let (l1, l2) = List.split (List.map convert_to_2 l) in
	  (FunApp(f, l1), FunApp(f, l2))

(* convert_to_1 raises Terms.Unify when there is a choice
   that cannot be unified into one term. *)

and convert_to_1 t =
  let (t1, t2) = convert_to_2 t in
  Terms.unify t1 t2;
  t1

let convert_to_2 t =
  let (t1, t2) = convert_to_2 t in
  (Terms.copy_term2 t1, Terms.copy_term2 t2)

let convert_to_1 t =
  Terms.copy_term2 (convert_to_1 t)

(* Convert formats (possibly with choice) to one format or to
   a pair of formats.
   Since nounif cannot be used for a phase earlier than the
   one mentioned in the nounif declaration, it is not essential
   that we can convert a nounif made with choice into a single format.
   Moreover, we do not have a unification for formats ready,
   so we prefer forbidding choice when a single format is needed.
 *)

let rec convertformat_to_1 = function
    FVar x -> FVar x
  | FAny x -> FAny x
  | FFunApp(f, [t1;t2]) when f.f_cat == Choice ->
      Parsing_helper.user_error "choice not allowed in nounif declarations for phases in which choice is not used in the process"
  | FFunApp(f, l) ->
      match f.f_cat with
        Name { prev_inputs_meaning = pim } ->
          (* The arguments of names are always choice, except for
             session identifiers *)
          let l' = List.map2 (fun t m ->
            match m with
              MSid _ | MCompSid | MAttSid ->
                convertformat_to_1 t
            | _ ->
                let t' = convertformat_to_1 t in
                FFunApp(Param.choice_fun (Terms.get_format_type t'), [t';t'])
                ) l pim
          in
          FFunApp(f, l')
      | _ ->
          FFunApp(f, List.map convertformat_to_1 l)

let rec convertformat_to_2 = function
    FVar x -> (FVar x, FVar x)
  | FAny x -> (FAny x, FAny x)
  | FFunApp(f, [t1;t2]) when f.f_cat == Choice ->
      let (t1',_) = convertformat_to_2 t1 in
      let (_,t2') = convertformat_to_2 t2 in
      (t1', t2')
  | FFunApp(f, l) ->
      match f.f_cat with
        Name { prev_inputs_meaning = pim } ->
          (* The arguments of names are always choice, except for
             session identifiers *)
          let l' = List.map2 (fun t m ->
            match m with
              MSid _ | MCompSid | MAttSid ->
                begin
                  match t with
                    FVar x -> assert (x.btype == Param.sid_type); FVar x
                  | FAny x -> assert (x.btype == Param.sid_type); FAny x
                  | _ -> Parsing_helper.user_error "In nounif declarations, session identifiers should be variables."
                end
            | _ ->
                let (t1,t2) = convertformat_to_2 t in
                FFunApp(Param.choice_fun (Terms.get_format_type t1), [t1;t2])
                ) l pim
          in
          (FFunApp(f, l'), FFunApp(f, l'))
      | _ ->
          let (l1, l2) = List.split (List.map convertformat_to_2 l) in
          (FFunApp(f, l1), FFunApp(f, l2))

(* Take into account "not fact" declarations (secrecy assumptions) *)

let get_not pi_state =
  let not_set = ref [] in
  let add_not f =
    not_set := f ::(!not_set)
  in
   List.iter (function
       QFact({ p_info = Attacker(i,ty) },_,[t],_) ->
      	 (* For attacker: not declarations, the not declaration is also
	    valid in previous phases, because of the implication
	      attacker_p(i):x => attacker_p(i+1):x
	    Furthermore, we have to translate unary to binary not declarations *)
	 for j = 0 to i do
	   if j < !min_choice_phase then
	     (* Phase coded by unary predicate, since it does not use choice *)
	     let att_j = Param.get_pred (Attacker(j,ty)) in
	     try
	       add_not(Pred(att_j,[Terms.auto_cleanup (fun () -> convert_to_1 t)]))
	     with Terms.Unify -> ()
	   else
	     (* Phase coded by binary predicate *)
	     let att2_j = Param.get_pred (AttackerBin(j,ty)) in
	     let (t',t'') = Terms.auto_cleanup (fun () -> convert_to_2 t) in
	     add_not(Pred(att2_j,[t';t'']))
	 done
     | QFact({ p_info = Mess(i,ty) } as p,_,[t1;t2],_) ->
	 (* translate unary to binary not declarations *)
	 if i < !min_choice_phase then
	   (* Phase coded by unary predicate, since it does not use choice *)
	   try
	     let t1', t2' = Terms.auto_cleanup (fun () ->
	       convert_to_1 t1, convert_to_1 t2)
	     in
	     add_not(Pred(p, [t1'; t2']))
	   with Terms.Unify -> ()
	 else
	   (* Phase coded by binary predicate *)
	   let mess2_i = Param.get_pred (MessBin(i,ty)) in
	   let (t1', t1''), (t2', t2'') = Terms.auto_cleanup (fun () ->
	     convert_to_2 t1, convert_to_2 t2)
	   in
	   add_not(Pred(mess2_i,[t1';t2';t1'';t2'']))
     | QFact({ p_info = Table(i) },_,[t],_) ->
      	 (* For "table" not declarations, the not declaration is also
	    valid in previous phases, because of the implication
	      table_p(i):x => table_p(i+1):x
	    Furthermore, we have to translate unary to binary not declarations *)
	 for j = 0 to i do
	   if j < !min_choice_phase then
	     (* Phase coded by unary predicate, since it does not use choice *)
	     let table_j = Param.get_pred (Table(j)) in
	     try
	       add_not(Pred(table_j,[Terms.auto_cleanup (fun () -> convert_to_1 t)]))
	     with Terms.Unify -> ()
	   else
	     (* Phase coded by binary predicate *)
	     let table2_j = Param.get_pred (TableBin(j)) in
	     let (t',t'') = Terms.auto_cleanup (fun () -> convert_to_2 t) in
	     add_not(Pred(table2_j,[t';t'']))
	 done
     | _ -> Parsing_helper.user_error "The only allowed facts in \"not\" declarations are attacker, mess, and table predicates (for process equivalences, user-defined predicates are forbidden)."
	   ) (pi_state.pi_get_not pi_state);
  !not_set

(* Compute predicates that queries try to prove *)

(* [add p accu] adds the predicate [p] to [accu] if it is not already present *)
let add p accu =
  if List.memq p accu then accu else p::accu

let add_events_event accu = function
  | QSEvent(_,_,_,_,FunApp(ev,_)) | QSEvent2(FunApp(ev,_),_) -> add ev accu
  | QSEvent _ | QSEvent2 _ -> internal_error "[pitranslweak.ml >> add_pred_prove_and_events_for_lemmas_event] Events predicate should have an event symbol."
  | QNeq _ | QEq _ | QGeq _ | QGr _ | QIsNat _ | QFact _ -> accu

let rec add_events_realquery accu = function
  | Before(_, concl) -> add_events_concl accu concl

and add_events_concl accu = function
  | QTrue | QFalse | QConstraints _ -> accu (* no events in constraint *)
  | QEvent e -> add_events_event accu e
  | NestedQuery(Before(hyp,concl)) ->
      let accu' = List.fold_left add_events_event accu hyp in
      add_events_concl accu' concl
  | QAnd(c1,c2) | QOr(c1,c2) ->
      add_events_concl (add_events_concl accu c1) c2

let add_events_query accu = function
  | RealQuery(q,_),_ -> add_events_realquery accu q
  | _ -> Parsing_helper.internal_error "[pitranslweak.ml >> add_events_query] Unexpected query for lemmas."

let get_events ql =
  List.fold_left add_events_query [] ql

(* Global translation *)

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


let reset() =
  terms_to_add_in_name_params := [];
  min_choice_phase := max_int;
  nrule := 0;
  red_rules := [];
  no_unif_set := [];
  for_equivalence := true;
  current_precise_actions := [];
  Hashtbl.reset explored_occurrences

let transl pi_state =
  (* Reset the record of which occurrence are precise (needed for reconstruction) *)
  Reduction_helper.reset_occ_precise_event ();
  reset ();
  let p =
    match pi_state.pi_process_query with
      SingleProcessSingleQuery(p, (ChoiceQuery | ChoiceQEnc _)) -> p.proc
    | SingleProcessSingleQuery(p, (CorrespQEnc _ | CorrespQuery _)) ->
        (* Case when we try to prove lemmas on biprocesses. *)
        for_equivalence := false;
        p.proc
    | _ -> Parsing_helper.internal_error "query not supported by pitranslweak"
  in
  Reduction_helper.reset_name_args p;
  let my_types = if Param.get_ignore_types() then [Param.any_type] else pi_state.pi_types in
  min_choice_phase :=
     begin
       match pi_state.pi_min_choice_phase with
       | Set min_phase -> min_phase
       | Unset -> Parsing_helper.internal_error "Pitranslweak.transl: pi_min_choice_phase should be set"
     end;

  for i = 0 to pi_state.pi_max_used_phase do

    transl_attacker pi_state my_types i;

    List.iter (fun t ->
      (* The attacker has the fail constants *)
      let fail_term = Terms.get_fail_term t in
      add_rule [] (att_fact i fail_term fail_term) Terms.true_constraints Init;

      let att_i = Param.get_pred (AttackerBin(i,t)) in
      if i < !min_choice_phase then
        begin
      	  (* Phase coded by unary predicates *)
      	  let v = Terms.new_var_def t in
      	  let att_i = Param.get_pred (Attacker(i,t)) in
      	  add_no_unif (att_i, [FVar v]) (NoUnifValue Selfun.never_select_weight) [Hypothesis]
      	end
      else
      	begin
      	  (* Phase coded by binary predicates *)
      	  let v1 = Terms.new_var_def t in
      	  let v2 = Terms.new_var_def t in
      	  add_no_unif (att_i, [FVar v1; FVar v2]) (NoUnifValue Selfun.never_select_weight) [Hypothesis]
      	end;

      if i > 0 then
      	(* It is enough to transmit only messages from one phase to the next,
      	   because the attacker already has (fail, fail) in all phases
      	   and the cases (fail, x) and (x, fail) immediately lead
      	   to bad in all cases. *)
      	let w1 = Terms.new_var_def_term t in
      	let w2 = Terms.new_var_def_term t in
      	let att_im1 = Param.get_pred (AttackerBin(i-1,t)) in
      	add_rule [Pred(att_im1, [w1; w2])] (Pred(att_i, [w1; w2])) Terms.true_constraints PhaseChange
    ) my_types;

    if i > 0 then
      let w1 = Terms.new_var_def_term Param.table_type in
      let w2 = Terms.new_var_def_term Param.table_type in
      let tbl_i = Param.get_pred (TableBin(i)) in
      let tbl_im1 = Param.get_pred (TableBin(i-1)) in
      add_rule [Pred(tbl_im1, [w1; w2])] (Pred(tbl_i, [w1; w2])) Terms.true_constraints TblPhaseChange
  done;


  (* Knowing the free names and creating new names is necessary only in phase 0.
     The subsequent phases will get them by attacker'_i(x,y) -> attacker'_{i+1}(x,y) *)

  (* The attacker has the public free names *)
  List.iter (fun ch ->
    if not ch.f_private then
      add_rule [] (att_fact 0 (FunApp(ch, [])) (FunApp(ch, []))) Terms.true_constraints Init) pi_state.pi_freenames;

  List.iter (fun t ->
    (* The attacker can create new names *)
    let v1 = Terms.new_var_def_term Param.sid_type in
    let new_name_fun = Terms.new_name_fun t in
    (* Fix now how the name [new_name_fun] is displayed, to avoid different
       displays in different clauses/derivations *)
    ignore (Display.string_of_fsymb new_name_fun);
    add_rule [] (att_fact 0 (FunApp(new_name_fun, [v1])) (FunApp(new_name_fun, [v1])))
      Terms.true_constraints (Rn (Param.get_pred (AttackerBin(0, t))));

    (* Rules that derive bad are necessary only in the last phase.
       Previous phases will get them by attacker'_i(x,y) -> attacker'_{i+1}(x,y) *)

    let att_pred = Param.get_pred (AttackerBin(pi_state.pi_max_used_phase, t)) in

    (* The attacker can perform equality tests *)
    let v1 = Terms.new_var_def_term t in
    let v2 = Terms.new_var_def_term t in
    let v3 = Terms.new_var_def_term t in
    add_rule [Pred(att_pred, [v1; v2]); Pred(att_pred, [v1; v3])]
    (Pred(Param.bad_pred, [])) (Terms.constraints_of_neq v2 v3) (TestEq(att_pred));

    let v1 = Terms.new_var_def_term t in
    let v2 = Terms.new_var_def_term t in
    let v3 = Terms.new_var_def_term t in
    add_rule [Pred(att_pred, [v2; v1]); Pred(att_pred, [v3; v1])]
    (Pred(Param.bad_pred, [])) (Terms.constraints_of_neq v2 v3) (TestEq(att_pred))
  ) my_types;

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

  (* Translate the process into clauses *)

  let cur_state_init =
    { tr_pi_state = pi_state;
      hypothesis = []; constra = Terms.true_constraints;
      name_params = [];  name_params_types = [];
      repl_count = 0;
      input_pred = Param.get_pred (InputPBin(0));
      output_pred = Param.get_pred (OutputPBin(0));
      cur_phase = 0;
      hyp_tags = [];
      record_fun_opt = None
    }
  in

  let tmp_min_choice_phase = !min_choice_phase in
  let tmp_nrule = !nrule in
  let tmp_for_equivalence = !for_equivalence in
  let tmp_current_precise_actions = !current_precise_actions in

  Terms.auto_cleanup (fun () -> set_free_names_prev_inputs (fun () -> transl_process cur_state_init p) pi_state);

  let generate_process_clauses f_add =
    min_choice_phase := tmp_min_choice_phase;
    nrule := tmp_nrule;
    for_equivalence := tmp_for_equivalence;
    current_precise_actions := tmp_current_precise_actions;
    let cur_state = { cur_state_init with record_fun_opt = Some f_add } in
    Terms.auto_cleanup (fun () -> set_free_names_prev_inputs (fun () ->  transl_process cur_state p) pi_state)
  in
  (* Take into account "nounif" declarations *)

  List.iter (function (f,n,opts) ->
    let fact_format =
      (* translate unary to binary nounif declarations *)
      match f with
        | ({ p_info = Attacker(i,ty) } as pred, [t]) ->
            if i < !min_choice_phase then
              (* Phase coded by unary predicate, since it does not use choice *)
              pred, [convertformat_to_1 t]
            else
              (* Phase coded by binary predicate *)
              let att2_i = Param.get_pred (AttackerBin(i,ty)) in
              let (t', t'') = convertformat_to_2 t in
              att2_i, [t';t'']
        | ({ p_info = Mess(i,ty) } as pred, [t1;t2]) ->
            if i < !min_choice_phase then
              (* Phase coded by unary predicate, since it does not use choice *)
              pred, [convertformat_to_1 t1; convertformat_to_1 t2]
            else
              (* Phase coded by binary predicate *)
              let mess2_i = Param.get_pred (MessBin(i,ty)) in
              let (t1', t1'') = convertformat_to_2 t1 in
              let (t2', t2'') = convertformat_to_2 t2 in
              mess2_i,[t1';t2';t1'';t2'']
        | ({ p_info = Table(i) } as pred, [t]) ->
            if i < !min_choice_phase then
              (* Phase coded by unary predicate, since it does not use choice *)
              pred, [convertformat_to_1 t]
            else
              (* Phase coded by binary predicate *)
              let table2_i = Param.get_pred (TableBin(i)) in
              let (t', t'') = convertformat_to_2 t in
              table2_i, [t';t'']
        | _ -> Parsing_helper.user_error "The only allowed facts in \"nounif\" declarations are attacker, mess, and table predicates (for process equivalences, user-defined predicates are forbidden)."
    in
    let fact_format = Selfun.homogeneous_format fact_format in

    if !Param.verbose_term
    then Display.Text.display_nounif_declaration f (Selfun.weight_of_user_weight n) opts;
    
    add_no_unif fact_format n opts
  ) (pi_state.pi_get_nounif pi_state);

  let events_in_queries = match pi_state.pi_process_query with
    | SingleProcessSingleQuery(_, (ChoiceQuery | ChoiceQEnc _)) -> []
    | SingleProcessSingleQuery(_, CorrespQEnc(qql,_)) -> get_events (List.map snd qql)
    | SingleProcessSingleQuery(_, CorrespQuery(ql,_)) -> get_events ql
    | _ -> Parsing_helper.internal_error "query not supported by pitranslweak"
  in

  let pi_state' =
    { pi_state with
      pi_terms_to_add_in_name_params = Set(!terms_to_add_in_name_params);
      pi_precise_actions = !current_precise_actions
    }
  in
  let horn_state =
    { h_clauses = ToGenerate (List.rev (!red_rules),generate_process_clauses);
      h_equations = pi_state.pi_equations;
      h_close_with_equations = false;
      h_not = get_not pi_state;
      h_elimtrue = [];
      h_equiv = pi_state.pi_equivalence_clauses;
      h_nounif = !no_unif_set;
      h_clauses_to_initialize_selfun = [];
      h_solver_kind = Solve_Equivalence;
      h_lemmas = [];
      h_pred_prove = [];
	(* The only queries that we can prove are lemmas, and
           their conclusions can contain only events, blocking predicates,
           and constraints, so nothing needs to be added for those in
           h_pred_prove.
           Lemma assumptions and assumptions of queries proved by induction
	   added in Lemma.transl_lemmas *)
     h_event_in_queries = events_in_queries
    }
  in
  reset();
  horn_state, pi_state'
