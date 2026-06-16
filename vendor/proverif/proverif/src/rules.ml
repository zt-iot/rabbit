open Parsing_helper
open Types
open Terms

(* Debug verification *)

let debug_check_ordered_rule msg ord_rule = match ord_rule.order_data with
  | None -> ()
  | Some ord_data ->
      let (hypl,concl,_,_) = ord_rule.rule in
      if List.length ord_data != List.length hypl
      then internal_error (Printf.sprintf "[%s >> debug_check_ordered_rule] The number of hyp differs from the number of order data." msg);

      let nb_pred = match concl with
        | Pred({ p_info = Combined pl; _ }, _) -> List.length pl
        | _ -> 1
      in
      List.iter (fun (ord_fun,_) ->
        if List.exists (fun (i,_) -> i < 0 || i > nb_pred) ord_fun
        then internal_error (Printf.sprintf "[%s >> debug_check_ordered_rule] The ordering function is out of scope" msg);
      ) ord_data

(* let resol_step = ref 0 *)

(* Global variables. *)

let sound_mode = ref false
let is_inside_query = ref false
let initialized = ref false
let not_set = ref ([]: fact list)
let elimtrue_set = ref ([]: (int * fact) list)
let close_with_equations = ref false
let events_only_for_lemmas = ref []
let events_only_for_lemmas_without_options = ref []
let all_original_lemmas = ref []

(* Predicates to prove *)

type predicates_to_prove_t =
  {
    mutable tp_attacker : int; (* The maximal phase for the attacker predicate *)
    mutable tp_table : int; (* The maximal phase for the table predicate *)
    mutable tp_others : predicate list
  }

(* For attacker facts that occur in the conclusion of queries, we need
   to add all attacker facts of previous phases and of any type to the predicates to prove.
   For attacker facts that occur in hypotheses of lemmas, we need to add
   all attacker facts of previous phases to predicates to prove
   (because the lemma matching allows matching attacker phase n in the hypothesis of the clause
   with attacker phase n' for n'>=n in the hypothesis of the lemma).
   For simplicity, in both cases, we add all attacker facts of previous phases and of any type
   to the predicates to prove, and we remember only the maximum phase in field [tp_attacker].
*)

let pred_to_prove = { tp_attacker = -1; tp_table = -1; tp_others = [] }

let initialise_pred_to_prove pred_list =
  pred_to_prove.tp_attacker <- -1;
  pred_to_prove.tp_table <- -1;
  pred_to_prove.tp_others <- [];

  List.iter (fun p -> match p.p_info with
    | Attacker(n,_) | AttackerBin(n,_) -> pred_to_prove.tp_attacker <- max pred_to_prove.tp_attacker n
    | Table n | TableBin n -> pred_to_prove.tp_table <- max pred_to_prove.tp_table n
    | _ ->
        if not (List.memq p pred_to_prove.tp_others)
        then pred_to_prove.tp_others <- p :: pred_to_prove.tp_others
  ) pred_list

let reset_pred_to_prove () =
  pred_to_prove.tp_attacker <- -1;
  pred_to_prove.tp_table <- -1;
  pred_to_prove.tp_others <- []

let is_pred_to_prove p = match p.p_info with
  | Attacker(n,_) | AttackerBin(n,_) -> pred_to_prove.tp_attacker >= n
  | Table n | TableBin n -> pred_to_prove.tp_table >= n
  | _ ->
      p == Param.event_pred_block || p == Param.inj_event_pred_block || p == Param.event2_pred_block ||
      p == Param.event_pred || p == Param.inj_event_pred || p == Param.event2_pred ||
      List.memq p pred_to_prove.tp_others

let is_pred_to_prove_fact = function
  | Pred(p,_) -> is_pred_to_prove p

(* Ordered reduction *)

let get_order_data ord_rule = match ord_rule.order_data with
  | None -> internal_error "[rules.ml >> get_order_data] Should only be applied when there are ordering data."
  | Some ord_data -> ord_data

let strict_ordering_function (ord_fun:ordering_function) =
  Terms.mapq_list (function (i,Leq) -> (i,Less) | t -> t) ord_fun

(* Block-predicate of user-defined predicate cannot be ordered:
   such predicates are added by lemmas and lemmas that conclude user-defined predicates
   just prove logical properties without any ordering constraints. *)
let can_pred_have_ordering_fun p =
  if p == Param.event_pred_block || p == Param.inj_event_pred_block || p == Param.event2_pred_block || p == Param.event_pred || p == Param.inj_event_pred || p == Param.event2_pred
  then true
  else
    match p.p_info with
      | Attacker _ | Mess _ | Table _ | AttackerBin _ | MessBin _ | TableBin _ | UserPred _ -> true
      | Block { p_info = Attacker _ | Mess _ | Table _ | AttackerBin _ | MessBin _ | TableBin _ ; _ } -> true
      | _ -> false

let can_fact_have_ordering_fun = function
  | Pred(p,_) -> can_pred_have_ordering_fun p

let create_ordered_fact (ord_fun:ordering_function) f =
  if can_fact_have_ordering_fun f then ord_fun else []

let implies_ordering_function_bool ord_fun1 ord_fun2 =
  try Database.implies_ordering_function ord_fun1 ord_fun2; true with NoMatch -> false

(* Generate the ordering function corresponding to the intersection of ord_fun1 and ord_fun2.
   I.E. \tau \delta(i) \tau' iff \tau \delta1(i) \tau' && \tau \delta2(i) \tau' *)
let rec inter_ordering_fun ord_fun1 ord_fun2 =
  match ord_fun1, ord_fun2 with
  | [], _ -> ord_fun2
  | _, [] -> ord_fun1
  | (i1,ord1)::q1, (i2,_)::q2 when i1 < i2 -> (i1,ord1) :: (inter_ordering_fun q1 ord_fun2)
  | (i1,_)::q1, (i2,ord2)::q2 when i1 > i2 -> (i2,ord2) :: (inter_ordering_fun ord_fun1 q2)
      (* At this point, both lists start with (i,_) for the same i *)
  | (i,Less)::q1, _::q2
  | _::q1, (i,Less)::q2 -> (i,Less)::(inter_ordering_fun q1 q2)
  | t::q1, _::q2 -> t :: (inter_ordering_fun q1 q2)

(* We allow ordering constraints saying that
   a user-defined predicate happens before another user-defined predicate
   and a non user-defined predicate happens before another non user-defined predicate.
   We never say that a non user-defined predicate happens before a user-defined predicate because there are no clauses with a non user-defined predicate in hypothesis (except equal, which is not ordered) and a user-defined predicate in the conclusion.
   The following function forbids saying that a user-defined predicate happens before a non user-defined predicate. (The ordering for user-defined predicate relies on the length of the derivation, while the ordering for non user-defined predicates relies on the length of the trace.) *)
let allowed_ordering_application hyp concl = match hyp,concl with
  | Pred(p_h,_), Pred(p_c,_) -> Terms.is_user_defined p_c || not (Terms.is_user_defined p_h)

let saturated_reduction_of_reduction ((hypl, concl, _, _) as rule) =

  let (application_result, strict_order_to_compute) =
    List.fold_right (fun fact (accu_ord,accu_strict) ->
      if can_fact_have_ordering_fun fact && allowed_ordering_application fact concl
      then
        let to_prove = is_pred_to_prove_fact fact in
        (Some to_prove :: accu_ord, to_prove || accu_strict)
      else
        (None :: accu_ord,accu_strict)
          ) hypl ([],false)
  in

  let generate_ordering_data (ord_fun,nounif_sel) =
    let strict_ord_fun =
      if strict_order_to_compute
      then strict_ordering_function ord_fun
      else [] (* In this case, it will be never used *)
    in
    List.map (function
      | None -> ([],nounif_sel)
      | Some true -> (strict_ord_fun,nounif_sel)
      | _ -> (ord_fun,nounif_sel)
    ) application_result
  in

  {
    sat_rule = rule;
    sat_generate_ordering_data = generate_ordering_data
  }

(*****************************************************************
        Analysis of the history for ordered clauses
******************************************************************)

type analysed_history =
  {
    a_hist : history;
    a_order_data : (ordering_function * int) list
  }

let get_order_data_from_analyed_history_op = function
  | None -> internal_error "[rules.ml >> get_order_data_from_analyed_history_op] This function should only be applied when order data exist."
  | Some ana_hist -> ana_hist.a_order_data

(* [replace_nth_list l1 n l2] returns a list obtained by replacing the [n]-th element of list [l2] with list [l1]. *)
let rec replace_nth_list l1 n = function
    [] -> internal_error "replace_nth_list error"
  | (a::l) -> if n = 0 then l1 @ l else a::(replace_nth_list l1 (n-1) l)

(* [generate_subsuming_ordering_fun \delta1 \delta2 generates an ordering function \delta such
   that \delta subsumes \delta1 and \delta subsumes \delta2 *)
let rec generate_subsuming_ordering_fun ord_fun1 ord_fun2 =
  match ord_fun1, ord_fun2 with
  | [], _ | _, [] -> []
  | (i1,_)::q1, (i2,_)::_ when i1 < i2 -> generate_subsuming_ordering_fun q1 ord_fun2
  | (i1,_)::_, (i2,_)::q2 when i1 > i2 -> generate_subsuming_ordering_fun ord_fun1 q2
    (* At this point, both lists start with (i,_) for the same i *)
  | (i,Leq)::q1, _::q2
  | _::q1, (i,Leq)::q2 -> (i,Leq)::(generate_subsuming_ordering_fun q1 q2)
  | t::q1, _::q2 -> t::(generate_subsuming_ordering_fun q1 q2)

(* [generate_ordering_fun_from_lemma ord_data_list matched_hyp] returns an ordering function
   that is guaranteed to hold for facts added by a lemma, knowing that the facts of the clause
   matched by the hypotheses of the lemma are specified by [matched_hyp] and the ordering
   information for the clause is given by [ord_data_list]. *)
let generate_ordering_fun_from_lemma ord_data_list matched_hyp =
  let get_ord_from_one_matched_hyp (i,_) =
    if i < 0 then
      (* Corresponds to the -i th fact of the conclusion. *)
      [-i,Leq]
    else
      (* Corresponds to the i th fact of the hypotheses. *)
      fst (List.nth ord_data_list i)
  in

  let rec go_through_matched_hyp accu = function
    | [] -> accu
    | (_,Pred(p,_))::_ when Terms.is_user_defined p -> accu
    | h::q ->
        let ord_fun = get_ord_from_one_matched_hyp h in
        go_through_matched_hyp (generate_subsuming_ordering_fun accu ord_fun) q
  in

  match matched_hyp with
    | [] -> internal_error "[rules.ml >> generate_ordering_fun_from_lemma] A lemma should have at least one fact in its premise."
    | (_,Pred(p,_))::_ when Terms.is_user_defined p -> []
    | h::q ->
        let ord_fun = get_ord_from_one_matched_hyp h in
        go_through_matched_hyp ord_fun q

(* [analyse_history] analyzes the history [hist]
   of the rule to retrieve the order information list of the hypotheses of the clauses.

   History:
    - Any : Basic removal.
    - Removed : Corresponds to the transformation rule Red_o
        -> We need to compute the intersection of ordering function and nounif selection
    - Resolution(hist1,n,hist2) : Corresponds to either the transformation rule DataHyp,
        element simplification or equiv set.
          -> For Data Hyp, we must have hist1 of the form Rule(-1,Apply f ,_,_,_) with f of cat Tuple
          -> For Element simplification, hist1 is of the form Rule(-1, Elem _ ,_,_,_)
          -> For Equiv Set, hist1 is of the form Rule(_, LbLEquiv,_,_,_)
    - HLemma : Corresponds to the application of Lemmas
    - HCaseDistinction : Corresponds to the generation of set of clauses completely covering
        our initial set of clauses.
        -> Does not modify the order nor the nounif selection
*)

let ordered_rule_of_analysed_history_op ana_hist_op ((_,_,hist,_) as rule) =
  match ana_hist_op with
  | None -> { rule = rule; order_data = None }
  | Some ana_hist ->
      assert (hist == ana_hist.a_hist);
      { rule = rule; order_data = Some ana_hist.a_order_data }

let analyse_history last_analysed_history_op ((_,_,hist,_):reduction) =
  match last_analysed_history_op with
  | None ->
      (* Corresponds to the case where there is no induction, no nested queries
         and no option ignoreAFewTimes *)
      None
  | Some last_analysed_history ->
      let rec sub_analyse hist =
        if hist == last_analysed_history.a_hist
        then last_analysed_history.a_order_data
        else
          match hist with
            | Any(i,hist') | HMaxHyp(i,hist') ->
                let ord_data_list' = sub_analyse hist' in
                Reduction_helper.remove_at i ord_data_list'
            | Removed(i_rm,i_dup,hist') ->
                (* We replace the duplicated ordering function with the intersection of the
                   duplicated ordering function and removed ordering function *)
                let ord_data_list1 = sub_analyse hist' in
                let (ord_fun_rm,nounif_sel_rm) = List.nth ord_data_list1 i_rm
                and (ord_fun_dup,nounif_sel_dup) = List.nth ord_data_list1 i_dup in
                let new_ord_fun = inter_ordering_fun ord_fun_rm ord_fun_dup in
                let new_nounif_sel = min nounif_sel_rm nounif_sel_dup in
                let ord_data_list2 = Reduction_helper.replace_at i_dup (new_ord_fun,new_nounif_sel) ord_data_list1 in
                Reduction_helper.remove_at i_rm ord_data_list2
            | HEquation(_,_,_,hist')
            | HCaseDistinction(_,_,_,_,hist') -> sub_analyse hist'
            | Resolution(hist1,n,hist2) ->
                let ord_data_list1 = sub_analyse hist2 in
                let (ord_fun,nounif_sel) = List.nth ord_data_list1 n in
                begin match hist1 with
                  | Rule(-1,Elem _,hyp,_,_)
                  | Rule(_,LblEquiv,hyp,_,_) ->
                      let ord_data_hyp = List.map (fun _ -> ([],nounif_sel)) hyp in
                      replace_nth_list ord_data_hyp n ord_data_list1
                  | Rule(_,LblClause,[],_,_) ->
                      Reduction_helper.remove_at n ord_data_list1
                  | Rule(-1,Apply (_,p),hyp,_,_) ->
                      (* Corresponds to Data Hyp so p must be an attacker predicate. *)
                      let new_ord_fun =
                        if is_pred_to_prove p
                        then strict_ordering_function ord_fun
                        else ord_fun
                      in
                      let ord_data_hyp = List.map (fun _ -> (new_ord_fun,nounif_sel)) hyp in
                      replace_nth_list ord_data_hyp n ord_data_list1
                  | Rule(-1,Init,_,_,_) -> replace_nth_list [] n ord_data_list1
                  | _ -> Parsing_helper.internal_error "[rules.ml >> analyse_history] Unexpected history (1)."
                end
            | HLemma(_,_,_,([],_,_),hist') -> sub_analyse hist'
            | HLemma(_,hyp_m,_,(hyp,_,_),hist') ->
                let ord_data_list1 = sub_analyse hist' in
                let ord_fun_lem = generate_ordering_fun_from_lemma ord_data_list1 hyp_m in
                let ord_data_lem = List.map (fun fact -> create_ordered_fact ord_fun_lem fact, 0) hyp in
                ord_data_list1 @ ord_data_lem
            | _ -> Parsing_helper.internal_error "[rules.ml >> analyse_history] Unexpected history (2)."
      in

      Some { a_hist = hist; a_order_data = sub_analyse hist }

let analysed_history_op_of_ordered_rule = function
  | { order_data = None } -> None
  | { order_data = Some ord_data; rule = (_,_,hist,_) } ->
      Some { a_hist = hist; a_order_data = ord_data }

(*****************************************************************
        Set Equiv
******************************************************************)

(* Check that two facts are smaller for all instances *)

let rec get_vars_rep vlist = function
    Var v -> vlist := v :: (!vlist)
  | FunApp(_,l) ->
      List.iter (get_vars_rep vlist) l

let get_vars_rep_fact vlist = function
    Pred(p,l) -> List.iter (get_vars_rep vlist) l

(* [remove_first vlist v] removes the first occurrence of
   [v] in [vlist]. Raise [Not_found] when [v] does not occur in [vlist] *)

let remove_first vlist v =
  let rec remove_first_rec v = function
      [] -> raise Not_found
    | (v'::l) -> if v' == v then l else v' :: (remove_first_rec v l)
  in
  vlist := remove_first_rec v (!vlist)

let is_smaller f1 f2 =
  (Terms.fact_size f1 < Terms.fact_size f2) &&
  (let v1 = ref [] in
  let v2 = ref [] in
  get_vars_rep_fact v1 f1;
  get_vars_rep_fact v2 f2;
  try
    List.iter (remove_first v2) (!v1);
    true
  with Not_found ->
    false)

let equiv_set = ref ([]: (fact list * fact * int) list)

let check_equiv (hyp, concl, n) =
  (* Check that \sigma h smaller than \sigma concl for all \sigma, for all h in hyp.
     This implies termination of the replacement process *)
  if not (List.for_all (fun h -> is_smaller h concl) hyp) then
    Parsing_helper.user_error "For equivalences, the conclusion must be larger than the hypotheses\nand this must be true for all instances of these facts.";
  (* Check that only ONE replacement rule applies to a given fact.
     This implies confluence of the replacement process *)
  List.iter (fun (_, concl',_) ->
    try
      Terms.auto_cleanup (fun () -> Terms.unify_facts concl concl');
      Parsing_helper.user_error "Conflict between equivalences: two of them apply to the same fact.";
    with Unify -> ()
        ) (!equiv_set);
  match concl with
    Pred(p,((FunApp(f,_) :: _) as l)) when
         p.p_prop land Param.pred_TUPLE != 0 &&
           f.f_cat = Tuple ->
     begin
       try
         let _ = reorganize_fun_app f l in
         Parsing_helper.user_error "Conflict between an equivalence and the decomposition of data constructors:\nan equivalence applies to a fact which is also decomposable by data constructors."
       with Not_found -> ()
     end
  | _ -> ()

let set_equiv set =
  (* Verify that the rules are ok *)
  List.iter check_equiv set;
  (* Store the replacement rules *)
  equiv_set := set

(*****************************************************************
        Limiting the depth of terms and number of hypotheses to
                        enforce termination. Disabled in sound mode.

        The limit function replace subterm with depth egal to
        Param.max_deph by fresh variable.
        Furthermore, the rule can have a limited number of hypothesis,
        depending of Param.max_hyp.
******************************************************************)

(* Limiting the induction size *)

let rec cancel_induction restwork vl hyp hist n = match hyp with
  | [] -> restwork hyp hist
  | pred::q_hyp  when List.exists (fun v -> occurs_var_fact v pred) vl ->
      cancel_induction (fun hyp1 hist1 ->
        restwork hyp1 (HMaxHyp(n,hist1))
      ) vl q_hyp hist (n+1)
  | pred::q_hyp ->
      cancel_induction (fun hyp1 hist1 ->
        restwork (pred::hyp1) hist1
      ) vl q_hyp hist (n+1)

let limit_induction f_next f_next_again ((hyp,concl,hist,constra) as r) =
  if !sound_mode
  then f_next r
  else
    try
      Selfun.find_inductive_variable_to_remove (fun vl ->
        cancel_induction (fun hyp1 hist1 ->
          TermsEq.simplify_constraints_rule f_next f_next_again (hyp1,concl,hist1,constra)
        ) vl hyp hist 0
      ) r
    with Not_found -> f_next r

let rec limit_depth n t =
   if n = 0 then
      Terms.new_var_def_term (Terms.get_term_type t)
   else
      match t with
      | Var v -> t
      | FunApp(f,l) -> FunApp(f, List.map (limit_depth (n-1)) l)

let limit_depth_occ n = function
  | FunApp(f,args) -> FunApp(f,List.map (limit_depth n) args)
  | _ -> Parsing_helper.internal_error "[Rules.ml >> limit_depth_occ] Should be a name."

let limit_depth_fact n = function
  | Pred(chann,[t;tocc]) when chann == Param.inj_event_pred_block ->
     (* We do not want that the occurrence name be replaced with a variable. *)
     Pred(chann,[limit_depth n t; limit_depth_occ n tocc])
  | Pred(chann,t) -> Pred(chann, List.map (limit_depth n) t)

let rec max_length n = function
    [] -> []
  | (a::l) -> if n = 0 then [] else a::(max_length (n-1) l)

let limit_length_constraints n c =
  {
    is_nat = max_length n c.is_nat;
    neq = List.map (max_length n) (max_length n c.neq);
    is_not_nat = max_length n c.is_not_nat;
    geq = max_length n c.geq
  }

let rec cancel_history n maxn h =
  if maxn <= n then h else
  cancel_history n (maxn-1) (HMaxHyp(n,h))

let limit_depth_rule r =
  if !sound_mode then r else
  let r =
    let max_hyp = !Param.max_hyp in
    if max_hyp < 0 then r else
    let (hyp, concl, hist,constra) = r in
    (* remove some hypotheses/constraints if they are too numerous
       Adjust the history hist accordingly *)
    (max_length max_hyp hyp, concl,
     cancel_history max_hyp (List.length hyp) hist,
     limit_length_constraints max_hyp constra)
  in
   let max_depth = ! Param.max_depth in
   if max_depth < 0 then r else
   let (hyp, concl, hist,constra) = r in
   (List.map (limit_depth_fact max_depth) hyp,
    limit_depth_fact max_depth concl, hist,
    Terms.map_constraints (limit_depth max_depth) constra)

(******************************************************************
        Decompose tuples and data constructors in hypotheses of rules.
        It is important for the correctness of this optimization that
        p:x is never selected when p is a predicate on which we
        perform the decomposition of data constructors, except
        when there are only such facts in the clause.

        Also eliminates duplicate hypotheses.
******************************************************************)

let hist_is_exempt_from_data_simplify h =
  match h with
  | Rule (_,Apply(f,_),_,_,_) -> Terms.is_data_or_proj f
  | Rule (_,LblEquiv,_,_,_) -> true
  | _ -> false

let rec pos_in_list init f = function
    [] -> -1
  | (a::l) -> if f a then init else pos_in_list (init+1) f l

let rec decompose_hyp_rec accu hypl =
  List.fold_right (fun hyp1 (hypl,nl,histl) ->
    let default() =
      let count = pos_in_list (nl+1) (equal_facts hyp1) hypl in
      if count >= 0 then
        (hypl, nl-1, Removed(nl, count, histl))
      else
        (hyp1::hypl, nl-1, histl)
    in
    match hyp1 with
      | Pred(chann,_) when chann == Param.event_pred_block || chann == Param.inj_event_pred_block || chann == Param.event2_pred_block -> default ()
      | Pred(chann,l0) ->
        let rec try_equiv_set = function
            [] ->
              if chann.p_prop land Param.pred_TUPLE != 0 then
                try
                  match l0 with
                    (FunApp(f,_) :: _) when f.f_cat = Tuple ->
                      let l = reorganize_fun_app f l0 in
                      begin match History.get_rule_hist (RApplyFunc(f,chann)) with
                        | Rule(_, _, hyp, _, _) as hist_dec ->
                            decompose_hyp_rec (hypl, nl+(List.length l)-1, (Resolution(hist_dec, nl, histl)))
                              (List.map2 (fun (Pred(p',_)) x -> Pred(p', x)) hyp l)
                        | _ -> Parsing_helper.internal_error "[rules.ml >> decompose_hyp_rec] Unexpected history."
                      end
                  | _ -> default()
                with Not_found -> default()
              else default()
          | (hypeq, concleq, neq)::l ->
              try
                let hypeq' =
                  Terms.auto_cleanup (fun () ->
                    Terms.match_facts concleq hyp1;
                    List.map copy_fact3 hypeq)
                in
                let hist_dec = Rule(neq, LblEquiv, hypeq, concleq, true_constraints) in
                decompose_hyp_rec (hypl, nl+(List.length hypeq')-1, (Resolution(hist_dec, nl, histl))) hypeq'
              with NoMatch ->
                try_equiv_set l
        in
        try_equiv_set (!equiv_set)
      ) hypl accu

let decompose_hyp_tuples ((hypl, concl, hist, constra) as rule) =
  if hist_is_exempt_from_data_simplify hist then
    rule
  else
   let (hypl', nl', histl') =
     decompose_hyp_rec ([], (List.length hypl)-1, hist) hypl
   in
   (hypl', concl, histl',constra)

(**********************************************************************
        Eliminate hypotheses p(x1...xn) where p has been declared "elimVar"
        or "elimVarStrict" and x1...xn do not occur elsewhere.
        Such a declaration means that p(x...x) is true for some value of x.
        This is correct in particular when p = attacker. When p is declared
        elimVar and we are not in sound_mode, x1...xn are allowed to occur
        in inequalities.

        In sound_mode, we always require that x1...xn do not occur in
        inequalities.
***********************************************************************)

let fold_right_prev3 f l_vars l_hyp acc =
  let rec fold_aux prev_vars l_vars l_hyp = match l_vars, l_hyp with
    | [],[] -> acc
    | vars::q_vars, t::q ->
        let acc' = fold_aux (vars::prev_vars) q_vars q in
        f prev_vars vars q_vars t acc'
    | _ -> Parsing_helper.internal_error "[rules.ml >> fold_right_prev] Lists should be of same size"
  in
  fold_aux [] l_vars l_hyp

let elim_any_x_condition chann l concl_vars prev_vars next_vars constra_vars =
  (
    chann.p_prop land Param.pred_ANY != 0 &&
    (* We first check that all terms are variables *)
    List.for_all (function Var _ -> true | _ -> false) l &&
    (* We now check the occurrences (costly) *)
    List.for_all (function
      | Var v ->
          not (
            (!sound_mode && List.memq v constra_vars) ||
            List.memq v concl_vars ||
            List.exists (List.memq v) next_vars ||
            List.exists (List.memq v) prev_vars
          )
      | _ -> false
    ) l
  )
  ||
  (
    chann.p_prop land Param.pred_ANY_STRICT != 0 &&
    (* We first check that all terms are variables *)
    List.for_all (function Var _ -> true | _ -> false) l &&
    (* We now check the occurrences (costly) *)
    List.for_all (function
      | Var v ->
          not (
            List.memq v constra_vars ||
            List.memq v concl_vars ||
            List.exists (List.memq v) next_vars ||
            List.exists (List.memq v) prev_vars
          )
      | _ -> false) l
  )

let elim_any_x_all (hypl', concl, histl', constra) =

  (* We retrieve the variables of each fact and of constraints, to avoid recomputing
     them later in the function List.find. *)

  let concl_vars = Terms.get_vars_fact_nolink concl in
  let hypl_vars = List.map (Terms.get_vars_fact_nolink) hypl' in
  let constra_vars = Terms.get_vars_constra_nolink constra in

  let (hypl'', _, histl'') =
    (* [prev_vars] is the list of variable lists of the hypotheses before [hyp1] in [hypl']
       [next_vars] is the list of variable lists of the hypotheses after [hyp1] in [hypl']
       [curr_vars] is the list of variable in [hyp1].
    *)
    fold_right_prev3 (fun prev_vars curr_vars next_vars hyp1 (hypl, nl, histl) -> match hyp1 with
      | Pred(chann, l) ->
          begin
            try
              let (n, ff) =
                List.find (fun (_, ff) ->
                  try
                    Terms.auto_cleanup (fun () ->
                      Terms.unify_facts ff hyp1;
                      (* check that all modified variables of hyp1 do not
                         occur in the rest of R including inequalities *)
                      List.iter (function
                        | { link = NoLink; _ } -> ()
                        | v ->
                            if
                              List.memq v constra_vars ||
                              List.memq v concl_vars ||
                              List.exists (List.memq v) next_vars ||
                              List.exists (List.memq v) prev_vars
                            then raise Unify
                      ) curr_vars;
                      (* all checks successful *)
                      true
                    )
                  with Unify -> false
                ) !elimtrue_set
              in
              (hypl, nl-1, (Resolution(Rule(n, LblClause, [], ff, true_constraints), nl, histl)))
            with Not_found ->
              if elim_any_x_condition chann l concl_vars prev_vars next_vars constra_vars
              then (hypl, nl-1, (Any(nl, histl)))
              else (hyp1 :: hypl, nl-1, histl)
          end
    ) hypl_vars hypl' ([], (List.length hypl')-1, histl')
  in
  (hypl'', concl, histl'',constra)

let elim_any_x_empty_elim_set (hypl', concl, histl', constra) =
  if
    (* We apply a first test to avoid computing the variables of the clauses when not necessary *)
    List.exists (function
      | Pred(chann,l) ->
          ((chann.p_prop land Param.pred_ANY != 0) || (chann.p_prop land Param.pred_ANY_STRICT != 0)) &&
          List.for_all (function Var v -> true | _ -> false) l
    ) hypl'
  then
    let concl_vars = Terms.get_vars_fact_nolink concl in
    let hypl_vars = List.map (Terms.get_vars_fact_nolink) hypl' in
    let constra_vars = Terms.get_vars_constra_nolink constra in

    let (hypl'', _, histl'') =
      fold_right_prev3 (fun prev_vars _ next_vars hyp1 (hypl, nl, histl) -> match hyp1 with
        | Pred(chann, l) ->
            if elim_any_x_condition chann l concl_vars prev_vars next_vars constra_vars
            then (hypl, nl-1, (Any(nl, histl)))
            else (hyp1 :: hypl, nl-1, histl)
      ) hypl_vars hypl' ([], (List.length hypl')-1, histl')
    in
    (hypl'', concl, histl'',constra)
  else (hypl',concl,histl',constra)

let elim_any_x r =
  if !elimtrue_set = []
  then elim_any_x_empty_elim_set r
  else elim_any_x_all r

(**********************************************
Subsumption test between rules:
H -> F (C) => H' -> F' (C') iff exists \sigma,
   \sigma H \subseteq H', \sigma F = F', C' => sigma C

This section consists of:
   1- Matching between hypotheses
   2- Reordering of the hypothesis
   3- Final function : [implies rule1 rule2]
***********************************************)

(* 1. Matching between hypotheses. Try all possible orderings
      of the hypotheses *)

(**Test \sigma H \subseteq H' for multiset inclusion *)
let rec match_fact_with_hyp nextf fact1 hyp2 passed_hyp =
  match hyp2 with
  | [] -> raise NoMatch
  | (fact2::fact_l) ->
      try
        Terms.auto_cleanup (fun () ->
          Terms.match_facts fact1 fact2;
          nextf (passed_hyp @ fact_l)
        )
      with NoMatch ->
        match_fact_with_hyp nextf fact1 fact_l (fact2 :: passed_hyp)

let rec match_hyp nextf hyp1 hyp2 =
  match hyp1 with
  | [] -> nextf ()
  | (fact1 :: fact_l1) ->
      match_fact_with_hyp
        (match_hyp nextf fact_l1) fact1 hyp2 []

let match_hyp_implies = match_hyp

let rec match_fact_with_hyp_ordered nextf fact1 ord1 ord_hyp2 passed_hyp =
  match ord_hyp2 with
  | [] -> raise NoMatch
  | ((fact2,(ord2,_)) as ord_fact2) :: fact_l ->
      try
        Terms.auto_cleanup (fun () ->
          Terms.match_facts fact1 fact2;
          Database.implies_ordering_function ord1 ord2;
          nextf (passed_hyp @ fact_l)
        )
      with NoMatch ->
        match_fact_with_hyp_ordered nextf fact1 ord1 fact_l (ord_fact2 :: passed_hyp)

let rec match_hyp_ordered nextf ord_hyp1 ord_hyp2 =
  match ord_hyp1 with
  | [] -> nextf ()
  | (fact1,(ord1,_)) :: fact_l1 ->
      match_fact_with_hyp_ordered
        (match_hyp_ordered nextf fact_l1) fact1 ord1 ord_hyp2 []

let match_hyp_ordered_implies = match_hyp_ordered

(* 2. Try to reorder hypotheses to speed up the subsumption test.
      Put first constant hypotheses (no unbound variable. They
      can contain variables already bound by matching the conclusion.)
      Then put other hypotheses in decreasing size order. *)

let rec has_unbound_var = function
    Var v ->
      begin
        match v.link with
          NoLink -> true
        | TLink _ -> false
        | VLink _ -> false
        | _ -> internal_error "unexpected link in has_unbound_var"
      end
  | FunApp(_,l) -> List.exists has_unbound_var l

let fact_has_unbound_var = function
    Pred(_, tl) -> List.exists has_unbound_var tl

let rank f =
  if fact_has_unbound_var f then
    fact_size f
  else
    1000000 (* Something probably bigger than all sizes of terms *)

let rank_compare (_,r1) (_,r2) = r2 - r1

let reorder hyp =
  if List.length hyp > 4 then
    let hyp_rank = List.map (fun f -> (f, rank f)) hyp in
    let hyp_sorted = List.sort rank_compare hyp_rank in
    List.map (fun (f,_) -> f) hyp_sorted
  else
    hyp

let reorder_and_split hyp =
  let bound_hyp = ref [] in
  let unbound_hyp = ref [] in

  List.iter (fun f ->
    if fact_has_unbound_var f
    then unbound_hyp := (f,fact_size f) :: !unbound_hyp
    else bound_hyp := f :: !bound_hyp
  ) hyp;

  let hyp_sorted = List.sort rank_compare !unbound_hyp in
  List.map (fun (f,_) -> f) hyp_sorted, !bound_hyp

let reorder_ordered hyp =
  if List.length hyp > 4 then
    let hyp_rank = List.map (fun f -> (f, rank (fst f))) hyp in
    let hyp_sorted = List.sort rank_compare hyp_rank in
    List.map (fun (f,_) -> f) hyp_sorted
  else
    hyp

let reorder_and_split_ordered hyp =
  let bound_hyp = ref [] in
  let unbound_hyp = ref [] in

  List.iter (fun ((f,_) as f_ord) ->
    if fact_has_unbound_var f
    then unbound_hyp := (f_ord,fact_size f) :: !unbound_hyp
    else bound_hyp := f_ord :: !bound_hyp
  ) hyp;

  let hyp_sorted = List.sort rank_compare !unbound_hyp in
  List.map (fun (f,_) -> f) hyp_sorted, !bound_hyp

(* Several simplification functions for rules *)

(* 1. Simplify the constraints *)

let simplify_rule_constra = TermsEq.simplify_constraints_rule

(* 2. eliminate rules that have in hypothesis a "not" fact
      (secrecy assumption) *)

let elim_not next_stage ((hyp', _, _,_) as r) =
  if (List.exists (fun h -> List.exists (matchafact (Terms.unblock_predicate_fact h)) (!not_set)) hyp') then
    ()
  else
    next_stage r

let elim_not_solving apply_not next_stage ((hyp', _, _,_) as r) =
  if apply_not && (List.exists (fun h -> List.exists (matchafact (Terms.unblock_predicate_fact h)) (!not_set)) hyp') then
    ()
  else
    next_stage r

(* 3. eliminate tautologies (rules that conclude a fact already in their
      hypothesis) *)

let elim_taut next_stage ((hyp', concl, _,_) as r) = 
  if List.exists (equal_facts concl) hyp' then
    ()
  else
    next_stage r

(* 4. eliminate hypotheses p(x1...xn) where p has been declared "elimVar"
   or "elimVarStrict" and x1...xn do not occur elsewhere.
   Such a declaration means that p(x...x) is true for some value of x.
   This is correct in particular when p = attacker. When p is declared
   elimVar and we are not in sound_mode, x1...xn are allowed to occur
   in inequalities.

   In sound_mode, we always require that x1...xn do not occur in
   inequalities. *)

let elim_any_x2 next_stage r =
  next_stage (elim_any_x r)

(* 5. decompose tuples and data constructors in hypotheses.
   It is important for the correctness of this optimization that
   p:x is never selected when p is a predicate on which we
   perform the decomposition of data constructors, except
   when there are only such facts in the clause.

   Also eliminates duplicate hypotheses.
 *)

let decompose_hyp_tuples2 next_stage r =
  next_stage (decompose_hyp_tuples r)

(* 6. decompose tuples and data constructors in conclusion
   It is important for the correctness of this optimization that
   p:x is never selected when p is a predicate on which we
   perform the decomposition of data constructors. *)

let decompose_concl_tuples next_stage ((hyp', concl, hist', constra) as r) =
  if hist_is_exempt_from_data_simplify hist' then
    next_stage r
  else
    let put_clause first_fact hist =
      assert (!current_bound_vars == []);
      let r = (Terms.mapq_list copy_fact hyp', copy_fact first_fact, hist, copy_constra constra) in
      cleanup();
      next_stage r
    in
    let rec tuple_dec hist concl =
      match concl with
        Pred(chann, l0) ->
          let rec try_equiv_set = function
              [] ->
                if chann.p_prop land Param.pred_TUPLE != 0 then
                  match l0 with
                    FunApp(f,_) :: _ when f.f_cat = Tuple ->
                      let l = reorganize_fun_app f l0 in
                      List.iteri (fun n first ->
                        match History.get_rule_hist (RApplyProj(f, n, chann)) with
                          | Rule(_,_,_,Pred(p',_), _) as hist_dec ->
                              let concl' = Pred(p', first) in
                              let hist'' = Resolution(hist, 0, hist_dec) in
                              rec_call concl' hist''
                          | _ -> Parsing_helper.internal_error "[rules.ml >> decompose_concl_tuples] Unexpected history"
                        ) l
                  | _ -> raise Not_found
                else
                  raise Not_found
            | (hypeq, concleq, neq)::l ->
                try
                  let hypeq' =
                    Terms.auto_cleanup (fun () ->
                      Terms.match_facts concleq concl;
                      List.map copy_fact3 hypeq)
                  in
                  List.iteri (fun n concl' ->
                    let hist_dec = Rule(neq + n + 1, LblEquiv, [concleq], List.nth hypeq n, true_constraints) in
                    let hist'' = Resolution(hist, 0, hist_dec) in
                    rec_call concl' hist''
                        ) hypeq'
                with NoMatch ->
                  try_equiv_set l
          in
          try_equiv_set (!equiv_set)
    and rec_call concl hist =
      try
        tuple_dec hist concl
      with Not_found ->
        put_clause concl hist
    in
    begin
      try
        tuple_dec hist' concl
      with Not_found ->
        next_stage r
    end

(* 7. Element simplification
     att(x) /\ elem(M_1, x) /\ ... /\ elem(M_n, x)
   becomes
     att(M_1) /\ ... /\ att(M_n)
   when x does not occur elsewhere in the clause.

   "att" can be any predicate declared with data decomposition (pred_TUPLE).
   The predicate "elem" must be declared pred_ELEM.
   *)

let rec collect_preds v = function
    [] -> []
  | (f::l) ->
      match f with
        Pred(p, [Var v']) when p.p_prop land Param.pred_TUPLE != 0
            && v' == v ->
              p :: (collect_preds v l)
      | _ -> collect_preds v l

let rec transform_hyp preds v hist n = function
    [] -> ([], hist)
  | (f::l) ->
      match f with
        Pred(p, [t1; Var v']) when p.p_prop land Param.pred_ELEM != 0 && v == v' ->
          begin match History.get_rule_hist (RElem(preds, p)) with
            | Rule(_, _, hyp, _, _) as hist_dec ->
                let hist' = Resolution(hist_dec, n,  hist) in
                let (l', hist'') = transform_hyp preds v hist' (n + List.length preds) l in
                ((List.map (function
                    (Pred(p',_)) -> Pred(p', [t1])
                  ) hyp) @ l', hist'')
            | _ -> Parsing_helper.internal_error "[rules.ml >> transform_hyp] Unexpected history"
          end
      | _ ->
          let (l', hist') = transform_hyp preds v hist (n+1) l in
          (f :: l', hist')

let transform_rule v (hyp, concl, hist, constra) =
  let preds = collect_preds v hyp in
  let (hyp', hist') = transform_hyp preds v hist 0 hyp in
  (hyp', concl, hist', constra)

let check_occurs_fact p0 v = function
    Pred(p, [Var v']) when p.p_prop land Param.pred_TUPLE != 0
              && v == v' -> false
  | Pred(p, [t1; Var v']) when p.p_prop land Param.pred_ELEM != 0 && p == p0
              && v == v' -> occurs_var v t1
  | Pred(p, tl) -> List.exists (occurs_var v) tl

let check_occurs_concl v = function
  | Pred(p, tl) -> List.exists (occurs_var v) tl

let check_occurs_rule p0 v (hyp, concl, hist, constra) =
  List.exists (check_occurs_fact p0 v) hyp ||
  (check_occurs_concl v concl) ||
  exists_constraints (occurs_var v) constra

let rec elem_simplif next_stage repeat_next_stage ((hyp, concl, hist, constra) as r) =
  let rec find_optim seen_vars = function
      [] -> next_stage r
    | (f::l) ->
        match f with
          Pred(p,[t1;Var v]) when p.p_prop land Param.pred_ELEM != 0
              && not (List.memq v seen_vars) ->
                if check_occurs_rule p v r then
                  find_optim (v::seen_vars) l
                else
                  repeat_next_stage (transform_rule v r)
        | _ -> find_optim seen_vars l
  in
  find_optim [] hyp

(* 9. Eliminate redundant hypotheses
   When R = H /\ H' -> C, and there exists \sigma such that
   \sigma H \subseteq H' and \sigma does not modify variables
   of H' and C, then R can be replaced with R' = H' -> C.
   This is a generalization of elimination of duplicate hypotheses.
   The function below does not really remove redundant hypotheses,
   but transforms them into duplicate hypotheses, so that
   they will be removed by the elimination of duplicate hypotheses.
   (In particular, in the history, they are coded as duplicate hypotheses.)

   Redundant hypotheses appear in particular when there are
   begin facts. They can slow down the subsumption test
   considerably.

   Note: it is important that elim_redundant_hyp comes as last
   simplification. In particular, it should come after elimination
   of attacker(x) (so that we don't have many hypotheses attacker(x)
   remaining, which can be mapped to any hypothesis attacker(..) in
   the instantiated clause) and after simplification of inequalities
   (so that we don't have inequalities with variables not
   used elsewhere, which cause problems for the subsumption test).
 *)

let rec is_marked_term = function
  | Var { link = VLink _ ; _ } -> true
  | Var _ -> false
  | FunApp(_,args) -> List.for_all is_marked_term args

let is_marked_fact = function
  | Pred(_,args) -> List.for_all is_marked_term args

let rec mark_variables = function
  | Var v ->
      begin match v.link with
        | TLink _ -> raise NoMatch
        | VLink _ -> ()
        | NoLink -> link v (VLink v)
        | _ -> Parsing_helper.internal_error "[rules.ml >> mark_variables] Unexpected links"
      end
  | FunApp(f,args) -> List.iter mark_variables args

let mark_variables_fact = function
  | Pred(_,args) -> List.iter mark_variables args

let rec match_redundant_terms apply_mark t1 t2 = match t1, t2 with
  | Var v, Var v' when v == v' -> if apply_mark then mark_variables t2
  | Var v, _ ->
      begin match v.link with
        | NoLink ->
            if v.unfailing
            then
              begin
                link v (TLink t2);
                if apply_mark then mark_variables t2
              end
            else
              begin match t2 with
                | Var v' when v'.unfailing -> raise NoMatch
                | FunApp(f_symb,_) when f_symb.f_cat = Failure -> raise NoMatch
                | _ ->
                    link v (TLink t2);
                    if apply_mark then mark_variables t2
              end
        | TLink t' ->
            (* Variables of [t'] have already been marked. *)
            if not (equal_terms t' t2)
            then raise NoMatch
        | VLink _ ->
            (* Since the variable has been marked, it can't be used in the substitution.
               The only possible case is when t1 = t2 which is already covered. *)
            raise NoMatch
        | _ -> Parsing_helper.internal_error "[rules.ml >> mark_variables] Unexpected links"
      end
  | FunApp (f1,args1), FunApp (f2,args2) ->
      if f1 != f2 then raise NoMatch;
      List.iter2 (match_redundant_terms apply_mark) args1 args2
  | _,_ -> raise NoMatch

let match_redundant_facts apply_mark f1 f2 = match f1, f2 with
  | Pred(p1,t1), Pred(p2,t2) ->
      if p1 != p2 then raise NoMatch;
      List.iter2 (match_redundant_terms apply_mark) t1 t2

(* 9.a For non ordered clauses *)

let rec match_redundant_fact_with_kept_facts restwork fact1 = function
  | [] -> raise NoMatch
  | fact2 :: q2 ->
      try
        Terms.auto_cleanup (fun () ->
          match_redundant_facts false fact1 fact2;
          restwork ()
        )
      with NoMatch ->
        match_redundant_fact_with_kept_facts restwork fact1 q2

let rec match_redundant_fact_with_hyp restwork fact1 passed_hyp = function
  | [] -> raise NoMatch
  | fact2 :: q2 ->
      try
        Terms.auto_cleanup (fun () ->
          match_redundant_facts true fact1 fact2;

          (* At that point, we need to keep fact2 *)
          restwork fact2 (List.rev_append passed_hyp q2)
        )
      with NoMatch ->
        match_redundant_fact_with_hyp restwork fact1 (fact2::passed_hyp) q2

let rec match_redundant_hyp restwork kept_hyp = function
  | [] -> restwork ()
  | fact :: q ->
      (* We first test if [fact] only contains marked variables *)
      if is_marked_fact fact
      then match_redundant_hyp restwork (fact::kept_hyp) q
      else
        try
          (* We first try by matching [fact] and [kept_hyp] *)
          match_redundant_fact_with_kept_facts (fun () ->
            match_redundant_hyp restwork kept_hyp q
          ) fact kept_hyp
        with NoMatch ->
          (* Since we did not find a match with kept facts,
             we try with the rest of the facts. *)
          try
            match_redundant_fact_with_hyp (fun fact' passed_hyp ->
              match_redundant_hyp restwork (fact'::kept_hyp) passed_hyp
            ) fact [] q
          with NoMatch ->
            (* No match was found hence [fact] must be kept and we mark it. *)
            mark_variables_fact fact;
            match_redundant_hyp restwork (fact::kept_hyp) q

let elim_redundant_hyp next_stage repeat_next_stage ((hyp,concl,hist,constra) as r) =
  if (!Param.redundant_hyp_elim) &&
    ((not (!Param.redundant_hyp_elim_begin_only)) ||
     (List.exists (function
         Pred({p_info = TestUnifP _}, _) -> false
       | Pred(p,_) -> p.p_prop land Param.pred_BLOCKING != 0
      ) hyp))
  then
    try
      Terms.auto_cleanup (fun () ->
        (* We first gather the variables of the clause *)
        let vars = ref [] in
        Terms.get_vars_fact vars concl;
        List.iter (Terms.get_vars_fact vars) hyp;

        (* We mark the variables of the conclusion *)
        mark_variables_fact concl;

        (* We look for a matching *)
        let (unbound_hyp,bound_hyp) = reorder_and_split hyp in
        (* The facts in [bound_hyp] do not have unbound variables, meaning that all
           variables have been marked when executing [mark_variables_fact concl].
           They are therefore necessarily kept in [match_redundant_hyp]. *)
        match_redundant_hyp (fun () ->
          (* We check whether some match was found *)
          let success = List.exists (fun v -> match v.link with TLink _ -> true | _ -> false) !vars in

          if success
          then
            begin
              (* It remains to check the disequalities and inequalities *)

              (* We first save the links and remove the VLink *)
              let saved_links =
                List.map (fun v ->
                  let v_link = v.link in
                  begin match v_link with
                    | VLink _ -> v.link <- NoLink
                    | _ -> ()
                  end;
                  (v,v_link)
                ) !vars
              in

              (* We first copy the constraints without renaming variables. *)
              let constra_inst = copy_constra3 constra in

              (* We now remove the all the links *)
              List.iter (fun v -> v.link <- NoLink) !vars;

              (* We compare *)
              try
                (* We check the implication of constraints. *)
                TermsEq.implies_constraints_keepvars (concl::hyp) constra constra_inst;

                (* We found a proper matching so we restore the TLink, copy the rule and run next_stage *)
                List.iter (function (v,TLink t) -> v.link <- TLink t | (v,_) -> v.link <- NoLink) saved_links;

                let rule' = copy_rule2 (hyp,concl,hist,constra_inst) in

                Terms.auto_cleanup (fun () -> repeat_next_stage rule');

                List.iter (fun (v,link) -> v.link <- link) saved_links;
              with NoMatch ->
                (* Restore link and raise Nomatch *)
                List.iter (fun (v,link) -> v.link <- link) saved_links;
                raise NoMatch
            end
          else raise NoMatch
        ) bound_hyp unbound_hyp
      )
    with NoMatch -> next_stage r
  else next_stage r

(* 9.b For ordered clauses *)

let match_redundant_facts_ordered apply_mark (fact1, (ord1,_)) (fact2, (ord2,_)) =
  match_redundant_facts apply_mark fact1 fact2;
  if not (Terms.equal_facts fact1 fact2)
  then Database.implies_ordering_function ord1 ord2

let rec match_redundant_fact_with_kept_facts_ordered restwork fact1 = function
  | [] -> raise NoMatch
  | fact2 :: q2 ->
      try
        Terms.auto_cleanup (fun () ->
          match_redundant_facts_ordered false fact1 fact2;
          restwork ()
        )
      with NoMatch ->
        match_redundant_fact_with_kept_facts_ordered restwork fact1 q2

let rec match_redundant_fact_with_hyp_ordered restwork fact1 passed_hyp = function
  | [] -> raise NoMatch
  | fact2 :: q2 ->
      try
        Terms.auto_cleanup (fun () ->
          match_redundant_facts_ordered true fact1 fact2;
          (* At that point, we need to keep fact2 *)
          restwork fact2 (List.rev_append passed_hyp q2)
        )
      with NoMatch ->
        match_redundant_fact_with_hyp_ordered restwork fact1 (fact2::passed_hyp) q2

let rec match_redundant_hyp_ordered restwork kept_hyp = function
  | [] -> restwork ()
  | ((fact,_) as o_fact) :: q ->
      (* We first test if fact only contain marked variables *)
      if is_marked_fact fact
      then match_redundant_hyp_ordered restwork (o_fact::kept_hyp) q
      else
        try
          (* We first try by matching fact and kept_hyp *)
          match_redundant_fact_with_kept_facts_ordered (fun () ->
            match_redundant_hyp_ordered restwork kept_hyp q
          ) o_fact kept_hyp
        with NoMatch ->
          (* Since we did not find a match with kept facts,
             we try with the rest of the facts. *)
          try
            match_redundant_fact_with_hyp_ordered (fun o_fact' passed_hyp ->
              match_redundant_hyp_ordered restwork (o_fact'::kept_hyp) passed_hyp
            ) o_fact [] q
          with NoMatch ->
            (* No match was found hence [fact] must be kept and we mark it. *)
            mark_variables_fact fact;
            match_redundant_hyp_ordered restwork (o_fact::kept_hyp) q

let elim_redundant_hyp_ordered next_stage repeat_next_stage ahist_op ((hyp, concl, hist, constra) as rule) =
  match ahist_op with
  | None -> elim_redundant_hyp next_stage repeat_next_stage rule
  | Some ana_hist ->
      if (!Param.redundant_hyp_elim) &&
       ((not (!Param.redundant_hyp_elim_begin_only)) ||
        (List.exists (function
            Pred({p_info = TestUnifP _}, _) -> false
          | Pred(p,_) -> p.p_prop land Param.pred_BLOCKING != 0
         ) hyp))
      then
        try
          Terms.auto_cleanup (fun () ->
            (* We first gather the variables of the clause *)
            let vars = ref [] in
            Terms.get_vars_fact vars concl;
            List.iter (Terms.get_vars_fact vars) hyp;

            (* We mark the variables of the conclusion *)
            mark_variables_fact concl;

            let ord_hyp = List.combine hyp ana_hist.a_order_data in

            (* We look for a matching *)
            let (unbound_hyp,bound_hyp) = reorder_and_split_ordered ord_hyp in
            (* The facts in [bound_hyp] do not have unbound variables, meaning that all
               variables have been marked when executing [mark_variables_fact concl].
               They are therefore necessarily kept in [match_redundant_hyp]. *)
            match_redundant_hyp_ordered (fun () ->
              (* We check whether some match was found *)
              let success = List.exists (fun v -> match v.link with TLink _ -> true | _ -> false) !vars in

              if success
              then
                begin
                  (* It remains to check the disequalities and inequalities *)

                  (* We first save the links and remove the VLink *)
                  let saved_links =
                    List.map (fun v ->
                      let v_link = v.link in
                      begin match v_link with
                        | VLink _ -> v.link <- NoLink
                        | _ -> ()
                      end;
                      (v,v_link)
                    ) !vars
                  in

                  (* We first copy the constraints without renaming variables. *)
                  let constra_inst = copy_constra3 constra in

                  (* We now remove the all the links *)
                  List.iter (fun v -> v.link <- NoLink) !vars;

                  (* We compare *)
                  try
                    (* We check the implication of constraints. *)
                    TermsEq.implies_constraints_keepvars (concl::hyp) constra constra_inst;

                    (* We found a proper matching so we restore the TLink, copy the rule and run next_stage *)
                    List.iter (function (v,TLink t) -> v.link <- TLink t | (v,_) -> v.link <- NoLink) saved_links;

                    let rule' = copy_rule2 (hyp,concl,hist,constra_inst) in

                    Terms.auto_cleanup (fun () -> repeat_next_stage rule');

                    List.iter (fun (v,link) -> v.link <- link) saved_links;
                  with NoMatch ->
                    (* Restore link and raise Nomatch *)
                    List.iter (fun (v,link) -> v.link <- link) saved_links;
                    raise NoMatch
                end
              else raise NoMatch
            ) bound_hyp unbound_hyp
          )
        with NoMatch -> next_stage rule
      else next_stage rule

(* 10. Simplification using the equational theory *)

let simp_eq_rule next_stage ((hypl, concl, _, _) as rule) =
  if TermsEq.hasConvergentEquations ()
  then
    try
      Terms.auto_cleanup (fun () ->
        List.iter (function Pred(p,l) ->
          if (!Param.simpeq_all_predicates) ||
             (p.p_prop land Param.pred_SIMPEQ != 0)
          then List.iter TermsEq.simp_eq l
              ) (concl::hypl)
          );
      next_stage rule
    with TermsEq.Reduces ->
      () (* Remove the clause when a term reduces. *)
  else
    next_stage rule

(* 11. Simplification using lemmas *)

let get_option_lemma in_solving lem =
  if in_solving
  then lem.l_verif_app
  else lem.l_sat_app

let rec extract_selected_fact index = function
  | [] -> Parsing_helper.internal_error "[rules.ml >> extract_selected_fact] Index should corresponds to an element of the list of facts."
  | f::q when index = 0 -> f, q
  | f::q ->
      let (f_sel,hyp) = extract_selected_fact (index-1) q in
      (f_sel,f::hyp)

(* Transform the injective event into an event *)
let event_of_inj_event = function
  | Pred(p,[t;_]) when p == Param.inj_event_pred -> Pred(Param.event_pred,[t])
  | Pred(p,[t;_]) when p == Param.inj_event_pred_block -> Pred(Param.event_pred_block,[t])
  | pred -> pred

let to_block_non_inj_event = function
  | Pred(p,[t;_]) when p == Param.inj_event_pred || p == Param.inj_event_pred_block -> Pred(Param.event_pred_block,[t])
  | Pred(p,args) when p == Param.event_pred -> Pred(Param.event_pred_block,args)
  | Pred(p,args) when p == Param.event2_pred -> Pred(Param.event2_pred_block,args)
  | fact -> fact

let are_facts_syntactically_unifiable fact1 fact2 =
  try
    Terms.auto_cleanup (fun () ->
      Terms.unify_facts fact1 fact2;
      true
    )
  with Unify -> false

let display_ordering_function ord_fun =
  Printf.printf "{";
  Display.Text.display_list (function
    | (n,Less) -> Printf.printf "%d -> <" n
    | (n,Leq) -> Printf.printf "%d -> <=" n
  ) "; " ord_fun;
  Printf.printf "}"

(* In the following function,
  - [n_idx] is the index predicate of the conclusion
  - [n] is the number of facts in the conclusion (>= 1)
  - [m_idx] is the index predicate of the lemma
  - [m] is the number of facts in the premise of the lemma (>= 1)
  - [order_fun_list] is the list of ordering function extracted by the matching
    between the lemma and the ordered clauses. The list must be order so that it
    matches the order of the premise of the lemma, i.e. the i-th element of the list
    is the ordering function for the i-th fact in the premise of the lemma.

    The size of [order_fun_list] must be equal to [m]
*)
let are_ordering_fun_strict (n_idx,n) (m_idx,m) (order_fun_list:ordering_function list) =

  let all_strict na nb ord_fun_l =
    List.for_all (List.exists (function (i,Less) when na <= i && i <= nb -> true | _ -> false)) ord_fun_l
  in

  let distinct_pairwise_leq_ordering na nb ord_fun_l =
    (* We check that each matched hypothesis are pairwise less or equal to one of a premise of the query. *)
    let rec all_distinct accu = function
      | [] -> true
      | ord_fun::q -> all_distinct_one accu q ord_fun

    and all_distinct_one accu rest = function
      | [] -> false
      | (n,_)::q ->
          if n < na || n > nb || List.mem n accu
          then all_distinct_one accu rest q
          else
            if all_distinct (n::accu) rest
            then true
            else all_distinct_one accu rest q
    in

    all_distinct [] ord_fun_l
  in

  let distinct_pairwise_leq_with_one_less_ordering na nb ord_fun_l =
    (* We check that each matched hypothesis are pairwise less or equal to one of a premise of the query and at least one is strictly less.
      When we managed to find a matching that is equal but not strict, we record it in found_equal.
    *)
    let rec all_distinct one_less accu = function
      | [] -> one_less
      | ord_fun::q -> all_distinct_one one_less accu q ord_fun

    and all_distinct_one one_less accu rest = function
      | [] -> false
      | (n,order)::q ->
          if n < na || n > nb || List.mem n accu
          then all_distinct_one one_less accu rest q
          else
            if all_distinct (one_less || order = Less) (n::accu) rest
            then true
            else all_distinct_one one_less accu rest q
    in
    all_distinct false [] ord_fun_l
  in

  let equal_ordering na nb m ord_fun_l =
    m <= nb - na + 1 && (distinct_pairwise_leq_ordering na nb ord_fun_l)
  in

  let strict_ordering na nb m ord_fun_l =
    na <= nb && (
      all_strict na nb ord_fun_l ||
      (m <= nb - na && distinct_pairwise_leq_ordering na nb ord_fun_l) ||
      (m > nb - na && distinct_pairwise_leq_with_one_less_ordering na nb ord_fun_l)
    )
  in

  let (ord_fun_l,ord_fun_pred_l) = Terms.split_list (m_idx-1) order_fun_list in

  (strict_ordering 1 (n_idx-1) (m_idx-1) ord_fun_l) ||
  (equal_ordering 1 (n_idx-1) (m_idx-1) ord_fun_l && strict_ordering n_idx n (m - m_idx + 1) ord_fun_pred_l)

(* let are_ordering_fun_strict (n_idx,n) (m_idx,m) (order_fun_list:ordering_function list) =
  Printf.printf "*** are_ordering_fun_strict:\n";
  Printf.printf "- (n_idx,n) = (%d,%d)\n" n_idx n;
  Printf.printf "- (m_idx,m) = (%d,%d)" m_idx m;
  Display.Text.display_item_list display_ordering_function order_fun_list;
  let r = are_ordering_fun_strict (n_idx,n) (m_idx,m) order_fun_list in
  Printf.printf "- Result = %b\n\n" r;
  r *)

let verify_application_condition last_analysed_hist (n_idx_opt,n) (m_idx,m) matched_facts ((_,concl,_,_) as rule) lemma_concl induction in_solving =
  if in_solving
  then
    if induction
    then
      (* We need to check that the ordering function are n-strict. *)
      let last_analysed_hist' = analyse_history last_analysed_hist rule in
      let order_data = get_order_data_from_analyed_history_op last_analysed_hist' in
      let order_funs =
        List.map (fun (i,_) ->
          if i < 0
          then [-i,Leq]
          else fst (List.nth order_data i)
        ) matched_facts
      in
      match n_idx_opt with
        | Some n_idx ->
            (are_ordering_fun_strict (n_idx,n) (m_idx,m) order_funs,last_analysed_hist')
        | None -> Parsing_helper.internal_error "[rules.ml >> verify_application_condition] Expected an index predicate for the conclusion of the ordered rule."
    else
      (* No additional condition to verify *)
      (true,last_analysed_hist)
  else
    (* During the saturation procedure *)
    if induction
    then
      (* No additional condition. We assume here that the matching did not use
         the conclusion: Should be guaranteed by [match_and_apply_lemma] *)
      (true,last_analysed_hist)
    else
      (* We need to check that if the conclusion of the clause was used then all
         events in conclusion of the lemma are not unifiable with the conclusion
         of the clause *)
      match concl with
        | Pred(p,args) when not (Terms.is_user_defined p) ->
            if List.exists (fun (i,_) -> i = -1) matched_facts
            then
	      let block_concl = to_block_non_inj_event concl in
              let exists_unif =
                List.exists (fun (f_list,_,_) ->
                  List.exists (fun fact ->
                    are_facts_syntactically_unifiable (to_block_non_inj_event fact) block_concl
                  ) f_list
                ) lemma_concl
              in
              (not exists_unif,last_analysed_hist)
            else (true,last_analysed_hist)
        | _ ->
            (* Only standard predicates need to be ordered. *)
            (true,last_analysed_hist)

(* let verify_application_condition last_analysed_hist (n_idx_opt,n) (m_idx,m) matched_facts ((_,concl,_,_) as rule) lemma_concl induction in_solving =
  Printf.printf "*** Verify Application Condition:\n"; *)


(* In this function, we instantiate in priority existential variables from lemma. *)
let rec unify_for_lemma priority_vars t1 t2 = match (t1,t2) with
    (Var v, Var v') when v == v' -> ()
  | (Var v, _) ->
      begin
        match v.link with
        | NoLink ->
            begin
              match t2 with
              | Var {link = TLink t2'} -> unify_for_lemma priority_vars t1 t2'
              | Var v' when v.unfailing ->
                         if List.memq v' priority_vars && v'.unfailing
                  then link v' (TLink t1)
                  else link v (TLink t2)
              | Var v' when v'.unfailing ->
                       link v' (TLink t1)
              | FunApp (f_symb,_) when f_symb.f_cat = Failure && v.unfailing = false -> raise Unify
              | Var v' when v'.vname.name = Param.def_var_name ->
                  if List.memq v priority_vars && not (List.memq v' priority_vars)
                  then link v (TLink t2)
                  else link v' (TLink t1)
              | Var v' ->
                  if List.memq v' priority_vars
                  then link v' (TLink t1)
                  else link v (TLink t2)
              | _ ->
                  occur_check v t2;
                         link v (TLink t2)
            end
        | TLink t1' -> unify_for_lemma priority_vars t1' t2
        | _ -> internal_error "Unexpected link in unify 1"
      end
  | (FunApp(f_symb,_), Var v) ->
      begin
        match v.link with
          NoLink ->
            if v.unfailing = false && f_symb.f_cat = Failure
            then raise Unify
            else
              begin
                     occur_check v t1;
                link v (TLink t1)
              end
        | TLink t2' -> unify_for_lemma priority_vars t1 t2'
        | _ -> internal_error "Unexpected link in unify 2"
      end
  | (FunApp(f1, l1), FunApp(f2,l2)) ->
      if f1 != f2 then raise Unify;
      List.iter2 (unify_for_lemma priority_vars) l1 l2

let match_and_apply_lemma next_stage_no_match next_stage_match last_analyzed_hist ((hyp,concl,hist,constra) as rule) induction in_verification lemma =
  if !current_bound_vars <> []
  then Parsing_helper.internal_error "[rules.ml >> match_lemma] No variables should be linked.";

  let app_op = get_option_lemma in_verification lemma in

  let (premise_lem1, subterms_list, constra_premise, l_conclusion1) =
    Terms.auto_cleanup (fun () ->
      let conclusion1 =
        List.map (fun (hyp_lem,constra_lem, eqs_lem) ->
          (Terms.mapq_list Terms.copy_fact hyp_lem,Terms.copy_constra constra_lem, List.map (fun (t1,t2) -> Terms.copy_term t1, Terms.copy_term t2) eqs_lem)
        ) lemma.l_conclusion
      in
      let subterms = List.map (fun (t1,t2) -> Terms.copy_term t1, Terms.copy_term t2) lemma.l_subterms in
      (List.map Terms.copy_fact lemma.l_premise, subterms, Terms.copy_constra lemma.l_constra, conclusion1)
    )
  in

  let index_predicate_lemma = Terms.get_index_predicate premise_lem1 in
  let nb_fact_premise = List.length premise_lem1 in

  let hyp_index = List.mapi (fun i f -> (i,f)) hyp in

  let (nb_fact_concl,fact_added_from_concl,index_predicate_concl) =
    if in_verification
    then
      let fact_concl = Terms.fact_list_of_conclusion concl in
      let m_hist, nb = List.fold_left (fun (hist,n) f -> ((n,event_of_inj_event f)::hist), n-1) ([],-1) fact_concl in
      (-nb - 1),m_hist,Some (Terms.get_index_predicate fact_concl)
    else
      if induction then
        0, [], None
      else
        1, [(-1,event_of_inj_event concl)], None
  in

  (* [check_substitution [] variables] returns [true] when the substitution
     defined by links in [variables] only instantiates variables in [exist_vars],
     that is, existential variables of the lemma that we are applying.
     In that case, the lemma is not considered to instantiate the clause. *)
  let exists_vars =
    let vars = ref [] in
    List.iter (Terms.get_vars_fact vars) premise_lem1;
    let vars_conclu = ref [] in
    List.iter (fun (fact_lem, constra_lem,eqs_lem) ->
      List.iter (fun (t1,t2) -> Terms.get_vars vars_conclu t1; Terms.get_vars vars_conclu t2) eqs_lem;
      iter_constraints (Terms.get_vars vars_conclu) constra_lem;
      List.iter (Terms.get_vars_fact vars_conclu) fact_lem;
    ) l_conclusion1;
    List.filter (fun v -> not (List.memq v !vars)) !vars_conclu
  in
  let instantiates_only_existential_vars vars =
    List.for_all (fun v -> List.memq v exists_vars) vars
  in

  (* The content of [last_analyzed_hist] is typically the order information
    of either the rule [rule], meaning that it was previously computed by
    previous application of [match_and_apply_lemma] or of one of the "ancestor"
    rule of [rule], i.e. a rule which after some normalisation steps produced [rule].

    If [verify_induction_condition] is applied in the function [match_all] below,
    [last_ordered_rule'] corresponds necessarily to [rule] thus we update
    [last_ordered_rule_ref]. This allows us to minimizing the analysis of a rule's
    history to produce the order information.
  *)
  let last_analyzed_hist_ref = ref last_analyzed_hist in

  (* Add specific application when l_sat_app = LAOnlyWhenRemove. *)
  (* Raise NoMatch when the conditions for applying the lemme are not satisfied. *)
  let apply_lemma_if_options_allow match_hyp matched_sub =
    let accu_rule = ref [] in

    let generate_new_rule only_inst_exist_vars fact_lem constra_lem eqs_lem =
      let (fact_lem1,constra_lem1,hyp1,concl1,constra1) =
        Terms.auto_cleanup (fun () ->
          Terms.mapq_list Terms.copy_fact2 fact_lem,
          Terms.copy_constra2 constra_lem,
          Terms.mapq_list Terms.copy_fact2 hyp,
          Terms.copy_fact2 concl,
          Terms.copy_constra2 constra
        )
      in

      let hyp2 = hyp1 @ fact_lem1
      and hist2 = HLemma(lemma.l_index,match_hyp,matched_sub,(fact_lem,constra_lem,eqs_lem),hist)
      and constra2 = Terms.wedge_constraints constra1 constra_lem1 in

      TermsEq.simplify_constraints_rule (fun rule ->
        (* We are adding a clause, so we cannot apply the lemma when
           lemma.l_sat_app = LAOnlyWhenRemove *)
        if app_op = LAOnlyWhenRemove then raise NoMatch;
        accu_rule := (only_inst_exist_vars,rule) :: !accu_rule
      ) (fun rule  ->
        (* We are adding a clause, so we cannot apply the lemma when
           lemma.l_sat_app = LAOnlyWhenRemove *)

        if app_op = LAOnlyWhenRemove then raise NoMatch;
        accu_rule := (only_inst_exist_vars,rule) :: !accu_rule
      ) (hyp2,concl1,hist2,constra2)
    in

    if app_op = LAOnlyWhenInstantiate
    then
      begin
        (* The only possible application case is when variables are instantiated *)
        List.iter (fun (fact_lem, constra_lem,eqs_lem) ->
          try
            Terms.auto_cleanup (fun () ->
              List.iter (fun (t1,t2) -> unify_for_lemma exists_vars t1 t2) eqs_lem;

              if instantiates_only_existential_vars (!current_bound_vars)
              then
                begin
                  TermsEq.check_constraints constra_lem;
                  raise NoMatch
                end
              else generate_new_rule false fact_lem constra_lem eqs_lem
            )
          with Unify | TermsEq.FalseConstraint -> ()
        ) l_conclusion1
      end
    else
      begin
        (* Check that the application of the lemma is not identity for this rule *)
        List.iter (fun (fact_lem, constra_lem,eqs_lem) ->
          try
            Terms.auto_cleanup (fun () ->
              List.iter (fun (t1,t2) -> unify_for_lemma exists_vars t1 t2) eqs_lem;

              if instantiates_only_existential_vars (!current_bound_vars)
              then
                begin
                  (* Check if all facts are included. Since the unification did not unify anything, all linked variables comes from matching. *)
                  let is_implied =
                    if exists_vars = []
                    then
                      ((* facts implied *)
                        last_analyzed_hist_ref := analyse_history !last_analyzed_hist_ref rule;
                        match !last_analyzed_hist_ref with
                          | None ->
                              List.for_all (fun fact ->
                                let fact1 = Terms.copy_fact4 fact in
                                List.exists (Terms.equal_facts fact1) hyp
                              ) fact_lem
                          | Some ana_hist ->
                              let ord_fun_lem = generate_ordering_fun_from_lemma ana_hist.a_order_data match_hyp in
                              List.for_all (fun fact ->
                                let fact1 = Terms.copy_fact4 fact in
                                List.exists2 (fun fact_hyp (ord_fun_hyp,_) ->
                                  Terms.equal_facts fact1 fact_hyp && (not (can_fact_have_ordering_fun fact_hyp) || implies_ordering_function_bool ord_fun_lem ord_fun_hyp)
                                ) hyp ana_hist.a_order_data
                              ) fact_lem
                      )
                      &&
                      ((* constraints implied *)
                       try
                         (* Check that implies_constra_list does not link new variables *)
                         TermsEq.implies_constraints_keepvars4 (concl::hyp) constra constra_lem;
                         true
                       with NoMatch -> false)
                    else
                      Terms.auto_cleanup (fun () ->
                        (* Due to the presence of existential variables, we need to check that the conclusion
                           of the lemma is not redundant with the hypotheses of the clause.

                           Since the condition [instantiates_only_existential_vars (!current_bound_vars)] holds,
                           we know that no variables of the clause have been instantiated and only existential variable may
                           have been instantiated with TLinks.
                        *)

                        try
                          last_analyzed_hist_ref := analyse_history !last_analyzed_hist_ref rule;
                          match !last_analyzed_hist_ref with
                            | None ->
                                match_hyp_implies (fun () ->
                                  TermsEq.implies_constraints_keepvars4 (concl::hyp) constra constra_lem;
                                  true
                                ) (reorder fact_lem) hyp
                            | Some ana_hist ->
                                let ord_fun_lem = generate_ordering_fun_from_lemma ana_hist.a_order_data match_hyp in
                                let ord_fact_lem =
                                    List.map (function
                                      | Pred(p,_) as f when is_user_defined_may_block_version p -> (f,([],false))
                                      | f -> (f,(ord_fun_lem,false))
                                    ) fact_lem in
                                let ord_hyp = List.map2 (fun f ord_data -> (f,ord_data)) hyp ana_hist.a_order_data in
                                match_hyp_ordered_implies (fun () ->
                                  TermsEq.implies_constraints_keepvars4 (concl::hyp) constra constra_lem;
                                  true
                                ) (reorder_ordered ord_fact_lem) ord_hyp
                        with NoMatch -> false
                      )
                  in

                  if is_implied
                  then raise NoMatch
                  else generate_new_rule true fact_lem constra_lem eqs_lem
                end
              else generate_new_rule false fact_lem constra_lem eqs_lem
            )
          with Unify -> ()
        ) l_conclusion1
      end;

    (* Now the new rules are accumulated in accu_rule, apply the next functions *)
    Terms.auto_cleanup (fun () ->
      List.iter (fun (only_inst_exist_vars,r) -> next_stage_match !last_analyzed_hist_ref only_inst_exist_vars r) !accu_rule
    )
  in

  (* [t] must contain only variables from the clause.
     It should have been copied (without renaming) before applying this function *)
  let rec match_one_subterm f_next pos_l t_sub t = match t with
    | Var _ | FunApp({ f_cat = Name _; _},_) ->
        Terms.auto_cleanup (fun () ->
          Terms.match_terms t_sub t;
          f_next (List.rev pos_l)
        )
    | FunApp(_,args) ->
        try
          Terms.auto_cleanup (fun () ->
            Terms.match_terms t_sub t;
            f_next (List.rev pos_l)
          )
        with NoMatch -> match_one_subterm_list f_next pos_l 1 t_sub args

  and match_one_subterm_list f_next pos_l i t_sub = function
    | [] -> raise NoMatch
    | t::q ->
        try
          match_one_subterm f_next (i::pos_l) t_sub t
        with NoMatch -> match_one_subterm_list f_next pos_l (i+1) t_sub q
  in

  let match_subterms f_next l_subterm =
    let l_subterm' = List.map (fun (t_sub,t) -> (t_sub,t,Terms.copy_term3 t)) l_subterm in

    let rec explore matched_sub = function
      | [] -> f_next matched_sub
      | (t_sub,t,t_inst)::q ->
          match_one_subterm (fun pos_l ->
            explore ((t_sub,t,pos_l)::matched_sub) q
          ) [] t_sub t_inst
    in

    explore [] l_subterm'
  in

  (* In the argument [fl_hyp], an element (n,f) represent a fact and its position
    in the clause. When [n] is negative, then it's part of the conclusion. When [n] is
    positive then it's part of the hypothesis. Note that predicate in the conclusion
    haven't been changed other than transforming injective events into events. In particular
    events are not blocking  when [n] is negative (but they are when [n] is positive as
    they appear in the hypotheses).

    In the the argument [matched_hyp], an element (n,f) represent a premise of the
    lemma, i.e. [f] as well as the index [n] of the fact in the rule with whom
    [f] was matched.
    The list [matched_hyp] is reversed.
  *)
  let rec match_all (matched_hyp:(int*fact) list) fl_hyp = function
    | [] ->
        (* Check constraints *)
        let constra_implied = 
          try
            (* Check that implies_constra_list does not link new variables *)
            TermsEq.implies_constraints_keepvars3 (concl::hyp) constra constra_premise;
            true
          with NoMatch -> false
        in
        if not constra_implied then raise NoMatch;

        (* Check subterms *)
        match_subterms (fun matched_sub ->
          let (lemma_applicable, last_analyzed_hist') =
            verify_application_condition
              !last_analyzed_hist_ref
              (index_predicate_concl,nb_fact_concl)
              (index_predicate_lemma,nb_fact_premise)
              (List.rev matched_hyp) rule
              l_conclusion1
              induction in_verification
          in
          last_analyzed_hist_ref := last_analyzed_hist';
          if lemma_applicable
          then apply_lemma_if_options_allow matched_hyp matched_sub
          else raise NoMatch
        ) subterms_list
    | fact_lem::q_lem -> match_one matched_hyp fact_lem q_lem [] fl_hyp

  and match_one (matched_hyp:(int*fact) list) fact_lem q_lem prev_hyp = function
    | [] -> raise NoMatch
    | (i_hyp,fact_hyp)::q_hyp ->
        try
          Terms.auto_cleanup (fun () ->
            (* Case to consider :
                Without induction, we do a match with greater phases. With induction,
                we match the same phase.

                - During Solving:
                  1. To match premise of lemma with conclusion
                      -> normal match
                  2. To match premise of lemma with hypothesis of rule
                      -> match with unblocking predicate
                - During Saturation (Lemma)
                  1. To match premise of lemma with conclusion
                      -> normal match
                  2. To match premise of lemma with hypothesis of the rule
                      -> match with unblocking predicate
                - During Saturation (Inductive lemma)
                  We only match premise of lemma hypothesis of the rule with special condition:
                  match with unblocking predicate
            *)

            let match_fun =
              if in_verification
              then
                if i_hyp < 0
                then if induction then match_facts else match_facts_phase_geq
                else if induction then match_facts_unblock else match_facts_unblock_phase_geq
              else
                if induction
                then
		  match_facts_unblock
                else
                  if i_hyp < 0
                  then match_facts_phase_geq
                  else match_facts_unblock_phase_geq
            in

            match_fun fact_lem (event_of_inj_event fact_hyp);
            match_all ((i_hyp,fact_lem)::matched_hyp) (prev_hyp @ q_hyp) q_lem
          )
        with NoMatch ->
          match_one matched_hyp fact_lem q_lem ((i_hyp,fact_hyp)::prev_hyp) q_hyp
  in

  try
    match_all [] (fact_added_from_concl @ hyp_index) premise_lem1
  with NoMatch -> next_stage_no_match !last_analyzed_hist_ref

let simplify_lemmas next_stage_no_match next_stage in_solving lemmas inductive_lemmas last_analyzed_hist rule =

  (* [only_inst_exists_vars_opt = None] when we have applied no lemma;
     [only_inst_exists_vars_opt = Some only_inst_exists_vars] when we have applied a lemma
     and it has instantiated variables of the clause iff not [only_inst_exists_vars] *)
  let rec match_rule only_inst_exists_vars_opt last_analyzed_hist rule =
    assert (!current_bound_vars == []);
    match_and_apply_all only_inst_exists_vars_opt last_analyzed_hist rule (lemmas,inductive_lemmas)

  and match_and_apply_all only_inst_exists_vars_opt last_analyzed_hist ((hyp,concl,hist,constra) as rule) (lemmas,inductive_lemmas) =
    if lemmas = [] && inductive_lemmas = []
    then
      match only_inst_exists_vars_opt with
      | Some only_inst_exists_vars ->
          next_stage only_inst_exists_vars last_analyzed_hist rule
      | None ->
          next_stage_no_match last_analyzed_hist rule
    else
      let (induction,lemma,rest_lemmas) = match lemmas,inductive_lemmas with
        | lemma :: q_lem, ind_lemmas -> (false,lemma,(q_lem,ind_lemmas))
        | [], lemma :: q_lem -> (true,lemma,([],q_lem))
        | [],[] -> internal_error "[rules.ml >> simplify_lemmas] SHould have been caught before."
      in
      match_and_apply_lemma
        (fun last_analyzed_hist' -> match_and_apply_all only_inst_exists_vars_opt last_analyzed_hist' rule rest_lemmas)
        (fun last_analysed_hist1 only_inst_exists_vars1 rule1 ->
          let only_inst_exists_vars_opt' =
            match only_inst_exists_vars_opt with
            | Some _ -> only_inst_exists_vars_opt
                  (* We cannot take into accound that the new application of a lemma
                     may have instantiated variables of the initial clause, because
                     it may happen that the first application creates new variables, and
                     the next application of a lemma instantiates those variables thinking
                     they are variables of the initial clause (which they are not). *)
            | None -> Some only_inst_exists_vars1
          in
          match_rule only_inst_exists_vars_opt' last_analysed_hist1 rule1
        )
        last_analyzed_hist
        rule
        induction
        in_solving
        lemma
  in

  if lemmas = [] && inductive_lemmas = []
  then next_stage_no_match last_analyzed_hist rule
  else match_rule None last_analyzed_hist rule

let simplify_lemmas_saturation next_stage_no_match next_stage lemmas inductive_lemmas rule =
  simplify_lemmas (fun _ r -> next_stage_no_match r) (fun only_inst_exist_vars _ r -> next_stage only_inst_exist_vars r) false lemmas inductive_lemmas None rule

let simplify_lemmas_solving next_stage_no_match next_stage lemmas inductive_lemmas last_analysed_hist rule =
  simplify_lemmas next_stage_no_match next_stage true lemmas inductive_lemmas last_analysed_hist rule

(* 12. Simplification on natural numbers. *)

let rec may_be_nat_number = function
  | Var v -> true
  | FunApp(f,[t]) when f == Terms.succ_fun -> may_be_nat_number t
  | _ -> false

(* Calls to [simplify_natural_number] are prevented on standard clauses in
   [normal_rule], in particular on the clauses for 0 and +1. *)
let simplify_natural_number next_stage ((_,concl,_,constra) as rule) = match concl with
  | Pred({p_info = Attacker _},[t]) when may_be_nat_number t ->
        begin
          try
            let constra' = Terms.constraints_of_is_nat t in
            TermsEq.implies_constraints_keepvars [concl] constra constra'
          with NoMatch -> next_stage rule
        end
  | Pred({p_info = AttackerBin _ | AttackerGuess _},[t1;t2]) when may_be_nat_number t1 && Terms.equal_terms t1 t2 ->
        begin
          try
            let constra' = Terms.constraints_of_is_nat t1 in
            TermsEq.implies_constraints_keepvars [concl] constra constra'
          with NoMatch -> next_stage rule
        end
  | _ -> next_stage rule

(* 13. Removal of useless events for lemmas *)

let initialise_useless_events_for_lemmas events_in_queries lemmas =
  events_only_for_lemmas := [];
  events_only_for_lemmas_without_options := [];
  all_original_lemmas := [];

  (* We record first the lemmas that are used in either saturation or solving *)
  List.iter (fun lem ->
    if lem.l_sat_app <> LANone || lem.l_verif_app <> LANone
    then all_original_lemmas := lem :: !all_original_lemmas
  ) lemmas;

  (* We first add to [events_in_queries] the events of the lemmas with the option REKeep. *)
  let acc_events_in_queries = ref events_in_queries in

  List.iter (fun lemma ->
    if lemma.l_remove_events = REKeep
    then
      List.iter (function
        | Pred(p,(FunApp(ev,_)::_)) when p == Param.event_pred || p == Param.event2_pred ->
            if not (List.memq ev !acc_events_in_queries)
            then acc_events_in_queries := ev :: !acc_events_in_queries
        | _ -> ()
      ) lemma.l_premise
  ) !all_original_lemmas;

  List.iter (fun lemma ->
    if lemma.l_remove_events = RERemove || (lemma.l_remove_events = RENone && !Param.event_lemma_simplification)
    then
      List.iter (function
        | Pred(p,(FunApp(ev,_)::_)) when p == Param.event_pred || p == Param.event2_pred ->
            if not (List.memq ev !acc_events_in_queries) && not (List.memq ev !events_only_for_lemmas)
            then events_only_for_lemmas := ev :: !events_only_for_lemmas
        | _ -> ()
      ) lemma.l_premise
  ) !all_original_lemmas;

  List.iter (fun lemma ->
    List.iter (function
      | Pred(p,(FunApp(ev,_)::_)) when p == Param.event_pred || p == Param.event2_pred ->
          if not (List.memq ev events_in_queries) && not (List.memq ev !events_only_for_lemmas_without_options)
          then events_only_for_lemmas_without_options := ev :: !events_only_for_lemmas_without_options
      | _ -> ()
    ) lemma.l_premise
  ) !all_original_lemmas

let is_fact_only_for_lemma = function
  | Pred(p,(FunApp(ev,args)::_)) when (p == Param.event_pred_block || p == Param.event2_pred_block || p == Param.inj_event_pred_block) && List.memq ev !events_only_for_lemmas -> true
  | _ -> false

let is_fact_only_for_lemma_bad = function
  | Pred(p,(FunApp(ev,args)::_)) when (p == Param.event_pred_block || p == Param.event2_pred_block || p == Param.inj_event_pred_block) && List.memq ev !events_only_for_lemmas_without_options -> true
  | _ -> false

let rec mark_variables_follow = function
  | Var { link = TLink t; _ } -> mark_variables_follow t
  | Var ({ link = NoLink; _ } as v)-> Terms.link v (VLink v)
  | Var _ -> ()
  | FunApp(_,args) -> List.iter mark_variables_follow args

let rec mark_variables_follow_fact = function
  | Pred(_,args) -> List.iter mark_variables_follow args

(* [inter_variables vars t] adds to [vars] to the marked variables in [t] *)
let rec inter_variables vars = function
  | Var { link = TLink t; _} -> inter_variables vars t
  | Var ({ link = VLink _; _ } as v)->
      if not (List.memq v !vars)
      then vars := v :: !vars
  | Var _ -> ()
  | FunApp(_,args) -> List.iter (inter_variables vars) args

let inter_variables_fact vars = function
  | Pred(_,args) -> List.iter (inter_variables vars) args

let rec remove_from_list x = function
  | [] -> []
  | x'::q when x' == x -> q
  | x'::q -> x' :: (remove_from_list x q)

(* [vars_not_in vars t] removes from [vars] the marked variables in [t].
   Raises [NoMatch] in case no variable remains in [vars]. *)
let rec vars_not_in vars = function
  | Var { link = TLink t; _} -> vars_not_in vars t
  | Var ({ link = NoLink; _ } as v)->
      Terms.link v (VLink v);
      vars := remove_from_list v !vars;
      if !vars = []
      then raise NoMatch
  | Var _ -> ()
  | FunApp(_,args) -> List.iter (vars_not_in vars) args

let vars_not_in_fact vars = function
  | Pred(_,args) -> List.iter (vars_not_in vars) args

let vars_not_in_nat vars constra =
  List.iter (vars_not_in vars) constra.is_nat;
  List.iter (fun (x,_,y) ->
    vars_not_in vars x;
    vars_not_in vars y;
  ) constra.geq

(* [is_forced_removal_rule_bad rule] is true when the clause [rule]
is of the form H -> bad where H contains only unselectable facts
and attacker2(x,y) for variables x,y.
In this case, attacker2(x,y) will be selected, very likely yielding
non-termination. In this case, we remove events useful only for lemmas
(without option KeepEvents), by the function
[remove_useless_events_for_lemma_bad]; that allows the removal of
attacker2(...) facts containing variables common with events. We can
then often obtain a simplified clause -> bad, and avoid the
non-termination. *)

let is_forced_removal_rule_bad (hypl,concl,_,_) = match concl with
  | Pred(p,[]) when p == Param.bad_pred ->
      List.for_all (function
        | Pred({p_info = AttackerBin _ | AttackerGuess _; _},args) -> List.for_all (function Var _ -> true | _ -> false) args
        | fact -> Terms.is_unselectable fact
      ) hypl
  | _ -> false

let remove_useless_events_for_lemma_bad (hypl,concl,hist,constra) =
  let rec remove_facts n hist = function
    | [] -> ([],hist)
    | fact :: q_fact ->
        let (q_fact',hist') = remove_facts (n+1) hist q_fact in

        if is_fact_only_for_lemma_bad fact
        then (q_fact',HMaxHyp(n,hist'))
        else (fact::q_fact',hist')
  in

  let (hypl',hist') = remove_facts 0 hist hypl in
  if hist == hist'
  then (hypl,concl,hist,constra) (* No modification *)
  else
    TermsEq.simple_simplify_constraints_rule
      (elim_any_x (hypl',concl,hist',constra))

let remove_useless_events_for_lemma_main in_saturation lemmas ((hypl,concl,hist,constra) as rule) =
  let check_one_fact_vs_one_fact_lemma fact sel_fact_end_or_inj_event_list begin_ev_fact_list fact_lem fact_lem_list =
    (* We have a clause [fact && sel_fact_end_or_inj_event_list && begin_ev_fact_list && constra => concl]
       and a lemma [fact_lem && fact_lem_list => ... ]
       We try to apply the lemma to a clause obtained by resolution from the clause
       above by unifying [fact] and [fact_lem]. Let [\sigma] be their mgu.
       If [possible_vars] is non-empty at the end of this function, the lemma can
       never be applied in this way on a clause obtained by resolution for the current
       clause, so we remove the event [fact] (since it is also useful only for lemmas).
       However, this transformation is complete in full generality, because the
       current clause can also be transformed by applied other lemmas at some point,
       which may later make an applicationn of a lemma using [fact] possible.

       Proof sketch: Let x be a variable in [possible_vars].
       x occurs in [fact_lem\sigma = fact\sigma]. So there is a variable y
       such that y occurs in [fact] and x occurs in y\sigma.
       x does not occur in [sel_fact_end_or_inj_event_list\sigma], [concl\sigma] and [nat_constra\sigma],
       so y does not occur in [sel_fact_end_or_inj_event_list], [concl], and [nat_constra].
       Hence during resolution from the clause [fact && sel_fact_end_or_inj_event_list && begin_ev_fact_list && constra => concl],
       the variable y will never be instantiated, so the clause obtained by resolution
       is [fact' && H && begin_ev_fact_list' => C] where y occurs in [fact'] (which is an instance of [fact]),
       y does not occur in H,C, and [begin_ev_fact_list'] is an instance of [begin_ev_fact_list].
       When we apply the lemma on this clause, [fact'] must be an instance of [fact_lem],
       so in fact y is left unchanged, i.e. y = x.
       The variable x does not occur in the events of [begin_ev_fact_list\sigma && H, C] that may
       be used to match [fact_lem_list\sigma], so y does not occur in the events of
       [begin_ev_fact_list' && H,C] that may be used to match [fact_lem_list].
       However, y = x occurs in [fact_lem_list\sigma]. The matching is then impossible.
       *)
    Terms.auto_cleanup (fun () ->
      try
        Terms.unify_facts (Terms.unblock_predicate_fact fact) fact_lem;

        let possible_vars = ref [] in
        Terms.auto_cleanup (fun () ->
          (* We start by marking the variables of fact_lem\sigma*)
          mark_variables_follow_fact fact_lem;

          (* We retrieve the variables that are also in fact_lem_list\sigma *)
          List.iter (inter_variables_fact possible_vars) fact_lem_list
        );
        if !possible_vars = []
        then false
        else
          begin
            try
              (* We remove from possible_vars the variables that are in the conclusion
                 and the potentially selectable facts, as well as injective events
                 and end events. *)
              Terms.auto_cleanup (fun () ->
                List.iter (vars_not_in_fact possible_vars) (concl::sel_fact_end_or_inj_event_list);
                vars_not_in_nat possible_vars constra;
              );
              (* We remove from possible_vars the variables that are in the begin events
                 that can unify with the other premises of the lemma. Note that the application
                 of the lemma may also use the conclusion as well as end events and injective
                 events in the hypothesis. The variables of those have already been removed above. *)
              List.iter (fun fact_ev ->
                if List.exists (fun fact_lem' -> are_facts_syntactically_unifiable (Terms.unblock_predicate_fact fact_ev) fact_lem') fact_lem_list
                then
                  Terms.auto_cleanup (fun () ->
                    vars_not_in_fact possible_vars fact_ev
                  )
              ) begin_ev_fact_list;
              true
            with NoMatch -> false
          end
      with Unify -> true
    )
  in

  let event_may_be_used = (Selfun.selection_fun_nostatechange rule = -1) in

  (* [fact] is blocking and non_injective *)
  let check_one_fact_vs_lemma fact fact_list lemma =

    match lemma.l_premise with
      | [fact_lem] ->
          (* When there is only one fact in the premise of the lemma, we check that the lemma was already applied. The test is sound but not complete. *)
          if event_may_be_used && ((in_saturation && lemma.l_sat_app = LAFull) || (not in_saturation && lemma.l_verif_app = LAFull))
          then
            Terms.auto_cleanup (fun () ->
              try
                match_facts_phase_geq fact_lem (Terms.unblock_predicate_fact fact);
                true
              with NoMatch -> false
            )
          else false
      | _ ->
          (* When there is more than one fact in the premise of the lemma, we check that the lemma cannot be applied. The test is also not complete. *)
          let (sel_fact_end_or_inj_events,begin_ev_facts) = List.partition (function Pred(p,_) when p == Param.event_pred_block || p == Param.event2_pred_block -> false | _ -> true) fact_list in
          let rec go_through_premise fact_lem_list = function
            | [] -> true
            | fact_lem :: q_lem ->
                if check_one_fact_vs_one_fact_lemma fact sel_fact_end_or_inj_events begin_ev_facts fact_lem (List.rev_append fact_lem_list q_lem)
                then go_through_premise (fact_lem::fact_lem_list) q_lem
                else false
          in
          go_through_premise [] lemma.l_premise
  in

  let rec check_facts_in_hypl n rest_hypl hypl hist = match hypl with
    | [] -> ([],hist)
    | fact :: q_fact ->
        let (q_fact',hist') = check_facts_in_hypl (n+1) (fact::rest_hypl) q_fact hist in

        if is_fact_only_for_lemma fact
        then
          (* In that case, the event cannot be injective, because 
	     lemmas/axioms/restrictions cannot contain injective events and 
	     the considered event occurs only in lemmas/axioms/restrictions. 
	     So, if [fact] is an event we look for, it is necessarily 
	     non-injective and blocking (as it is in hypothesis of the clause)*)
          let hypl' = rest_hypl@q_fact' in
          if List.for_all (check_one_fact_vs_lemma fact hypl') lemmas
          then
            (* The fact has been found useless. We use HMaxHyp for history but we should
               probably use a new one for clarity. *)
            (q_fact',HMaxHyp(n,hist'))
          else (fact::q_fact',hist')
        else (fact::q_fact',hist')
  in

  let (hypl',hist') = check_facts_in_hypl 0 [] hypl hist in
  if hist == hist'
  then rule (* No modification *)
  else
    TermsEq.simple_simplify_constraints_rule
      (elim_any_x (hypl',concl,hist',constra))

let remove_useless_events_for_lemma in_saturation lemmas rule =
  if lemmas <> []
  then
    if is_forced_removal_rule_bad rule
    then remove_useless_events_for_lemma_bad rule
    else
      if !events_only_for_lemmas <> []
      then remove_useless_events_for_lemma_main in_saturation lemmas rule
      else rule
  else rule

(* 14. Simplification of conclusion attacker2(t,fail) and
   attacker2(fail,t) into bad. Also remove clauses that conclude
   non-constant attacker facts that contain ground public terms (they
   can be inferred by applying each function symbol one after the
   other). *)

let simplify_conclusion next_f ((hyp,concl,hist,constra) as r) = match concl with
  | Pred({ p_info = AttackerBin _ | AttackerGuess _;_} as p, [t1;t2]) ->
      let replace left =
        let hist_fail = History.get_rule_hist (RFail(left,p)) in
        let hist' = Resolution(hist,0,hist_fail) in
        next_f (hyp,Pred(Param.bad_pred,[]),hist',constra)
      in
      if Terms.is_failure t1 && not (Terms.is_may_fail_term t2)
      then replace false
      else if Terms.is_failure t2 && not (Terms.is_may_fail_term t1)
      then replace true
      else
        begin match t1 with
          | FunApp(_,[]) -> next_f r
          | _ ->
            if not (Terms.is_ground_public t1 && Terms.equal_terms t1 t2)
            then next_f r
        end
  | Pred({p_info = Attacker _;_}, [t]) ->
      begin match t with
        | FunApp(_,[]) -> next_f r
        | _ ->  if not (Terms.is_ground_public t) then next_f r
      end
  | _ -> next_f r

(* Combines the previous simplication functions, then add the
   simplified rule to the rule base *)

(* [is_standard_clause r] returns true when the clause [r]
   must be protected from simplifications *)
let is_standard_clause ((_,_,hist,_) as r) =
  (match hist with
  | Rule(_,tag,_,_,_) ->
      begin
        match tag with
        | PhaseChange (* phase clause *)
        | Rl _ (* listening clause *)
	| LblEquiv -> true
        | Apply(f, _) (* data constructor or projection clause *) ->
	    Terms.is_data_or_proj f
	      (* Clauses for data constructors 
		   att(x1) && ... && att(xn) -> att(f(x1...xn))
		   att'(x1,y1) && ... && att'(xn,yn) -> att'(f(x1...xn),f(y1...yn))
		 and projections 
                   att(f(x1...xn)) -> att(xi)
		   att'(f(x1...xn),f(y1...yn)) -> att'(xi,yi)
		 as well as clauses LblEquiv must be preserved for the decomposition
		 of data constructors and the replacement of equivalent facts
		 performed in [decompose_hyp_tuples] and [decompose_concl_tuples]
		 to be sound.
		 In particular, clauses for the data constructors 0 and +1 
		 must be preserved for the simplification of natural numbers
		 performed in [simplify_natural_number] to be sound. *)
        | _ -> false
      end
  | _ -> false) ||
    Weaksecr.is_standard_clause r || Noninterf.is_standard_clause r

let normal_rule database lemmas inductive_lemmas r =
  let rec normal_rule apply_lemma r =
    assert (!Terms.current_bound_vars == []);
    simplify_conclusion (
      decompose_hyp_tuples2 (
        simp_eq_rule (
          elim_not (
            Weaksecr.simplify (
              Noninterf.simplify (
                decompose_concl_tuples (
                  elim_taut (
                    elim_any_x2 (
                      simplify_rule_constra (
                        simplify_natural_number (
                          elem_simplif (
                            elim_redundant_hyp (fun rule1 ->
                              let next_no_lemma rule2 = Weaksecr.remove_equiv_events (limit_induction normal_rule_add_rule (normal_rule apply_lemma)) rule2 in
                              if apply_lemma
                              then simplify_lemmas_saturation next_no_lemma (fun only_inst_exist_vars rule3 -> normal_rule (not only_inst_exist_vars) rule3) lemmas inductive_lemmas rule1
                              else next_no_lemma rule1
                            ) (normal_rule apply_lemma)
                          ) (normal_rule apply_lemma)
                        )
                      ) (normal_rule apply_lemma)
                    )
                  )
                )
              ) (normal_rule apply_lemma)
            ) (normal_rule apply_lemma)
          )
        )
      )
    ) r

  (* Note that currently, we apply remove_useless_events_for_lemma on all clauses but we could as an
     alternative only apply it on clauses with the conclusion selected. *)
  and normal_rule_add_rule r = Database.DB.add_rule database (remove_useless_events_for_lemma true !all_original_lemmas (limit_depth_rule r)) in

  if is_standard_clause r then
    (* [simplify_conclusion] must be applied to the projection clauses
       att'(f(x1...xn),x) && x <> f(g1...gn) -> att'(xi, fail)
       (see weaksecr.ml)
       It does not affect other standard clauses, so it is fine to 
       apply it to all standard clauses *)
    simplify_conclusion (Database.DB.add_rule database) r
  else
    normal_rule true r

(* During solving, the standard clauses have already been included in the
   database, so we do not need to protect them any more. *)
let normal_rule_solving apply_not database lemmas inductive_lemmas ord_rule =

  let all_lemmas = lemmas @ inductive_lemmas in

  let rec normal_rule apply_lemma ana_hist_op rule =
    assert (!Terms.current_bound_vars == []);
    decompose_hyp_tuples2 (
      elim_not_solving  apply_not (
        Weaksecr.simplify (
          elim_any_x2 (
            simplify_rule_constra (
                elem_simplif (fun r' -> 
                  let ana_hist_op' = analyse_history ana_hist_op r' in
                  elim_redundant_hyp_ordered (fun rule1 ->
                    if apply_lemma
                    then
                      simplify_lemmas_solving normal_rule_add_rule (fun only_inst_exist_vars ana_hist_op2 rule2 ->
                        normal_rule (not only_inst_exist_vars) ana_hist_op2 rule2
                      ) lemmas inductive_lemmas ana_hist_op' rule1
                    else normal_rule_add_rule (analyse_history ana_hist_op rule1) rule1
                  ) (normal_rule apply_lemma ana_hist_op') ana_hist_op' r'
                ) (normal_rule apply_lemma ana_hist_op)
            ) (normal_rule apply_lemma ana_hist_op)
          )
        ) (normal_rule apply_lemma ana_hist_op)
      )
    ) rule

  and normal_rule_add_rule ana_hist_op rule =
    let rule' = remove_useless_events_for_lemma false all_lemmas rule in
    let ana_hist_op' = analyse_history ana_hist_op rule' in
    let ord_rule = ordered_rule_of_analysed_history_op ana_hist_op' rule' in
    Database.DBOrd.add_rule database ord_rule

  in

  let ana_hist_op = analysed_history_op_of_ordered_rule ord_rule in
  normal_rule true ana_hist_op ord_rule.rule

(* Check whether hypothesis of the clause is unsatifiable *)

exception Satisfiable

let is_hypothesis_unsatisfiable r =
  assert (!Terms.current_bound_vars == []);

  let rec apply_normal_rule r =
    simp_eq_rule (
      simplify_rule_constra (fun _ -> raise Satisfiable) apply_normal_rule
    ) r
  in

  try
    apply_normal_rule r;
    true
  with Satisfiable -> false

(* [compos] unifies [concl1] with the selected hypothesis of [hyp2]
   and builds the resulting rule
   There must be no selected fact in [rule1], and a selected fact in [rule2]

   R = F1 & ... & Fn -> F0
   R' = F'1 & ... & F'n' -> F'0
can be composed into
      s F1 & ... & s Fn & s F'2 & ... & s F'n -> s F'0
where s is the most general unifier of F0 and F'1
if
    F'1 selected
and for all Fi, Fi not selected

*)

let rec replace_and_copy2_aux l1 l = match l1 with
  | [] -> List.map copy_fact2 l
  | t::q -> (copy_fact2 t)::(replace_and_copy2_aux q l)

let rec replace_and_copy2 l1 n = function
    [] -> internal_error "replace_and_copy2"
  | (a::l) ->
      if n = 0
      then replace_and_copy2_aux l1 l
      else (copy_fact2 a)::(replace_and_copy2 l1 (n-1) l)

let compos next_stage (hyp1, concl1, hist1,constra1) (hyp2, concl2, hist2,constra2) (sel_index, fact) =
  (* compose with the selected fact *)
  assert (!current_bound_vars == []);
  try
    (*let a = record_time time_compo (fun () -> List.nth hyp2 sel_index) in*)
    unify_facts concl1 fact;
    let hyp' = replace_and_copy2 hyp1 sel_index hyp2 in
    (* Careful ! The order of hypotheses is important for the history *)
    let concl' = copy_fact2 concl2 in
    let hist' = Resolution(hist1, sel_index, hist2) in
    let constra' = wedge_constraints (copy_constra2 constra1) (copy_constra2 constra2) in
    cleanup();
    next_stage (hyp', concl', hist', constra')
  with Unify ->
    cleanup()

let compos_solving next_stage sat_rule (ord_rule,sel_index,fact,ord_data_op) =
  compos (fun rule' ->
    let order_data_op = match ord_rule.order_data,ord_data_op with
      | None, None -> None
      | Some ord_data_list, Some ord_data ->
          let ord_data_list' = replace_nth_list (sat_rule.sat_generate_ordering_data ord_data) sel_index ord_data_list in
          Some ord_data_list'
      | _ -> internal_error "[rules.ml >> compos_solving] Unexpected case."
    in
    let ord_rule' = { rule = rule'; order_data = order_data_op } in
    next_stage ord_rule'
  ) sat_rule.sat_rule ord_rule.rule (sel_index,fact)

(* Redundancy test [redundant ruleset annotinitrule]
   [ruleset] must be a set of clauses with empty selection
   [annotinitrule] must be a clause with empty selection
   The test returns true if and only if the clause [annotinitrule] can be derived
   with a derivation containing clauses in [ruleset].
*)

(* We show some invariant for the testing of global redundancy:

  During both the saturation procedure, we will compose the ongoing rule with a rule
  that has unselectable hypotheses. Hence, these rules are of the form:
    R = constraints && B && Ax -> C
  where B is a conjunction of blocking predicate, Ax is a conjunction of att(x) and/or comp(x).
  When C is the fact att(x) or comp(x), Ax does not contain att(x) or comp(x) for the same x.
  (Ax cannot contain C, because R would be a tautology,
  so it would be removed. The only other possibilities are that:
   - R = ... & att(x) -> comp(x): impossible because there are no clauses with comp as conclusion
   and another predicate as hypothesis
   - R = ... & comp(x) -> att(x): impossible because all clauses that have comp as hypothesis
   and att as conclusion have a name function symbol as root of the conclusion.)

  We will denote R -> R' a rule R' obtained by composing R with a rule with unselectable hypotheses.

  We can show that all Rinit ->^* R, the rule R is of the form:
    constraints && B && Ax && Am && Anu -> C
  where B is a conjunction of blocking predicates, Ax is a conjunction of att(x) or comp(x),
  Am and Anu are conjunctions of att(M) and/or comp(M) where vars(M) \subseteq vars(C) and
  x is not just a variables,
  facts in Anu match a nounif declaration with weight < dummy_weight = -4000, facts in Am do not.

  Notice that during saturation, the first rule is C -> C.
  Take Rc an unselectable rule constraints' && B' && Ax' -> C' such that \sigma = mgu(C,C'). For the redundancy
  to work, we need C to be unchanged by \sigma, i.e. C\sigma = C.
  This implies that the resulting clause is of the form:
    constraints'\sigma && B'\sigma && Ax'\sigma -> C
  We can split Ax'\sigma as Ax && Am && Anu where facts of Ax are att(x) or comp(x),
  facts of Anu are other facts that match a nounif declaration with weight < dummy_weight.

  Given a rule R, we'll use the notation B(R), Ax(R), Am(R) and Anu(R) for the corresponding
  conjunctions of facts. Finally, we write F1 && ... && Fn < F1' && ... && Fm' when
  {{ |F1|, ..., |Fn| }} <_m {{ |F1'|, ..., |Fm'| }} with <_m is the order on multiset.

  We can show that for all R -> R',
    - B(R)\sigma'' \subseteq B(R') (possibly instantiated due to simplification of constraints)
    - Anu(R) \subseteq Anu(R')
    - Am(R') < Am(R)

  Take a rule R = constraints && B && Ax && Am && Anu -> C with a selectable hypothesis F. This hypothesis
  must be in Am since B are blocking, Ax are att(x) or comp(x), and Anu are matching a nounif
  declaration with weight < dummy_weight.
  Hence Am = Am' && F.

  Take Rc an unselectable rule constraints' && B' && Ax' -> C' such that \sigma = mgu(F,C'). For the redundancy
  to work, we need C to be unchanged by \sigma, i.e. C\sigma = C. But vars(F) \subseteq vars(C)
  hence F\sigma = F. This implies that the resulting clause is of the form:
    constraints && constraints'\sigma && B && Ax && Am' && Anu && B'\sigma && Ax'\sigma -> C
  We can split Ax'\sigma as Ax'' && Am'' && Anu'
  where facts of Ax'' are att(x) or comp(x), facts of Anu' are other facts that match a nounif declaration.
  Note that, when C' is not the fact att(x) or comp(x),
  the facts of Am'' are att(y)\sigma where y is a variable of C', so we have Am'' < C'\sigma = F.
  When C' is att(x) or comp(x), Ax' does not contain att(x) or comp(x) for the same x,
  hence Ax'\sigma = Ax', so Ax'' = Ax', and Am'' and Anu' are empty. Therefore, in both cases,
  Am' && Am'' < Am, which concludes the proof.

  Note that these invariants are preserved by application of elim_any_x (the facts att(x) or comp(x)
  in Ax have a variable that occurs in B, Am, Anu, C, since they were not removed before,
  hence in B or C since the variables of Am, Anu are in C, hence they remain after elim_any_x) and decompose_hyp_tuples.
  The simplification of constraints may instantiate variables of Ax with succ(...succ(x)) or
  succ(...succ(0)). The succ and 0 are removed by decompose_hyp_tuples. The remaining fact att(x) is in Ax.
  The variables of Am, Anu, C cannot be instantiated by the simplification of constraints
  because they all occur in C and C must remain unchanged.
  Can variables of B be instantiated?
     The only common variables between constraints and constraints'\sigma are variables of C,
     which cannot be instantiated. Moreover [constraints] is already simplified.
     Even with that, variables of B can be instantiated in very particular cases. For instance:
     y is a variable of C => cannot be instantiated
     x is a variable of B not in C.
     constraints = x<>y, x<>y+2 is_nat(x) [y may not be nat]  constraints'\sigma = is_nat(y)
     is_nat(x,y) implies that case distinctions are made. The case y<x, x<y+2 implies
     x = y+1 => x is instantiated into y+1.

  Since for all R ->^+ R', Am(R') < Am(R) and all variables of Am(R') and Am(R) are in their respective
  conclusion, we deduce that R cannot subsume R'. So we need not verify that the current rule is not
  subsumed by a previously seen clause in the same branch. Furthermore, we have a termination guarantee.

  Finally, if R ->^* R' and B(R') cannot subsume the hypothesis of [initrule], where the subsumption test
  is computed using set inclusion instead of multiset inclusion (we need set inclusion because
  variables of B may be instantiated, possibly making two elements of B equal; the duplicate element
  is then removed in decompose_hyp_tuples), then we know
  that for all R' ->^* R'', R'' cannot subsume [initrule], so we can stop searching from R'.
*)

exception Redundant

let counter_redundant = ref 0

let redundant ruleset ((((_,initconcl,_,_) as initrule), _) as annot_initrule) =
  let rec redundant_rec ((hyp, _, hist, constra) as rule, _) first =
    let sel_index = Selfun.selection_fun (hyp, Param.dummy_fact, hist, constra) in
    if sel_index != -1 then

      let sel_fact = List.nth hyp sel_index in

      if first || not (is_pred_to_prove_fact sel_fact)
      then
        let apply elt =
          (* In the set of clause with conclusion selected, the additional data represents whether
             the clause contains only unselectable hypotheses. *)
          if first || elt.Database.SetClause.additional_data
          then
            let check_fun ((_,concl,_,_) as r) =
              if matchafact initconcl concl then
                let r' = elim_any_x (Database.remove_ground_public_terms (decompose_hyp_tuples r)) in
                let annot_r' = Database.SubClause.generate_subsumption_data r' in
                let (r_implies,block_set_implies) = Database.SubClause.implies_redundant annot_r' annot_initrule in
                if r_implies
                then raise Redundant
                else if block_set_implies
                then redundant_rec annot_r' false
            in
            let (elt_clause,_) = elt.annot_clause in
            compos (simplify_rule_constra check_fun check_fun) elt_clause rule (sel_index,sel_fact)
        in

        Database.SetClause.iter_unifiable apply ruleset sel_fact
  in
  try
    let rule = ([initconcl], initconcl, Empty(initconcl), true_constraints) in
    let annot_rule = Database.SubClause.generate_subsumption_data rule in
    redundant_rec annot_rule true;
    false
  with Redundant ->
    if !Param.verbose_redundant then
      begin
        incr counter_redundant;
        Printf.printf "Redundant rule eliminated %d:\n" !counter_redundant;
        Display.Text.display_rule_indep initrule
      end;
    true

(* Redundancy test [redundant_solving sat_rules first_rule_set annot_target_rule]
   [sat_rules] is the set of clauses with empty selection obtained as a result of saturation
   [first_rule_set] is the current set of clauses in solving
   [annot_target_rule] must be a clause with empty selection
   The test returns true if and only if the clause [annot_target_rule] can be derived
   with a derivation containing with top clause in [first_rule_set]
   and other clauses in [sat_rules].
*)

let redundant_solving sat_rules first_rule_set ((({ rule = (_,target_concl,_, _); _ } as target_rule), _) as annot_target_rule) =

  let rec redundant_rec ((({ rule = (hyp,concl,hist,constra) } as ord_rule), _) as annot_ord_rule) seen_list =
    if matchafact target_concl concl
    then
      let sel_index = Selfun.selection_fun (hyp, Param.dummy_fact, hist, constra) in
      if (sel_index != -1) && (not (is_pred_to_prove_fact (List.nth hyp sel_index)))
      then
        if not (List.exists (fun annot_r' -> Database.SubOrdClause.implies annot_r' annot_ord_rule) seen_list)
        then
          let seen_list' = annot_ord_rule :: seen_list in
          let sel_fact = List.nth hyp sel_index in
          let sel_ord_data = match ord_rule.order_data with
            | None -> None
            | Some ord_data -> Some (List.nth ord_data sel_index)
          in
          Database.SetSatClause.iter_unifiable (fun sat_rule ->
                  (* [sat_rule] is filtered before calling [redundant_solving]
                     so that it contains only clauses with unselectable hypotheses. *)
            compos_solving (check_ord_rule seen_list') sat_rule (ord_rule,sel_index,sel_fact,sel_ord_data)
          ) sat_rules sel_fact

  and check_ord_rule seen_list ord_rule =
    let ana_hist_op = analysed_history_op_of_ordered_rule ord_rule in

    let sub_check rule =
      let rule' = elim_any_x (Database.remove_ground_public_terms (decompose_hyp_tuples rule)) in
      let ana_hist_op' = analyse_history ana_hist_op rule' in
      let ord_rule'' = ordered_rule_of_analysed_history_op ana_hist_op' rule' in
      let annot_ord_rule'' = Database.SubOrdClause.generate_subsumption_data ord_rule'' in
      let (r_implies,block_set_implies) = Database.SubOrdClause.implies_redundant annot_ord_rule'' annot_target_rule in
      if r_implies
      then raise Redundant
      else if block_set_implies
      then redundant_rec annot_ord_rule'' seen_list
    in

    simplify_rule_constra sub_check sub_check ord_rule.rule
  in

  let apply ({ rule = (_, first_concl, _, _); _ } as first_rule) =
    try
      let init_rule =
        auto_cleanup (fun () ->
          Terms.match_facts first_concl target_concl;
          { first_rule with rule = copy_rule2 first_rule.rule }
        )
      in
      check_ord_rule [] init_rule;
      false
    with NoMatch -> false
  in

  try
    Database.SetOrdClause.exists apply first_rule_set
  with
    | Redundant ->
        if !Param.verbose_redundant then
          begin
            print_string "Redundant rule eliminated:\n";
            Display.Text.display_ordered_rule_indep target_rule
          end;
        true

let redundant_glob database annot_initrule =
  !Param.redundancy_test <> Param.NoRed && redundant database.Database.DB.base_ns annot_initrule

let redundant_glob_solving database sat_rules annot_target_rule =
  !Param.redundancy_test <> Param.NoRed && redundant_solving sat_rules database.Database.DBOrd.base_ns annot_target_rule

let redundant_final_solving database sat_rules =
  if !Param.redundancy_test = Param.BestRed
  then
    Database.SetOrdClause.iter (fun elt ->
      (* By deactivating the clause, the application of [redundant rulelist' elt.sub_data elt.clause] will behave
         as if the rule elt.clause was not in the list [rulelist']. *)
      Database.SetOrdClause.deactivate database.Database.DBOrd.base_ns elt;

      (* If the clause is redundant, we leave it deactivated which corresponds to removing it from the database.
         Hence, if the clause is not redundant, it is important to reactivate it! *)
      if not (redundant_solving sat_rules database.Database.DBOrd.base_ns elt.Database.SetOrdClause.annot_clause)
      then Database.SetOrdClause.activate database.Database.DBOrd.base_ns elt;
    ) database.Database.DBOrd.base_ns

(* Saturates the rule base, by repeatedly applying the composition [compos] *)

let complete_rules database lemmas inductive_lemmas =
  let normal_rule = normal_rule database lemmas inductive_lemmas in
  let rec search_fix_point () = match Database.QueueClause.get database.Database.DB.queue with
    | None ->
        Display.stop_dynamic_display ();
        Database.SetClause.to_list database.Database.DB.base_ns
    | Some ((((hyp,concl,_,_) as rule), _, sub_data) as annot_rule) ->
        let sel_index = Selfun.selection_fun rule in

        if sel_index == -1
        then
          begin
            if not (redundant_glob database (rule, sub_data))
            then
              begin
                let is_unselectable = List.for_all is_unselectable hyp in
                (* Consider only clauses with unselectable hypotheses in redundancy
                   to help termination of the search for a derivation.
                   (In general, the termination of resolution is not guaranteed.
                   With this condition, the facts usable by resolution
                   are smaller in the hypothesis than in the conclusion, which implies termination.) *)
                Database.SetClause.add database.Database.DB.base_ns annot_rule concl is_unselectable;
                Database.DB.display_dynamic_statistics database;
                Database.SetClause.iter_unifiable (fun elt ->
                  let (elt_clause,_) = elt.annot_clause in
                  compos normal_rule rule elt_clause (elt.additional_data,elt.selected_fact)
                  ) database.Database.DB.base_sel concl;
              end
          end
        else
          begin
            let sel_fact = List.nth hyp sel_index in

            Database.SetClause.add database.Database.DB.base_sel annot_rule sel_fact sel_index;
            Database.DB.display_dynamic_statistics database;
            Database.SetClause.iter_unifiable (fun ns_elt ->
              let (ns_elt_clause,_) = ns_elt.annot_clause in
              compos normal_rule ns_elt_clause rule (sel_index,sel_fact)
            ) database.Database.DB.base_ns sel_fact;
          end;

        Database.DB.display_rule_during_completion database (rule,sel_index);
        search_fix_point ()
  in
  search_fix_point ()

let complete_rules_solving ?(apply_not=false) sat_rules sat_rules_for_redundant_glob database lemmas inductive_lemmas =
  let normal_rule = normal_rule_solving apply_not database lemmas inductive_lemmas in

  let rec search_fix_point () = match Database.QueueOrdClause.get database.Database.DBOrd.queue with
    | None ->
        Display.stop_dynamic_display ();
        redundant_final_solving database sat_rules_for_redundant_glob;
        Database.SetOrdClause.to_list database.Database.DBOrd.base_ns
    | Some ((ord_rule,feature_vector,imp_data) as annot_ord_rule) ->
        let (sel_index,(({ rule = (_,concl,_,_); _} as ord_rule1,_,sub_data1) as annot_ord_rule1)) =
          let (hyp, _, hist, constra) = ord_rule.rule in
          let sel_index = Selfun.selection_fun (hyp, Param.dummy_fact, hist, constra) in
          if sel_index == -1
          then
            match ord_rule.order_data with
              | None -> sel_index, annot_ord_rule
              | Some order_data ->
                  let (hypl,_,_,_) = ord_rule.rule in
                  let (sel_index', order_data') = Selfun.selection_with_ignore_nounif hypl order_data in
                  (sel_index',({ ord_rule with order_data = Some order_data'}, feature_vector, imp_data))
          else sel_index, annot_ord_rule
        in

        if sel_index == -1
        then
          begin
            if not (redundant_glob_solving database sat_rules_for_redundant_glob (ord_rule1, sub_data1))
            then
              (* The boolean here as no value here. *)
              Database.SetOrdClause.add database.Database.DBOrd.base_ns annot_ord_rule1 concl true;
              Database.DBOrd.display_dynamic_statistics database;
          end
        else
          begin
            let (hyp, _, _, _) = ord_rule1.rule in
            let sel_fact = List.nth hyp sel_index in
            let sel_ord_data = match ord_rule1.order_data with
              | None -> None
              | Some ord_data -> Some (List.nth ord_data sel_index)
            in
            Database.SetOrdClause.add database.Database.DBOrd.base_sel annot_ord_rule1 sel_fact sel_index;
            Database.DBOrd.display_dynamic_statistics database;
            Database.SetSatClause.iter_unifiable (fun sat_rule -> compos_solving normal_rule sat_rule (ord_rule1,sel_index,sel_fact,sel_ord_data)) sat_rules sel_fact
          end;

        Database.DBOrd.display_rule_during_completion database (ord_rule1,sel_index);
        search_fix_point ()
  in
  search_fix_point ()

(* Solving request rule *)

let saturated_rules = ref []
let set_saturated_rules = ref Database.SetSatClause.empty
let set_saturated_rules_for_redundant_glob = ref Database.SetSatClause.empty

let rec generate_initial_ord acc= function
  | 0 -> acc
  | n -> generate_initial_ord ([Leq,n]::acc) (n-1)

let solving_request_rule ?(close_equation=true) ?(apply_not=false) lemmas inductive_lemmas ord_rule =
  assert (!initialized);

  let database = Database.DBOrd.create () in

  let close_eq =
    if close_equation
    then TermsEq.close_rule_hyp_eq
    else (fun restwork r -> restwork r)
  in

  close_eq (fun rule ->
    let ord_rule2 = { ord_rule with rule = rule } in
    normal_rule_solving apply_not database lemmas inductive_lemmas ord_rule2
  ) ord_rule.rule;

  complete_rules_solving ~apply_not:apply_not !set_saturated_rules !set_saturated_rules_for_redundant_glob database lemmas inductive_lemmas

(* Main functions *)

(* Only used in query_goal and query_goal_not. *)
let query_goal_std lemmas g =
  let ord_rule = { rule = ([g], g, Empty(g),true_constraints); order_data = None } in
  solving_request_rule lemmas [] ord_rule

(* Only used for Horn and typed Horn front-ends *)
let query_goal g =
  match query_goal_std [] g with
    [] ->
      print_string "RESULT goal unreachable: ";
      Display.auto_cleanup_display (fun () -> Display.Text.display_fact g);
      Display.Text.newline();
      if !Param.html_output then
        begin
          Display.Html.print_string "<span class=\"result\">RESULT <span class=\"trueresult\">goal unreachable</span>: ";
          Display.auto_cleanup_display (fun () -> Display.Html.display_fact g);
          Display.Html.print_string "</span>";
          Display.Html.newline();
        end
  | l ->
      List.iter (fun ord_rule ->
        Display.auto_cleanup_display (fun () ->
          print_string "goal reachable: ";
          Display.Text.display_rule_abbrev ord_rule.rule;
          if !Param.html_output then
            begin
              Display.Html.print_string "goal reachable: ";
              Display.Html.display_rule_abbrev ord_rule.rule
            end;
          begin
            try
              ignore (History.build_history None ord_rule.rule)
            with Not_found -> ()
          end;
          cleanup()
            )
      ) l;
      print_string "RESULT goal reachable: ";
      Display.auto_cleanup_display (fun () -> Display.Text.display_fact g);
      Display.Text.newline();
      if !Param.html_output then
        begin
          Display.Html.print_string "<span class=\"result\">RESULT <span class=\"unknownresult\">goal reachable</span>: ";
          Display.auto_cleanup_display (fun () -> Display.Html.display_fact g);
          Display.Html.print_string "</span>";
          Display.Html.newline();
        end

let query_goal_not lemmas g =
  match query_goal_std lemmas g with
    [] ->
      print_string "ok, secrecy assumption verified: fact unreachable ";
      Display.auto_cleanup_display (fun () -> Display.Text.display_fact g);
      Display.Text.newline();
      if !Param.html_output then
        begin
          Display.Html.print_string "ok, secrecy assumption verified: fact unreachable ";
          Display.auto_cleanup_display (fun () -> Display.Html.display_fact g);
          Display.Html.newline()
        end
  | l ->
      List.iter (fun ord_rule ->
        Display.auto_cleanup_display (fun () ->
          print_string "goal reachable: ";
          Display.Text.display_rule_abbrev ord_rule.rule;
          if !Param.html_output then
            begin
              Display.Html.print_string "goal reachable: ";
              Display.Html.display_rule_abbrev ord_rule.rule
            end;
          begin
            try
              ignore (History.build_history None ord_rule.rule)
            with Not_found -> ()
          end;
          cleanup()
            )
          ) l;
        if !Param.html_output then
        Display.Html.print_line "Error: you have given a secrecy assumption that I could not verify.";
      (* TO DO close HTML files properly before this error *)
      Parsing_helper.user_error "you have given a secrecy assumption that I could not verify."

let completion lemmas inductive_lemmas clauses =
  (* Reinit the rule database *)
  let database = Database.DB.create () in

  let (display_header,display_footer) =
    if !Param.html_output
    then
      begin
        let qs =
          if !is_inside_query then
            "inside" ^ (string_of_int (!Param.inside_query_number))
          else
            (string_of_int (!Param.current_query_number))
        in
        (fun () ->
          Display.LangHtml.openfile ((!Param.html_dir) ^ "/clauses" ^ qs ^ ".html") ("ProVerif: clauses for query " ^ qs);
          Display.Html.print_string "<H1>Initial clauses</H1>\n";
          Display.Html.display_start_list ();
        ), (fun () ->
          Display.Html.display_end_list ();
          Display.LangHtml.close();
          Display.Html.print_string ("<A HREF=\"clauses" ^ qs ^ ".html\" TARGET=\"clauses\">Clauses</A><br>\n")
        )
      end
    else if (!Param.verbose_explain_clauses != Param.NoClauses) || (!Param.explain_derivation = false)
    then
      (fun () ->
        Display.Text.print_string "Initial clauses:";
        Display.Text.display_start_list ()
      ), Display.Text.display_end_list
    else (fun () -> ()), (fun () -> ())
  in

  let display_one_initial_clause rule =
    if !Param.html_output
    then Display.Html.display_rule_num_abbrev rule
    else if (!Param.verbose_explain_clauses != Param.NoClauses) || (!Param.explain_derivation = false)
    then 
      begin 
        Display.stop_dynamic_display ();
        Display.Text.display_rule_num_abbrev rule
      end
  in

  let complete_with_equations rulelist =
    print_string "Completing with equations...\n";
    List.iter (fun rule ->
      if !Param.verbose_rules then
        begin
	  Display.stop_dynamic_display ();
          print_string "Completing ";
          Display.Text.display_rule_indep rule
        end
      else
        begin
          database.count <- database.count + 1;
          if database.count mod 200 = 0 then
            begin
	      Display.stop_dynamic_display ();
              print_string ((string_of_int database.count) ^ " rules completed.");
              Display.Text.newline()
            end
        end;
      TermsEq.close_rule_eq (normal_rule database lemmas inductive_lemmas) (copy_rule rule)
    ) rulelist;

    Display.stop_dynamic_display ();

    (* Convert the queue of rules into a list, to display it *)
    let rulelisteq =
      let l = ref [] in
      Database.QueueClause.iter (fun (r,_,_) -> l := r::(!l)) database.Database.DB.queue;
      !l
    in
    if !Param.html_output then
      begin
        Display.LangHtml.openfile ((!Param.html_dir) ^ "/eqclosure.html") "ProVerif: clauses completed with equations";
        Display.Html.print_string "<H1>Clauses completed with equations</H1>\n";
        Display.Html.display_item_list (fun r -> Display.auto_cleanup_display (fun () -> Display.Html.display_rule_nonewline r)) rulelisteq;
        Display.LangHtml.close();
        Display.Html.print_string "<A HREF=\"eqclosure.html\">Clauses completed with equations</A><br>\n"
      end
    else if !Param.verbose_completed then
      begin
        Display.Text.print_string "Clauses completed with equations:";
        Display.Text.display_item_list (fun r -> Display.auto_cleanup_display (fun () -> Display.Text.display_rule_nonewline r)) rulelisteq
      end
  in


  begin match clauses with
    | Given rulelist ->
        display_header ();
        List.iter display_one_initial_clause rulelist;
        display_footer ();

        if (!close_with_equations) && (TermsEq.hasEquations())
        then complete_with_equations rulelist
        else List.iter (normal_rule database lemmas inductive_lemmas) rulelist;
    | ToGenerate(rulelist_attacker,generate_process_rules) ->
        assert (!close_with_equations = false);
        Display.Text.print_line "Translating the process into Horn clauses...";
        display_header ();
        let display_and_normalise rule =
          Terms.auto_cleanup (fun () ->
            display_one_initial_clause rule;
            normal_rule database lemmas inductive_lemmas rule
          )
        in
        List.iter display_and_normalise rulelist_attacker;
        generate_process_rules display_and_normalise;
        display_footer ()
  end;


  Display.stop_dynamic_display ();

  (* Initialize the selection function *)
  Selfun.guess_no_unif database.queue;

  (* Display initial queue *)
  if !Param.verbose_base
  then Database.DB.display_initial_queue database;

  (* Complete the rule base *)
  print_string "Completing...\n";
  let completed_rules = complete_rules database lemmas inductive_lemmas in
  if !Param.html_output then
    begin
      let qs =
        if !is_inside_query then
          "inside" ^ (string_of_int (!Param.inside_query_number))
        else
          string_of_int (!Param.current_query_number)
      in
      Display.LangHtml.openfile ((!Param.html_dir) ^ "/compclauses" ^ qs ^ ".html") ("ProVerif: completed clauses for query " ^ qs);
      Display.Html.print_string "<H1>Completed clauses</H1>\n";
      Display.Html.display_item_list (fun r -> Display.auto_cleanup_display (fun () -> Display.Html.display_rule_nonewline r)) completed_rules;
      Display.LangHtml.close();
      Display.Html.print_string ("<A HREF=\"compclauses" ^ qs ^ ".html\">Completed clauses</A><br>\n")
    end
  else if !Param.verbose_completed then
    begin
      Display.Text.print_string "Completed clauses:";
      Display.Text.display_item_list (fun r -> Display.auto_cleanup_display (fun () -> Display.Text.display_rule_nonewline r)) completed_rules
    end;

  (* Initialise the ordered rules for the base *)
  let sat_rules = List.map saturated_reduction_of_reduction completed_rules in
  let sat_rules_for_redundant_glob =
    List.filter (fun sat_rule ->
      let (hyp1, _, _, _) = sat_rule.sat_rule in
      List.for_all is_unselectable hyp1
    ) sat_rules
  in
  saturated_rules := sat_rules;
  set_saturated_rules := Database.SetSatClause.of_list sat_rules;
  set_saturated_rules_for_redundant_glob := Database.SetSatClause.of_list sat_rules_for_redundant_glob;

  (* Verify the secrecy assumptions *)
  List.iter (query_goal_not lemmas) (!not_set)

let initialize state =
  initialized := true;
  saturated_rules := [];
  set_saturated_rules := Database.SetSatClause.empty;
  set_saturated_rules_for_redundant_glob := Database.SetSatClause.empty;
  not_set := state.h_not;
  elimtrue_set := state.h_elimtrue;
  initialise_pred_to_prove state.h_pred_prove;
  initialise_useless_events_for_lemmas state.h_event_in_queries state.h_lemmas;
  set_equiv state.h_equiv;
  Selfun.initialize state.h_nounif state.h_solver_kind;
  List.iter (fun r -> ignore (Selfun.selection_fun r)) state.h_clauses_to_initialize_selfun;
  Weaksecr.initialize state.h_solver_kind;
  Noninterf.initialize state.h_solver_kind;
  Database.FeatureGenClause.initialize ();
  Database.FeatureGenOrdClause.initialize ();
  (* This assertions aims to check that equations have already been
     recorded *)
  assert ((state.h_equations != []) = (TermsEq.hasEquations()));
  close_with_equations := state.h_close_with_equations;

  (* Display all lemmas *)
  if state.h_lemmas != []
  then
    begin
      if !Param.html_output then
        begin
          let qs =
            if !is_inside_query then
              "inside" ^ (string_of_int (!Param.inside_query_number))
            else
              (string_of_int (!Param.current_query_number))
          in
          Display.LangHtml.openfile ((!Param.html_dir) ^ "/lemmas" ^ qs ^ ".html") ("ProVerif: lemmas for the verification of query " ^ qs);
          Display.Html.print_string "<H1>Lemmas</H1>\n";
          Display.Html.display_lemmas state.h_lemmas;
          Display.LangHtml.close();
          Display.Html.print_string ("<A HREF=\"lemmas" ^ qs ^ ".html\" TARGET=\"lemmas\">Lemmas</A><br>\n")
        end
      else if !Param.verbose_lemmas || not !Param.explain_derivation then
        begin
          Display.Text.print_string "Lemmas used in the verification of the query:";
          Display.Text.display_lemmas state.h_lemmas
        end
    end

let corresp_initialize state =
  (* Main be used also for correspondence queries
     on biprocesses, so with Solve_Equivalence as well *)
  initialize state;

  (* We gather the lemmas *)
  let (lemmas,inductive_lemmas) =
    List.fold_left (fun (acc_l,acc_i) lem ->
      if lem.l_sat_app <> LANone
      then
        if lem.l_induction = None
        then (lem::acc_l,acc_i)
        else (acc_l,lem::acc_i)
      else (acc_l,acc_i)
    ) ([],[]) state.h_lemmas
  in

  completion lemmas inductive_lemmas state.h_clauses

  (* We allow subsequent calls to resolve_hyp, query_goal_std,
     sound_bad_derivable after this initialization and completion *)

let reset () =
  initialized := false;
  not_set := [];
  elimtrue_set := [];
  set_equiv [];
  Selfun.initialize [] Solve_Standard;
  Weaksecr.initialize Solve_Standard;
  Noninterf.initialize Solve_Standard;
  saturated_rules := [];
  set_saturated_rules := Database.SetSatClause.empty;
  set_saturated_rules_for_redundant_glob := Database.SetSatClause.empty;
  close_with_equations := false;
  reset_pred_to_prove ();
  events_only_for_lemmas := [];
  all_original_lemmas := []

let internal_bad_derivable lemmas rulelist =
  completion lemmas [] rulelist;
  List.filter (function
    | { sat_rule = (_, Pred(p, []), _, _); _} when p == Param.bad_pred -> true
    | _ -> false
  ) !saturated_rules

(* Test whether bad is derivable from rulelist;
   this function does not alter saturated_rules, so that it can be called
   even if I am calling query_goal_std afterwards to test whether some fact
   is derivable from other completed clauses.
   Furthermore, it is guaranteed to say that that bad is derivable only
   if it is actually derivable *)

let sound_bad_derivable lemmas rulelist =
  assert (!initialized);
  let old_saturated_rules = !saturated_rules in
  let old_set_sat_rules = !set_saturated_rules in
  let old_set_sat_rules_glob = !set_saturated_rules_for_redundant_glob in
  let old_sound_mode = !sound_mode in
  is_inside_query := true;
  sound_mode := true;
  let r = internal_bad_derivable lemmas (Given rulelist) in
  is_inside_query := false;
  sound_mode := old_sound_mode;
  saturated_rules :=  old_saturated_rules;
  set_saturated_rules := old_set_sat_rules;
  set_saturated_rules_for_redundant_glob := old_set_sat_rules_glob;
  List.map (fun sat_r -> sat_r.sat_rule) r

let bad_derivable state =
  assert (state.h_solver_kind <> Solve_Standard);
  initialize state;
  (* We gather the lemmas *)
  let lemmas =
    List.fold_left (fun acc_l lem ->
      if lem.l_sat_app <> LANone
      then
        begin
          if lem.l_induction <> None
          then internal_error "[rules.ml >> bad_derivable] There should not be any inductive lemma when proving equivalence.";
          (lem::acc_l)
        end
      else acc_l
    ) [] state.h_lemmas
  in
  let r = internal_bad_derivable lemmas state.h_clauses in
  reset();
  List.map (fun sat_r -> sat_r.sat_rule) r

let bad_in_saturated_database () =
  List.exists (function
    | { sat_rule = (_, Pred(p, []), _, _); _} when p == Param.bad_pred -> true
    | _ -> false
  ) !saturated_rules

let bad_in_saturated_database_opt () =
  match 
    List.find_opt (function
      | { sat_rule = (_, Pred(p, []), _, _); _} when p == Param.bad_pred -> true
      | _ -> false
	    ) !saturated_rules
  with
  | Some cl -> Some cl.sat_rule
  | None -> None

let main_analysis state goal_set =
  assert (state.h_solver_kind = Solve_Standard);
  initialize state;
  completion [] [] state.h_clauses;
  List.iter query_goal goal_set;
  reset()
