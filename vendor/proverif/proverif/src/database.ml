open Terms
open Types
open Pitypes

(** Subsumption of clauses w.r.t. to set and queue of clauses *)

(* [remove_ground_public_terms] removes attacker
   facts (including attackerbin and attacker guess) that
   contain only public ground terms. *)

(* All elements in hypl are public ground terms *)
let rec remove_sure_ground_public_terms accu hypl =
  List.fold_right (fun hyp1 (hypl,nl,histl) -> match hyp1 with
  | Pred(chann,((FunApp(f,_)::_) as l0)) ->
      let l = reorganize_fun_app f l0 in
      begin match History.get_rule_hist (RApplyFunc(f,chann)) with
      | Rule(_, _, hyp, _, _) as hist_dec ->
          remove_sure_ground_public_terms (hypl, nl+(List.length l)-1, (Resolution(hist_dec, nl, histl)))
            (List.map2 (fun (Pred(p',_)) x -> Pred(p', x)) hyp l)
      | _ -> Parsing_helper.internal_error "[rules.ml >> remove_sure_ground_public_terms] Unexpected history."
      end
  | _ -> Parsing_helper.internal_error "[rules.ml >> remove_sure_ground_public_terms] Unexpected terms."
	) hypl accu

let rec remove_ground_public_terms_rec accu hypl =
  List.fold_right (fun hyp1 (hypl,nl,histl) -> match hyp1 with
  | Pred(chann,t::q) ->
      if chann.p_prop land Param.pred_ATTACKER != 0 && is_ground_public t && List.for_all (equal_terms t) q
      then remove_sure_ground_public_terms (hypl,nl,histl) [hyp1]
      else (hyp1::hypl, nl-1, histl)
  | _ -> (hyp1::hypl, nl-1, histl)
	) hypl accu

let remove_ground_public_terms (hypl, concl, hist, constra) =
  let (hypl',_,histl') =
    remove_ground_public_terms_rec ([],(List.length hypl)-1,hist) hypl
  in
  (hypl',concl,histl',constra)

(* Raise NoMatch when the subsumption does not hold. *)
let rec implies_ordering_function (ord_fun1:ordering_function) (ord_fun2:ordering_function) =
  match ord_fun1, ord_fun2 with
  | [], _ -> ()
  | _, [] -> raise NoMatch
  | (i1,_)::q1, (i2,_)::q2 when i2 > i1 -> raise NoMatch
  | (i1,_)::q1, (i2,_)::q2 when i2 < i1 -> implies_ordering_function ord_fun1 q2
      (* At this point, both lists start with (i,_) for the same i *)
  | (_,Less)::q1, (_,Leq)::q2 -> raise NoMatch
  | _::q1, _::q2 -> implies_ordering_function q1 q2

(* Functions to compute the size of facts and terms.
   Follows links.*)

let rec term_size = function
  | Var { link = TLink t } -> term_size t
  | Var _ -> 0
  | FunApp(_,args) -> 1 + term_list_size args

and term_list_size = function
  | [] -> 0
  | a::l -> term_size a + term_list_size l

let fact_size = function
  | Pred(_,args) -> 1 + term_list_size args

(* Functions to compute the size of facts and terms.
   Records at the same time if there is a variable without link.
   Does not follow links.*)

let rec term_size_unbound has_unbound = function
  | Var v ->
      if v.link = NoLink
      then has_unbound := true;
      0
  | FunApp(_,args) -> 1 + term_list_size_unbound has_unbound args

and term_list_size_unbound has_unbound = function
  | [] -> 0
  | a::l -> term_size_unbound has_unbound a + term_list_size_unbound has_unbound l

let fact_size_unbound has_unbound = function
  | Pred(_,args) -> 1 + term_list_size_unbound has_unbound args

(* Addition in a sorted list of pairs, in decreasing order of the first component *)
let rec add_in_sorted_list n f l = match l with
  | [] -> [n,f]
  | (n',f')::q -> if n >= n' then (n,f)::l else (n',f')::(add_in_sorted_list n f q)

(********************************************
Check usage of may-fail variables and fail
*********************************************)

let rec check_no_fail = function
    Var v -> assert(not v.unfailing)
  | FunApp(f,l) ->
      assert(f.f_cat != Failure);
      List.iter check_no_fail l

let check_top_fail = function
    Var v -> ()
  | FunApp(f,l) -> List.iter check_no_fail l

let check_fact_fail = function
    Pred({p_info = TestUnifP _}, [t1;t2]) ->
      begin
        (* testunif: allow fail at the top, plus possibly inside a tuple *)
        match (t1,t2) with
          FunApp(f1,l1), FunApp(f2,l2) when f1 == f2 && f1.f_cat == Tuple ->
            List.iter check_top_fail l1;
            List.iter check_top_fail l2
        | _ ->
            check_top_fail t1;
            check_top_fail t2
      end
  | Pred(p,l) ->
      (* attacker predicates: allow fail at the top
         other predicates: don't allow fail at all *)
      begin
        match (unblock_predicate p).p_info with
          Attacker _ | AttackerBin _ | AttackerGuess _  (* attacker *) ->
            List.iter check_top_fail l
        | UserPred _ (* user-defined *)
        | OtherInternalPred (* event_pred, inj_event_pred, bad_pred, ... *)
        | Equal _ (* equal; used in user-defined clauses *)
        | Mess _ | InputP _ | OutputP _ | MessBin _ | InputPBin _
           | OutputPBin _ | Table _ | TableBin _ | Compromise _ | Combined _ | Subterm _  ->
            List.iter check_no_fail l
        | _ -> Parsing_helper.internal_error "Terms.check_rule: unexpected predicate info"
      end

let check_rule ((hyp, concl, hist, constra) as r) =
  try
    List.iter check_fact_fail hyp;
    check_fact_fail concl;
    iter_constraints check_no_fail constra
  with x ->
    Display.Text.display_rule_indep r;
    raise x

let check_rule_ordered ord_rule = check_rule ord_rule.rule

(***********************************
    Clauses
************************************)

module type ClauseSig =
  sig

    (* the type [hyp_fact] will correspond to either [Types.fact] in the case of a [reduction]
       or to [Types.fact * ordering_function] in the case of an [ordered_reduction] *)
    type hyp_fact

    type t

    val empty_clause : t

    val get_reduction : t -> reduction

    (* Must raise Terms.NoMatch when the facts cannot be matched.
       In the case of [ordered_reduction], [match_facts hfact1 hhfact2] it will also check that
       the ordering function of [hfact1] subsumes the ordering function of [hfact2]
    *)
    val match_facts : hyp_fact -> hyp_fact -> unit

    val fact_of_hyp_fact : hyp_fact -> fact

    val get_clause_with_hyp_fact : t -> (hyp_fact list * fact * history * constraints)

    (* [simplify_remove_hyp] simplifies a clause by removing some of its
       hypotheses, so that the obtained clause subsumes the original one.
       In practice, we remove attacker facts containing ground public terms *)
    val simplify_remove_hyp : t -> t

    val check : t -> unit

    val display : t -> unit

    val display_indep : t -> unit

    val display_hyp_fact : hyp_fact -> unit
  end

(***********************************
    Subsumption
************************************)

module type SubsumptionSig =
  sig
    type hyp_fact
    type clause

    type subsumption_data =
      {
        (* For an element (s,hfact) in the lists, [s] is the size of the fact of [hfact]. *)
        bound_facts : (int * hyp_fact) list; (* List are always kept in decreasing order w.r.t. the first projection of the pair *)
        unbound_facts : (int * hyp_fact) list (* List are always kept in decreasing order w.r.t. the first projection of the pair *)
      }

    type sub_annot_clause = clause * subsumption_data

    val empty_sub_data : subsumption_data
    val empty_sub_annot_clause : sub_annot_clause

   (* In the following functions, a clause can always be seen as its reduction part and its subsumption data part.
      For instance, when a clause is an ordered_reduction, the subsumption data contains the ordering function of the clause.

      For example, on a reduction R = (H && \phi -> C), the subsumption data [sub_data] of R is such that:
        - [sub_data.bound_facts] is the list of facts in H (with their size) that contains only variables of C
        - [sub_data.unbound_facts] are the remaining facts of H (with their size). Hence all facts in [sub_data.unbound_facts]
          contain a variable not in C.

      When R is an ordered reduction, it's similar except that [sub_data.bound_facts] and [sub_data.unbound_facts] also contain
      the ordering functions associated to the ordered facts in H.

      As mentioned above, [sub_data.bound_facts] and [sub_data.unbound_facts] are sorted by decreasing size.
    *)

    (* [implies r1 r2] returns true iff the rule [r1] implies/subsumes the rule [r2],
       where [r1] and [r2] are clauses with associated subsumption data. *)
    val implies : sub_annot_clause -> sub_annot_clause -> bool

    (* [implies_redundant r1 r2] returns a pair of booleans [(r_implies,block_set_implies)]
       where [r_implies] is true when [r1] implies/subsumes [r2]
       and [block_set_implies] is true when the blocking predicates part [Hblock1] of
       [r1 = Hblock1 && Hother1 -> C1] "subsumes" that part [Hblock2] of
       [r2 = Hblock2 && Hother2 -> C2], i.e. there exists a substitution [sigma] such that
       [sigma C1 = C2] and [sigma Hblock1 \subseteq Hblock2] for set inclusion.
       (When [block_set_implies] is false, subsumption cannot become true
       after future resolutions so we can cut this branch when we determine
       whether a clause is redundant.) *)
    val implies_redundant : sub_annot_clause -> sub_annot_clause -> bool * bool

    (* Similar to [implies] except that we do not apply an initial test on the number of hypotheses in the rule.
       This function is only used in combination with the feature vector. *)
    val implies_no_test : clause -> subsumption_data -> clause -> subsumption_data -> bool

    (* [generate_subsumption_data r] generates the subsumption data associated to [r]. *)
    val generate_subsumption_data : clause -> sub_annot_clause

  end

module MakeSubsumption (C:ClauseSig) =
  struct

    type hyp_fact = C.hyp_fact
    type clause = C.t

    type subsumption_data =
      {
        bound_facts : (int * hyp_fact) list;
        unbound_facts : (int * hyp_fact) list
      }

    type sub_annot_clause = clause * subsumption_data

    let empty_sub_data = { bound_facts = []; unbound_facts = [] }
    let empty_sub_annot_clause = (C.empty_clause, empty_sub_data)

    (* Functions matching hypotheses that only contain variables
       bound by the conclusion of the clause. *)

    (* [match_fact_bound_with_hyp size1 fact1 passed_hyp hyp2]
       raises [Terms.NoMatch] when the matching of [fact1] with any fact of [hyp2] fails,
       returns [hyp2'] when it succeeds, where [hyp2'] is the list of
       unused elements of [passed_hyp] and [hyp2].

       [size1] is the size of [fact1] including the links, i.e. [fact1\sigma] *)
    let rec match_fact_bound_with_hyp size1 fact1 passed_hyp = function
      | [] -> raise Terms.NoMatch
      | ((size2,fact2) as f2) :: fact_l2 ->
          (* Since [fact1] contains only variables from the conclusion, the instantiation of [fact1] must be
             equal to one of the facts in the hypotheses of the second clause. *)
          if size2 > size1
          then match_fact_bound_with_hyp size1 fact1 (f2::passed_hyp) fact_l2
          else if size2 = size1
          then
            try
              (* Since [fact1] is bound, the matching actually creates no link *)
              C.match_facts fact1 fact2;
              List.rev_append passed_hyp fact_l2
            with Terms.NoMatch ->
              match_fact_bound_with_hyp size1 fact1 (f2::passed_hyp) fact_l2
          else raise Terms.NoMatch

    let rec match_hyp_bound hyp1 hyp2_bound = match hyp1 with
      | [] -> hyp2_bound
      | (_,fact1) :: fact_l1 ->
          let size1 = fact_size (C.fact_of_hyp_fact fact1) in
          let hyp2_bound' = match_fact_bound_with_hyp size1 fact1 [] hyp2_bound in
          (* Success *)
          match_hyp_bound fact_l1 hyp2_bound'
          (* When [match_fact_bound_with_hyp size1 fact1 [] hyp2_bound] raises [NoMatch],
             [fact1] could not be matched with any fact in [hyp2_bound], we do not need to
             try the unbound hypotheses of clause 2 [hyp2_unbound] for the following reason.

             If we have a clause R1 = F1 ... -> C1 and F1 is bound and
             a clause R2 = F2 ... -> C2 where F2 is unbound. All
             variables of F1 are in C1. When we match C1 with C2, we
             obtain F1\sigma and all its variables are in C2. Now,
             since F2 is "unbound", F2 contains variables not in C2, so
             F2 cannot be equal to F1\sigma. Conclusion: it is enough
             to match "bound" facts of R1 with bound facts of R2.

             In this case, the whole function call raises [NoMatch]  *)

    (* Functions matching hypotheses that contain variables
       unbound by the conclusion of the clause. *)

    let rec match_fact_with_hyp nextf fact1 passed_hyp = function
      | [] -> raise Terms.NoMatch
      | ((_,fact2) as f2)::fact_l ->
          try
            Terms.auto_cleanup (fun () ->
              C.match_facts fact1 fact2;
              nextf (List.rev_append passed_hyp fact_l)
            )
          with Terms.NoMatch ->
            match_fact_with_hyp nextf fact1 (f2 :: passed_hyp) fact_l

    let rec match_hyp nextf hyp1 hyp2 = match hyp1 with
      | [] -> nextf ()
      | (_,fact1) :: fact_l1 -> match_fact_with_hyp (match_hyp nextf fact_l1) fact1 [] hyp2

    (* Main function for subsumption of two clauses. *)

    let implies_internal ((_,concl1,_,constr1):reduction) sub_data1 ((hyp2,concl2,_,constr2):reduction) sub_data2 =
      try
        Terms.auto_cleanup (fun () ->
          begin match concl1 with
            | Pred(p, []) when p == Param.bad_pred -> ()
            | _ -> Terms.match_facts concl1 concl2
          end;

          let r2_bound_facts = match_hyp_bound sub_data1.bound_facts sub_data2.bound_facts in
          (* All facts of [elt1.bound_facts] have been matched. *)
          match_hyp (fun () ->
            TermsEq.implies_constraints_keepvars3 (concl2 :: hyp2) constr2 constr1
              ) sub_data1.unbound_facts (r2_bound_facts @ sub_data2.unbound_facts);
          true
        )
      with Terms.NoMatch -> false

    let implies (cl1, sub_data1) (cl2, sub_data2) =
      let ((hyp1,_,_,_) as r1) = C.get_reduction cl1 in
      let ((hyp2,_,_,_) as r2) = C.get_reduction cl2 in
      if List.length hyp1 > List.length hyp2
      then false
      else implies_internal r1 sub_data1 r2 sub_data2

    let implies_no_test cl1 sub_data1 cl2 sub_data2 =
      let red1 = C.get_reduction cl1 in
      let red2 = C.get_reduction cl2 in
      implies_internal red1 sub_data1 red2 sub_data2

    (* Set Subsumption for the part of blocking predicates *)

    let is_blocking (Pred(p,_)) =
      p.p_prop land Param.pred_BLOCKING != 0

    let is_blocking_sub_data (_, f) =
      is_blocking (C.fact_of_hyp_fact f)

    let rec set_match_fact_bound_with_hyp size1 fact1 = function
      | [] -> raise Terms.NoMatch
      | (size2,fact2) :: fact_l2 ->
          (* Since [fact1] contains only variables from the conclusion, the instantiation of [fact1] must be
             equal to one of the facts in the hypotheses of the second clause. *)
          if size2 > size1
          then set_match_fact_bound_with_hyp size1 fact1 fact_l2
          else if size2 = size1
          then
            try
              (* Since [fact1] is bound, the matching actually creates no link *)
              C.match_facts fact1 fact2
            with Terms.NoMatch ->
              set_match_fact_bound_with_hyp size1 fact1 fact_l2
          else raise Terms.NoMatch

    let set_match_hyp_bound hyp1 hyp2_bound =
      List.iter (fun (_,hyp_fact1) ->
        let size1 = fact_size (C.fact_of_hyp_fact hyp_fact1) in
        set_match_fact_bound_with_hyp size1 hyp_fact1 hyp2_bound) hyp1

    let rec set_match_fact_with_hyp nextf fact1 = function
      | [] -> raise Terms.NoMatch
      | (_,fact2)::fact_l ->
          try
            Terms.auto_cleanup (fun () ->
              C.match_facts fact1 fact2;
              nextf ()
            )
          with Terms.NoMatch ->
            set_match_fact_with_hyp nextf fact1  fact_l

    let rec set_match_hyp nextf hyp1 hyp2 = match hyp1 with
      | [] -> nextf ()
      | (_,fact1) :: fact_l1 ->
          set_match_fact_with_hyp (fun () -> set_match_hyp nextf fact_l1 hyp2) fact1 hyp2

    let set_implies_block ((_,concl1,_,_):reduction) sub_data1 ((_,concl2,_,_):reduction) sub_data2 =
      try
        Terms.auto_cleanup (fun () ->
          begin match concl1 with
            | Pred(p, []) when p == Param.bad_pred -> ()
            | _ -> Terms.match_facts concl1 concl2
          end;

          let r1_bound = List.filter is_blocking_sub_data sub_data1.bound_facts in
          let r2_bound = List.filter is_blocking_sub_data sub_data2.bound_facts in
          set_match_hyp_bound r1_bound r2_bound;
          (* All facts of [r1_bound] have been matched. *)
          let r1_unbound = List.filter is_blocking_sub_data sub_data1.unbound_facts in
          let all_hyp2 = r2_bound @ List.filter is_blocking_sub_data sub_data2.unbound_facts in
          set_match_hyp (fun () -> ()) r1_unbound all_hyp2;
          true
        )
      with Terms.NoMatch -> false

    (* Mixed set and multiset subsumption for redundancy during solving *)

    (* The only difference with [match_fact_bound_with_hyp]
       is that it additionally returns the fact [f2] for which matching succeeds *)
    let rec mixed_match_fact_bound_with_hyp size1 fact1 passed_hyp = function
      | [] -> raise Terms.NoMatch
      | ((size2,fact2) as f2) :: fact_l2 ->
          (* Since [fact1] contains only variables from the conclusion, the instantiation of [fact1] must be
             equal to one of the facts in the hypotheses of the second clause. *)
          if size2 > size1
          then mixed_match_fact_bound_with_hyp size1 fact1 (f2::passed_hyp) fact_l2
          else if size2 = size1
          then
            try
             C.match_facts fact1 fact2;
             (f2, List.rev_append passed_hyp fact_l2)
            with Terms.NoMatch ->
              mixed_match_fact_bound_with_hyp size1 fact1 (f2::passed_hyp) fact_l2
          else raise Terms.NoMatch

    (* The only difference with [match_fact_with_hyp]
       is that it passes the fact [f2] for which matching succeeds
       to [next_f] *)
    let rec mixed_match_fact_with_hyp nextf fact1 passed_hyp = function
      | [] -> raise Terms.NoMatch
      | ((_,fact2) as f2)::fact_l ->
          try
            Terms.auto_cleanup (fun () ->
              C.match_facts fact1 fact2;
              nextf f2 (List.rev_append passed_hyp fact_l)
            )
          with Terms.NoMatch ->
            mixed_match_fact_with_hyp nextf fact1 (f2 :: passed_hyp) fact_l

    let mixed_implies_internal ((_,concl1,_,constr1):reduction) sub_data1 ((hypl2,concl2,_,constr2):reduction) sub_data2 =

      let result_set_implies = ref false in


      let r2_bound_block = List.filter is_blocking_sub_data sub_data2.bound_facts in
      let (r2_unbound_block, r2_unbound_unblock) =
        List.partition is_blocking_sub_data sub_data2.unbound_facts
      in
      let (r1_unbound_block, r1_unbound_unblock) =
        List.partition is_blocking_sub_data sub_data1.unbound_facts
      in
      let all_hyp2 = r2_bound_block @ r2_unbound_block in

      let set_match_bound hyp1 =
        set_match_hyp_bound hyp1 r2_bound_block;
        (* All facts of [elt1.bound_facts] have been matched. *)
        set_match_hyp (fun () -> result_set_implies := true) r1_unbound_block all_hyp2
      in

      let set_match hyp1 = set_match_hyp (fun () -> result_set_implies := true) hyp1 all_hyp2 in

      let rec mixed_match_hyp_bound hyp1 matched2 hyp2_bound = match hyp1 with
      | [] -> hyp2_bound
      | (_,hyp_fact1) :: fact_l1 ->
          let fact1 = C.fact_of_hyp_fact hyp_fact1 in
          let size1 = fact_size fact1 in
          let (fact2, hyp2_bound') =
            try
              mixed_match_fact_bound_with_hyp size1 hyp_fact1 [] hyp2_bound
            with Terms.NoMatch ->
              (* The multiset subsumption failed so we check the set subsumption *)
              if is_blocking fact1
              then set_match_fact_bound_with_hyp size1 hyp_fact1 (List.filter is_blocking_sub_data matched2);
              set_match_bound (List.filter is_blocking_sub_data fact_l1);
              raise Terms.NoMatch
          in
          (* Success *)
          mixed_match_hyp_bound fact_l1 (fact2::matched2) hyp2_bound'

      in

      (* Only applied to blocking facts *)
      let rec mixed_match_hyp nextf hyp1 matched2 hyp2 = match hyp1 with
        | [] -> nextf ()
        | (_,fact1) :: fact_l1 ->
            try
              mixed_match_fact_with_hyp (fun fact2 hyp2' ->
                mixed_match_hyp nextf fact_l1 (fact2::matched2) hyp2'
                  ) fact1 [] hyp2
            with Terms.NoMatch ->
              (* The multiset subsumption failed so we check the set subsumption *)
              if not !result_set_implies
              then set_match_fact_with_hyp (fun () -> set_match fact_l1) fact1 matched2;
              raise Terms.NoMatch
      in

      try
        Terms.auto_cleanup (fun () ->
          begin match concl1 with
            | Pred(p, []) when p == Param.bad_pred -> ()
            | _ -> Terms.match_facts concl1 concl2
          end;

          let r2_bound_facts = mixed_match_hyp_bound sub_data1.bound_facts [] sub_data2.bound_facts in
          (* All facts of [sub_data1.bound_facts] have been matched. *)
          let (r2_rem_bound_block, r2_rem_bound_unblock) =
            List.partition is_blocking_sub_data r2_bound_facts
          in
          let r2_block = r2_rem_bound_block @ r2_unbound_block in
          let r2_unblock = r2_rem_bound_unblock @ r2_unbound_unblock in
          let not_subsumed = List.length r1_unbound_unblock > List.length r2_unblock in
          mixed_match_hyp (fun () ->
            result_set_implies := true;
            if not_subsumed then
              raise NoMatch;
            match_hyp (fun () ->
              TermsEq.implies_constraints_keepvars3 (concl2 :: hypl2) constr2 constr1
                ) r1_unbound_unblock r2_unblock
              ) r1_unbound_block [] r2_block;
          (true,true)
        )
      with Terms.NoMatch -> (false,!result_set_implies)

    (* Specific function for subsumption of two clauses. Only used in redundancy.
       It returns two booleans [(r_implies,block_set_implies)], see interface of
       [implies_redundant] above.
     *)

    let nb_blocking_predicate =
      List.fold_left (fun acc_nb_block f ->
        if is_blocking f
        then acc_nb_block+1
        else acc_nb_block
            ) 0

    let implies_redundant (cl1, sub_data1) (cl2, sub_data2) =
      let ((hyp1,_,_,_) as r1) = C.get_reduction cl1 in
      let ((hyp2,_,_,_) as r2) = C.get_reduction cl2 in
      let nb_block1 = nb_blocking_predicate hyp1 in
      let nb_block2 = nb_blocking_predicate hyp2 in

      if (List.length hyp1 - nb_block1 > List.length hyp2 - nb_block2) || (nb_block1 > nb_block2)
      then
        (* Multiset subsumption is false *)
        if (nb_block1 <> 0 && nb_block2 = 0)
        then
          (* Set subsumption of blocking predicate is false *)
          (false,false)
        else if nb_block1 = 0
        then (false,true)
        else (false,set_implies_block r1 sub_data1 r2 sub_data2)
      else
        if nb_block1 = 0
        then implies_internal r1 sub_data1 r2 sub_data2, true
        else mixed_implies_internal r1 sub_data1 r2 sub_data2

    (* Function for computing the subsumption data of a clause. *)

    let generate_subsumption_data rule =
      let (hyp,concl,_,_) = C.get_clause_with_hyp_fact rule in

      Terms.auto_cleanup (fun () ->
        (* Mark variables in conclusion *)
        Terms.mark_variables_fact concl;

        (* We split the hypotheses in two lists depending on
           whether the fact has unbound variables or not. *)
        let unbound_facts = ref [] in
        let bound_facts = ref [] in

        List.iter (fun fact ->
          let has_unbound = ref false in
          let size = fact_size_unbound has_unbound (C.fact_of_hyp_fact fact) in
          if !has_unbound
          then unbound_facts := add_in_sorted_list size fact !unbound_facts
          else bound_facts := add_in_sorted_list size fact !bound_facts
               ) hyp;

        rule, { bound_facts = !bound_facts; unbound_facts = !unbound_facts })

  end

(***********************************
    Features
************************************)

(* Width of a symbol in a term:
    An occurrence of a symbol f in a term t is at width w if:
      - t = f(t_1,...,t_n) and w = 0
      - t = C[g(r_1,...,r_{i-1},f(t_1,...,t_n),r_{i+1},...,r_m)] and w = i
*)

(* We consider the following features for a clause H -> C and we explain their
   value v. Note that each recorded symbol and predicate has a unique non negative
   identifier (in f.f_record or p.p_record)
    - Bad : v = 0 when the conclusion is bad, otherwise v = 1
    - NbHyp : v = |H|, i.e. number of hypotheses
    - Occ i_f :
        if i_f < 0 then v = number of occurrences in the conclusion of a symbol
          f with identifier -i_f.
        if i_f > 0 then v = number of occurrences in the hypotheses of a symbol
          f with identifier i_f.
    - Depth(i_f,d) :
        if i_f < 0 then v = number of occurrences at depth d in the conclusion
          of a symbol f with identifier -i_f
        if i_f > 0 then v = number of occurrences at depth d in the hypotheses
          of a symbol f with identifier i_f
        if d = -1 then it records the maximal depth of symbol f
    - Width(i_f,w) :
        if i_f < 0 then v = number of occurrences at width w in the conclusion
          of a symbol f with identifier -i_f
        if i_f > 0 then v = number of occurrences at width w in the hypotheses
          of a symbol f with identifier i_f
    - CapAll : v = number of occurrence of all non-recorded symbols in the clause
*)

type feature =
  | Bad
  | NbHyp
  | Occ of int
  | Depth of int * int
  | Width of int * int
  | CapAll

(* We order the features as follows:
  -> Bad < Occ < NhHyp < Depth < Width < CapAll.
  -> Occ(i) < Occ(i') when i < i'
  -> Depth(i_f,d) < Depth(i_f',d') when i_f < i_f' or (i_f = i_f' and d < d')
  -> Width(i_f,w) < Width(i_f',w') when i_f < i_f' or (i_f = i_f' and w < w')
*)

(* We will always assume that a feature_vector is always ordered increasingly
   using the lexicographic order.

   The list represents all the non-zero values of the feature inside a feature vector.
   For example, assume that we have in total [5] features F_1 ... F_5 (according to the order,
   F_1 is Bad and F_2 is NbHyp).

   If a clause has as feature vector (0,2,1,0,3) then its representation would be:
    [(F_2,2);(F_3,1);(F_5,3)]
*)
type feature_vector = (feature * int) list

(***** Recording the function symbols and predicates *****)

(* Record functions *)

let record_counter = ref 0

let record_fun f =
  if !Param.record_funs && f.f_record <= 0
  then
    begin
      incr record_counter;
      f.f_record <- !record_counter
    end

let record_name f =
   if !Param.record_names && f.f_record <= 0
   then
     begin
       incr record_counter;
       f.f_record <- !record_counter
     end

let record_predicate p =
  if !Param.record_predicates && p.p_record == 0
  then
    begin
      incr record_counter;
      p.p_record <- !record_counter
    end

let record_event ev =
  if !Param.record_events && ev.f_record <= 0
  then
    begin
      incr record_counter;
      ev.f_record <- !record_counter
    end

let record_table t =
  if !Param.record_tables && t.f_record <= 0
  then
    begin
      incr record_counter;
      t.f_record <- !record_counter
    end

let get_root f_next t =
  try
    f_next (Terms.get_root t)
  with Not_found -> ()

let record_from_fact = function
  | Pred({ p_info = Table _},[t]) -> get_root record_table t
  | Pred({ p_info = TableBin _},[t1;t2]) ->
      get_root record_table t1;
      get_root record_table t2
  | Pred(p,[t]) when p == Param.event_pred_block || p == Param.event_pred ->
      get_root record_event t
  | Pred(p,[t1;t2]) when p == Param.event2_pred_block || p == Param.event2_pred ->
      get_root record_event t1;
      get_root record_event t2
  | Pred(p,[t;_]) when p == Param.inj_event_pred || p == Param.inj_event_pred_block ->
      get_root record_event t
  | Pred(p,_) -> record_predicate p

let record_from_rule (hypl,concl,_,_) = List.iter record_from_fact (concl::hypl)

(***** Comparison *****)

let compare_feature f1 f2 = match f1, f2 with
  | Bad, Bad -> 0
  | Bad, _ -> -1
  | _, Bad -> 1
  | Occ i, Occ i' -> i - i'
  | Occ _, _ -> -1
  | _, Occ _ -> 1
  | NbHyp, NbHyp -> 0
  | NbHyp, _ -> -1
  | _, NbHyp -> 1
  | Depth(i,d), Depth(i',d') -> let c = i - i' in if c = 0 then d - d' else c
  | Depth _, _ -> -1
  | _, Depth _ -> 1
  | Width(i,w), Width(i',w') -> let c = i - i' in if c = 0 then w - w' else c
  | Width _, _ -> -1
  | _, Width _ -> 1
  | _ -> 0

(***** Display *****)

let display_feature = function
  | Bad -> "Bad"
  | NbHyp -> "NbHyp"
  | Occ i -> Printf.sprintf "Occ %d" i
  | Depth(i,d) -> Printf.sprintf "Depth(%d,%d)" i d
  | Width(i,d) -> Printf.sprintf "Width(%d,%d)" i d
  | CapAll -> "CapAll"

let display_feature_vector =
  Display.Text.display_list (fun (v,i) -> Printf.printf "(%s,%d)" (display_feature v) i) ";"

(***** Generation of feature vector *****)

module Int =
  struct
    type t = int
    let compare x y = -(compare x y)
  end

module IMap = Tree.MakeOne(Int)

module type FeatureGenerationSig =
  sig
    type subsumption_data
    type clause
    type annot_clause = clause * feature_vector * subsumption_data

    (* [initialize ()] needs to be executed before starting saturating clauses. *)
    val initialize : unit -> unit

    val generate_feature_vector_and_subsumption_data : clause -> annot_clause
  end

module MakeFeatureGeneration (C:ClauseSig) (S:SubsumptionSig with type hyp_fact = C.hyp_fact and type clause = C.t) =
  struct

    type subsumption_data = S.subsumption_data
    type clause = C.t
    type annot_clause = clause * feature_vector * subsumption_data

    type generation_data =
      {
        mutable occ_hyp : int;
        mutable occ_concl : int;
        mutable max_depth_hyp : int;
        mutable max_depth_concl : int;
        mutable depth_hyp : int IMap.t;
        mutable depth_concl : int IMap.t;
        mutable width_hyp : int IMap.t;
        mutable width_concl : int IMap.t
      }

    let create_gen_data () =
      {
        occ_hyp = 0;
        occ_concl = 0;
        max_depth_hyp = 0;
        max_depth_concl = 0;
        depth_hyp = IMap.empty;
        depth_concl = IMap.empty;
        width_hyp = IMap.empty;
        width_concl = IMap.empty
      }

    (* The table represents the different elements for each symbol. *)
    let generation_data = ref (Array.make 0 (create_gen_data ()))
    let occ_non_recorded_symbol = ref 0
    let nb_hyp = ref 0
    let bad_not_in_concl = ref false

    let initialize () =
      if !Param.feature then
	begin
	  generation_data := Array.make !record_counter (create_gen_data ());
	  for i = 0 to !record_counter - 1 do
            !generation_data.(i) <- create_gen_data ()
	  done;
	  bad_not_in_concl := false;
	  occ_non_recorded_symbol := 0;
	  nb_hyp := 0
	end

    (* We generate the feature list from what was recorded *)
    let feature_vector_of_generation_data () =

      let feature_vector = ref [] in

      (* Capture All *)
      if !occ_non_recorded_symbol != 0
      then
        begin
          feature_vector := [CapAll,!occ_non_recorded_symbol];
          occ_non_recorded_symbol := 0
        end;

      (* Width *)
      if !Param.record_width
      then
        begin
          (* In hypotheses *)
          for i = !record_counter - 1 downto 0 do
            if not (IMap.is_empty !generation_data.(i).width_hyp)
            then
              begin
                IMap.iter (fun d n ->
                  feature_vector := (Width(i+1,d),n) :: !feature_vector
                ) !generation_data.(i).width_hyp;
                !generation_data.(i).width_hyp <- IMap.empty
              end
          done;

          (* In conclusion *)
          for i = 0 to !record_counter - 1 do
            if not (IMap.is_empty !generation_data.(i).width_concl)
            then
              begin
                IMap.iter (fun d n ->
                  feature_vector := (Width(-i-1,d),n) :: !feature_vector
                ) !generation_data.(i).width_concl;
                !generation_data.(i).width_concl <- IMap.empty
              end
          done;
        end;


      if !Param.record_depth
      then
        (* Full depth have been recorded *)
        begin
          (* In hypotheses *)
          for i = !record_counter - 1 downto 0 do
            if not (IMap.is_empty !generation_data.(i).depth_hyp)
            then
              begin
                IMap.iter (fun d n ->
                  feature_vector := (Depth(i+1,d),n) :: !feature_vector
                ) !generation_data.(i).depth_hyp;
                !generation_data.(i).depth_hyp <- IMap.empty
              end
          done;

          (* In conclusion *)
          for i = 0 to !record_counter - 1 do
            if not (IMap.is_empty !generation_data.(i).depth_concl)
            then
              begin
                IMap.iter (fun d n ->
                  feature_vector := (Depth(-i-1,d),n) :: !feature_vector
                ) !generation_data.(i).depth_concl;
                !generation_data.(i).depth_concl <- IMap.empty
              end
          done;
        end
      else
        (* Max Depth *)
        begin
          (* In hypotheses *)
          for i = !record_counter - 1 downto 0 do
            if !generation_data.(i).max_depth_hyp != 0
            then
              begin
                feature_vector := (Depth(i+1,-1),!generation_data.(i).max_depth_hyp) :: !feature_vector;
                !generation_data.(i).max_depth_hyp <- 0
              end
          done;

          (* In conclusion *)
          for i = 0 to !record_counter - 1 do
            if !generation_data.(i).max_depth_concl != 0
            then
              begin
                feature_vector := (Depth(-i-1,-1),!generation_data.(i).max_depth_concl) :: !feature_vector;
                !generation_data.(i).max_depth_concl <- 0
              end
          done
        end;

      (* NbHyp *)
      feature_vector := (NbHyp,!nb_hyp) :: !feature_vector;
      nb_hyp := 0;

      (* Occurrences in hypotheses *)
      for i = !record_counter - 1 downto 0 do
        if !generation_data.(i).occ_hyp != 0
        then
          begin
            feature_vector := (Occ(i+1),!generation_data.(i).occ_hyp) :: !feature_vector;
            !generation_data.(i).occ_hyp <- 0
          end
      done;

      (* Occurrences in conclusion *)
      for i = 0 to !record_counter - 1 do
        if !generation_data.(i).occ_concl != 0
        then
          begin
            feature_vector := (Occ(-i-1),!generation_data.(i).occ_concl) :: !feature_vector;
            !generation_data.(i).occ_concl <- 0
          end
      done;

      (* Bad *)
      if !bad_not_in_concl
      then
        begin
          feature_vector := (Bad,1) :: !feature_vector;
          bad_not_in_concl := false
        end;

      !feature_vector

    (*** Gather the data  ***)

    let f_update = function
      | None -> Some 1
      | Some n -> Some (n+1)

    let record_symbol_hyp f d w =
      let i = f.f_record - 1 in

      if !Param.record_depth
      then !generation_data.(i).depth_hyp <- IMap.update d f_update !generation_data.(i).depth_hyp
      else
        begin
          (* We do not record the full depth hence we only record occurrences
             and max_depth. *)
          !generation_data.(i).occ_hyp <- !generation_data.(i).occ_hyp + 1;
          !generation_data.(i).max_depth_hyp <- max !generation_data.(i).max_depth_hyp d;
        end;

      if !Param.record_width
      then !generation_data.(i).width_hyp <- IMap.update w f_update !generation_data.(i).width_hyp

    let record_symbol_concl f d w =
      let i = f.f_record - 1 in

      if !Param.record_depth
      then !generation_data.(i).depth_concl <- IMap.update d f_update !generation_data.(i).depth_concl
      else
        begin
          (* We do not record the full depth hence we only record occurrences
             and max_depth. *)
          !generation_data.(i).occ_concl <- !generation_data.(i).occ_concl + 1;
          !generation_data.(i).max_depth_concl <- max !generation_data.(i).max_depth_concl d;
        end;

      if !Param.record_width
      then !generation_data.(i).width_concl <- IMap.update w f_update !generation_data.(i).width_concl

    let rec feature_symbol_hyp has_unbound size depth width = function
      | Var { link = NoLink; _ } -> has_unbound := true
      | Var _ -> ()
      | FunApp({ f_type = (_,typ);_} as f, args) ->
          if f.f_record <= 0
          then incr occ_non_recorded_symbol (* [f] is non-recorded *)
          else if typ == Param.event_type || typ == Param.table_type
          then !generation_data.(f.f_record-1).occ_hyp <- !generation_data.(f.f_record-1).occ_hyp + 1
          else record_symbol_hyp f depth width;

          (* Increase size *)
          incr size;

          feature_symbol_hyp_list has_unbound size (depth+1) 1 args

    and feature_symbol_hyp_list has_unbound size depth width = function
      | [] -> ()
      | t::q ->
          feature_symbol_hyp has_unbound size depth width t;
          feature_symbol_hyp_list has_unbound size depth (width + 1) q

    let rec feature_symbol_concl depth width = function
      | Var ({ link = NoLink; _ } as v) -> Terms.link v (VLink v) (* Mark the variables*)
      | Var _ -> ()
      | FunApp({ f_type = (_,typ);_} as f, args) ->
          if f.f_record <= 0
          then incr occ_non_recorded_symbol (* [f] is non-recorded *)
          else if typ == Param.event_type || typ == Param.table_type
          then !generation_data.(f.f_record-1).occ_concl <- !generation_data.(f.f_record-1).occ_concl + 1
          else record_symbol_concl f depth width;

          feature_symbol_concl_list (depth+1) 1 args

    and feature_symbol_concl_list depth width = function
      | [] -> ()
      | t::q ->
          feature_symbol_concl depth width t;
          feature_symbol_concl_list depth (width + 1) q

    let generate_feature_vector_fact_concl = function
      | Pred(p,[]) when p == Param.bad_pred -> ()
      | Pred(p,args) ->
          (* Feature_bad *)
          bad_not_in_concl := true;

          (* Feature occurrence, depth and width for function symbol *)
          feature_symbol_concl_list 1 1 args;

          (* Feature occurrence for predicate *)
          if p.p_record != 0
          then !generation_data.(p.p_record - 1).occ_concl <- !generation_data.(p.p_record - 1).occ_concl + 1

    let generate_feature_vector_fact_hyp = function
      | Pred(p,args) ->
          (* Feature number hypotheses *)
          incr nb_hyp;

          (* Feature occurrence, depth and width for function symbol *)
          let size = ref 1 in
          let has_unbound = ref false in
          feature_symbol_hyp_list has_unbound size 1 1 args;

          (* Feature occurrence for predicate *)
          if p.p_record != 0
          then !generation_data.(p.p_record - 1).occ_hyp <- !generation_data.(p.p_record - 1).occ_hyp + 1;

          (!size,!has_unbound)

    let generate_feature_vector_and_subsumption_data (rule:C.t) =
      if !Param.feature then
	begin
          (* The feature table should be clean at that stage as well as
             occurrence_non_recorded_symbol and bad_in_conclusion *)

	  let (hyp,concl,_,_) = C.get_clause_with_hyp_fact rule in

	  let subsumption_data =
	    Terms.auto_cleanup (fun () ->
              (* Go through conclusion. Note that the variables are marked. *)
	      generate_feature_vector_fact_concl concl;

              (* Go through hypotheses: We split the hypotheses in two lists depending on
		 whether the fact has unbound variables or not. *)
	      let unbound_facts = ref [] in
	      let bound_facts = ref [] in

	      List.iter (fun fact ->
		let (size,has_unbound_vars) = generate_feature_vector_fact_hyp (C.fact_of_hyp_fact fact) in
		if has_unbound_vars
		then unbound_facts := add_in_sorted_list size fact !unbound_facts
		else bound_facts := add_in_sorted_list size fact !bound_facts
		     ) hyp;

	      { S.bound_facts = !bound_facts; S.unbound_facts = !unbound_facts }
		)
	  in

          (* Generate the feature vector *)

	  rule, feature_vector_of_generation_data (), subsumption_data
	end
      else
	begin
	  let (rule, sub_data) = S.generate_subsumption_data rule in
	  (rule, [], sub_data)
	end

  end

(***********************************
    Feature Trie
************************************)

module FeatureTrie =
  struct

    module FV =
      struct
        type t_fst = feature
        type t_snd = int
        type t = t_fst * t_snd

        let compare_fst fe1 fe2 = - (compare_feature fe1 fe2)
        let compare_snd = compare
      end

    module FVTree = Tree.Make(FV)

    type 'a t =
      | Node of 'a t FVTree.t * 'a list
      | Empty

    let empty = Empty

    let create elt (fe_vec:feature_vector) =

      let rec create_trie = function
        | [] -> Node (FVTree.empty,[elt])
        | fev :: q_vec ->
            let trie = create_trie q_vec in
            Node (FVTree.singleton fev trie, [])
      in

      create_trie fe_vec

    let add t elt (fe_vec:feature_vector) =

      let rec explore_tree t fe_vec = match t, fe_vec with
        | Empty, _ -> create elt fe_vec
        | Node(fe_map,elt_l), [] -> Node(fe_map,elt::elt_l)
        | Node(fe_map,elt_l), fe::q_vec ->
            let fe_map' =
              FVTree.update fe (function
                | None ->
                    (* The feature is not present in the map *)
                    Some (create elt q_vec)
                | Some t' ->
                    (* The feature is present in the map *)
                    Some (explore_tree t' q_vec)
              ) fe_map
            in
            Node(fe_map',elt_l)
      in

      explore_tree t fe_vec

    (* [exists_leq p fe_vec t] returns true if there exists an element of [t] with
       feature vector less or equal to [fe_vec] that satisfies the predicate [p] *)
    let rec exists_leq p fe_vec t = match t, fe_vec with
      | Empty, _ -> false
      | Node(_,elt_l), [] ->
          (* Only the elements with empty feature vector can be less or equal *)
          List.exists p elt_l
      | Node(fe_map,elt_l), (fe,v)::q_vec ->
          (* Since feature_vector are always sorted in increasing order w.r.t. compare_feature, we have
             that [fe_vec] is sorted in decreasing order w.r.t. FV.compare_fst.

             Since we need to find the element with a feature vector [fe_vect'] smaller than [fe_vec],
             we deduce that [fe_vect'] starts with (fe',v') with either
             - fe' = fe but v' <= v : In that case, we compare the rest of the feature_vector [q_vec] with
               the elements associated to [(fe',v')] in [fe_map].
             - fe' > fe : Note that in full representation, fe' > fe implies that the value of fe on the
               elements associated to [(fe',v')] in [fe_map] is necessary 0. Note that fe' > fe implies fe' is
               strictly smaller than fe w.r.t. FV.compare_fst
             - The case fe' < fe is impossible as it would imply that the value of fe' on t would be 0
               and so the feature vector of all elements associated to fe_map would not be smaller than
               [fe_vec].
          *)
          (* We need to look in fe_map the branches that have a feature smaller than fe. *)

          (* The elements with no positive features are smaller *)
          List.exists p elt_l || FVTree.exists_leq (exists_leq p) (fe,v) q_vec fe_map

    let rec iter f_iter = function
      | Empty -> ()
      | Node(fe_map,elt_l) ->
          List.iter f_iter elt_l;
          FVTree.iter (iter f_iter) fe_map

    let rec iter_geq f_iter fe_vec t = match t, fe_vec with
      | _, [] ->
          (* All elements of the trie have a feature vector bigger than fe_vec *)
          iter f_iter t
      | Empty, _ -> ()
      | Node(fe_map,_), (fe,v)::q_vec ->
          (* The elements with no positive features are strictly smaller hence
             we do not apply [f_iter] on them. *)
          FVTree.iter_geq (iter_geq f_iter fe_vec) (iter_geq f_iter q_vec) (fe,v) fe_map

    let rec filter f = function
      | Empty -> Empty
      | Node(fe_map,elt_l) ->
          let elt_l' = List.filter f elt_l in
          let fe_map' =
            FVTree.update_all (fun t ->
              match filter f t with
                | Empty -> None
                | t' -> Some t'
            ) fe_map
          in
          if elt_l' = [] && FVTree.is_empty fe_map'
          then Empty
          else Node(fe_map',elt_l')
  end

(***********************************
    Unification Trie
************************************)

module UnificationTrie =
  struct

    module FunSymb =
      struct
        type t = funsymb
        let compare f1 f2 = compare f1.f_record f2.f_record
      end

    module FMap = Tree.MakeOne(FunSymb)

    (* The unification tree stores the clauses.
       Each clause H -> C is associated with a fact p(t1,...,tn) that will be used for unification
       in the composition rule, i.e. the selected fact in H->C.
       A tree represents all clauses where the selected facts have the same predicate. (Hence we will
       store one tree for each predicate, e.g. att, mess, table, etc.)
       The tree has leaves labeled by sets of clauses and edges labeled by function symbols and
       a special symbol for variables (let's denote it X).
       If the clause H->C with selected fact p(t1,...,tn) is stored in the label of a leaf then the labels
       along the branch leading to this leaf corresponds to the depth-first search exploration
       of the arguments [t1,...,tn].

       For example, a clause H->C with selected fact att(f(a[],g(c[],d[]))), the branch to the leaf
       storing H->C will be labeled by f -> a -> g -> c -> d.

       Handling variables and limiting the depth of terms:
       When the selected fact contains variables, we don't create different branch for each different
       variable. Similarly, to avoid having too large branches when the working with large terms,
       we limit the depth of our depth-first search exploration.

       Formally, given a selected fact p(t1,...,tn), we generate its representatives by replacing every
       variables in p(t1,...,tn) by X and by replacing every term in p(t1,...,tn) at depth [max_depth]
       by X.

       For example, if [max_depth = 4] then the representative of att(f(y,z,g(c[],h(d[])))) is
       att(f(X,X,g(c[],h(X)))). Thus the clause will be stored in the leaf with the branch:
       f -> X -> X -> g -> c -> h -> X.

       Note that clauses with the same representative are necessary stored in the same leaf.

       In the following structure and in particular if [Node of 'a t option * 'a t FMap.t],
       the ['a t option] represents the son whose edge is labeled by the special symbol X.
       The ['a t FMap.t] represents the sons whose edges are labeled by a standard function symbol.

       When looking to unify a fact F with selected facts of the clauses in the tree, we will look
       at those whose representive can be unified with F, considing every instance of X in the
       representative as a distinct variable.

       Coming back to our example, the representive for unification will be att(f(x1,x2,g(c[],h(x3)))).
     *)

    type 'a t =
      | Leaf of 'a list
      | Node of 'a t option * 'a t FMap.t

    let empty = Leaf []

    let is_empty = function
      | Leaf [] -> true
      | _ -> false

    (* [generate_branch f_next prev_tree d t] generates a branch corresponding
       to the representative of term [t] and plugs [prev_tree] at the end of this
       branch. The resulting tree is given to [f_next] as argument. *)
    let rec generate_branch f_next prev_tree d = function
      | Var _ -> f_next (Node (Some prev_tree,FMap.empty))
      | FunApp _ when d = !Param.unify_trie_term_max_depth -> f_next (Node (Some prev_tree,FMap.empty))
      | FunApp(f,args) ->
          (* It is important to first generate the branch corresponding to the arguments
             [args] since they should appear below [f] in the branch. *)
          generate_branch_list (fun tree ->
            f_next (Node (None, FMap.singleton f tree))
          ) prev_tree (d+1) args

    and generate_branch_list f_next prev_tree d = function
      | [] -> f_next prev_tree
      | t::q ->
          (* It is important to first generate the branch corresponding to [q]
             since it should appear below the portion of the branch corresponding
             to [t] in the depth-first search representation. *)
          generate_branch_list (fun tree ->
            generate_branch f_next tree d t
          ) prev_tree d q

    (* [add tree (elt:'a) args] adds the element [elt] represented by [args] in the tree. *)
    let add tree elt args =

      (* [add_aux f_next d tree t] adds the element [elt] partially represented by [t] in [tree].
        The function [f_next] intuitively represents the remaining of the depth-first-search exploration
        once [t] is fully explored. Hence, the tree given as argument to [f_next] should correspond to
        the tree after exploration of [t].
      *)
      let rec add_aux f_next d tree t = match tree with
        | Leaf [] ->
            (* We first generate the tree corresponding to the remaining of the depth-first-search*)
            let tree1 = f_next tree in
            (* This tree is plugged after the branch for [t]. *)
            generate_branch (fun tree -> tree) tree1 d t
        | Leaf _ -> Parsing_helper.internal_error "[database.ml >> UnificationTrie.add] Unexpected case"
        | Node(var_op,fun_map) ->
            match t with
              | Var _ -> Node(add_var_op_aux f_next var_op,fun_map)
              | FunApp(_,_) when d = !Param.unify_trie_term_max_depth -> Node(add_var_op_aux f_next var_op,fun_map)
              | FunApp(f,args) ->
                  let fun_map1 =
                    FMap.update f (function
                      | None ->
                          (* Will generate a new branch starting with [f]. *)
                          Some(add_aux_list f_next (d+1) (Leaf []) args)
                      | Some tree1 ->
                          (* Update the current tree labeled with [f]. *)
                          Some(add_aux_list f_next (d+1) tree1 args)
                    ) fun_map
                  in
                  Node(var_op,fun_map1)


      and add_var_op_aux f_next = function
        | None -> Some(f_next (Leaf[]))
        | Some tree -> Some (f_next tree)

      and add_aux_list f_next d tree = function
        | [] -> f_next tree
        | t::q ->
            (* Important to start with exploring first [t] since we're doing a depth-first-search.
               Note that when creating a branch, we need to generate first the branch for [q] and then [t]
               but here since we're exploring an existing tree, we need to start with [t] and then [q].
            *)
            add_aux (fun tree1 ->
              add_aux_list f_next d tree1 q
            ) d tree t

      in

      add_aux_list (function
        | Leaf elt_l -> Leaf (elt::elt_l)
        | _ ->
            (* We cannot have a node here as it would imply that there is an inconsistency with the
               depth-first-search exploration of the arguments. *)
            Parsing_helper.internal_error "[subsumption.ml >> UnificationTrie.add] Unexpected case (2)"
      ) 1 tree args

    (* [apply_on_next_n_term f_next n tree] explores [n] "full" term on all branches of [tree] and apply
       the function [f_next] on each corresponding subtree. *)
    let rec apply_on_next_n_term f_next n tree =
      if n = 0
      then f_next tree
      else
        match tree with
          | Leaf _ -> Parsing_helper.internal_error "[database.ml >> UnificationTrie.apply_on_next_n_term] Unexpected case"
          | Node(Some tree1,fun_map) ->
              apply_on_next_n_term f_next (n-1) tree1;
              FMap.iter (fun f tree2 ->
                apply_on_next_n_term f_next ((List.length (fst f.f_type))+n-1) tree2
              ) fun_map
          | Node(None, fun_map) ->
              FMap.iter (fun f tree2 ->
                apply_on_next_n_term f_next ((List.length (fst f.f_type))+n-1) tree2
              ) fun_map

    (* We apply the function [f] on the elements of the tree that have a representative unifiable with [args] *)
    let iter_unify f tree args =

      let rec iter_aux f_next tree t = match tree,t with
        | Leaf [], _ -> ()
        | Leaf _ , _ -> Parsing_helper.internal_error "[database.ml >> UnificationTrie.iter_unify] Unexpected case"
        | _, Var _ ->
            (* Since the term is a variable, we need to look at all the branch related to this particular term. *)
            apply_on_next_n_term f_next 1 tree
        | Node(var_op,fun_map), FunApp(f,args) ->
            begin match FMap.find_opt f fun_map with
              | None -> ()
              | Some tree1 -> iter_list_aux f_next tree1 args
            end;
            begin match var_op with
              | None -> ()
              | Some tree1 ->
                  (* Since the representative has a variable, it may unify with [t] so
                     we need to continue exploring on [tree1] *)
                  f_next tree1
            end;

      and iter_list_aux f_next tree = function
        | [] -> f_next tree
        | t::q ->
            (* Important to start with exploring first [t] since we're doing a depth-first-search. *)
            iter_aux (fun tree1 ->
              iter_list_aux f_next tree1 q
            ) tree t

      in

      iter_list_aux (function
        | Leaf elt_l -> List.iter f elt_l
        | _ -> Parsing_helper.internal_error "[database.ml >> UnificationTrie.iter_unify] Unexpected case (2)"
      ) tree args

    (* [filter f tree] returns the tree with only the elements that satisfy the predicate [f]. *)
    let rec filter f = function
      | Leaf elt_l -> Leaf (List.filter f elt_l)
      | Node(var_op,fun_map) ->
          let var_op1 = match var_op with
            | None -> None
            | Some tree ->
                let tree1 = filter f tree in
                if tree1 = Leaf []
                then None
                else Some tree1
          in
          let fun_map1 =
            FMap.update_all (fun t ->
              match filter f t with
                | Leaf [] -> None
                | t' -> Some t'
            ) fun_map
          in

          if var_op1 = None && FMap.is_empty fun_map1
          then Leaf []
          else Node(var_op1,fun_map1)

  end

(***********************************
    Set of clauses
************************************)

module type SetSig =
  sig
    type clause
    type subsumption_data
    type sub_annot_clause = clause * subsumption_data
    type annot_clause = clause * feature_vector * subsumption_data

    type active_status = Active | Inactive | Removed

    type 'a element =
      {
        mutable annot_clause: sub_annot_clause;
        mutable selected_fact: fact;
        mutable additional_data : 'a;
          (* When the clause has a selected hypothesis, it will store its index.
             When the clause has its conclusion selected, it will store whether
	     all hypotheses of the clause are unselectable. *)
        mutable active : active_status;
      }

    type 'a t

    (* The empty set *)
    val create : unit -> 'a t

    (* Should not be applied on an element that is already active. *)
    val activate : 'a t -> 'a element -> unit

    (* Should not be applied on an element that is already inactive. *)
    val deactivate : 'a t -> 'a element -> unit

    (* [add set annot_cl uni_fact add_data] adds to [set] the annotated clause [cl].
       (An annotated clause is a clause with associated feature vector
       and subsumption data.)
       [uni_fact] is the selected fact of [cl].
       Note that [cl] is active in the resulting set. *)
    val add : 'a t -> annot_clause -> fact -> 'a -> unit

    (* [implies set annot_cl] checks whether an active clause from [set] implies
       the annotated clause [cl]. *)
    val implies : 'a t -> annot_clause -> bool

    (* [deactivate_implied_by empty_add_data set annot_cl] deactivates the clauses from [set]
       that are implied by the annotated clause [annot_cl].
       [empty_add_data] is a empty additional data value, that replaces the additional
       data of deactivated clauses. *)
    val deactivate_implied_by : 'a -> 'a t -> annot_clause -> unit

    (* [cleanup_deactivated set] removes the deactivated clauses in [set] *)
    val cleanup_deactivated : 'a t -> unit

    (* [iter f set] applies [f] to all active clauses *)
    val iter : ('a element -> unit) -> 'a t -> unit

    (* [iter_unifiable f set fact] applies [f] to all active clauses in [set]
       whose selected fact may be unifiable with [fact] *)
    val iter_unifiable : ('a element -> unit) -> 'a t -> fact -> unit

    (* [length set] returns the number of active clauses in [set]. *)
    val length : 'a t -> int

    (* [to_list set] returns the list of active clauses in [set]. *)
    val to_list : 'a t -> clause list

    (* [exists f set] returns [true] if there exists an active clause [cl] in [set]
       such that [f cl = true]. *)
    val exists : (clause -> bool) -> 'a t -> bool
  end

module MakeSet (C:ClauseSig) (S:SubsumptionSig with type hyp_fact = C.hyp_fact and type clause = C.t) =
  struct
    type clause = C.t
    type subsumption_data = S.subsumption_data
    type sub_annot_clause = clause * subsumption_data
    type annot_clause = clause * feature_vector * subsumption_data

    type active_status = Active | Inactive | Removed

    type 'a element =
      {
        mutable annot_clause: sub_annot_clause;
        mutable selected_fact: fact;
        mutable additional_data: 'a;
        mutable active : active_status
      }

    type 'a t =
      {
        mutable trie : 'a element FeatureTrie.t;
        mutable unify_trie : (predicate * ('a element  UnificationTrie.t)) list;
        mutable elt_list : 'a element list;
        mutable nb_total : int;
        mutable nb_deactive : int
      }

    let create () = { trie = FeatureTrie.empty; unify_trie = []; elt_list = []; nb_total = 0; nb_deactive = 0 }

    let activate set elt =
      assert (elt.active == Inactive);
      elt.active <- Active;
      set.nb_deactive <- set.nb_deactive - 1

    let deactivate set elt =
      assert (elt.active == Active);
      elt.active <- Inactive;
      set.nb_deactive <- set.nb_deactive + 1

    let rec update_in_list p f = function
      | [] -> [p,f (UnificationTrie.empty)]
      | (p',tree)::q when p == p' -> (p',f tree)::q
      | t::q -> t::(update_in_list p f q)

    let add set (cl, vector, sub_data) sel_fact add_data  =
      let elt = { annot_clause = (cl, sub_data); selected_fact = sel_fact; additional_data = add_data; active = Active } in
      let Pred(p,args) = sel_fact in
      set.unify_trie <- update_in_list p (fun tree -> UnificationTrie.add tree elt args) set.unify_trie;
      if !Param.feature then
        set.trie <- FeatureTrie.add set.trie elt vector;
      set.elt_list <- elt :: set.elt_list;
      set.nb_total <- set.nb_total + 1

    (* [implies set vector cl] checks whether a clause from [set] implies (w.r.t. [f_implies])
       the clause [cl] that have [vertor] as feature vector. *)
    let implies set (cl, vector, sub_data) =
      let test_fun elt =
	let (elt_cl, elt_sub_data) = elt.annot_clause in
        elt.active == Active && S.implies_no_test elt_cl elt_sub_data cl sub_data
      in
      if !Param.feature then
	FeatureTrie.exists_leq test_fun vector set.trie
      else
	List.exists test_fun set.elt_list

    let deactivate_implied_by empty_add_data set (cl, vector, sub_data) =
      if !Param.feature then
	FeatureTrie.iter_geq (fun elt ->
	  let (elt_cl, elt_sub_data) = elt.annot_clause in
          if elt.active == Active && S.implies_no_test cl sub_data elt_cl elt_sub_data
          then
            begin
	      elt.annot_clause <- S.empty_sub_annot_clause; (* Remove the clause, so that it can be garbage collected *)
	      elt.additional_data <- empty_add_data;
              elt.selected_fact <- Param.dummy_fact;
              elt.active <- Removed;
              set.nb_deactive <- set.nb_deactive + 1
            end
	      ) vector set.trie
      else
	set.elt_list <- List.filter (fun elt ->
	  let (elt_cl, elt_sub_data) = elt.annot_clause in
	  match elt.active with
	  | Removed -> assert false
	  | Inactive -> true
	  | Active ->
	      if S.implies_no_test cl sub_data elt_cl elt_sub_data
	      then
		begin
		  set.nb_total <- set.nb_total - 1;
		  false
		end
	      else
		true
		  ) set.elt_list


    let rec cleanup_deactivated_unify_trie = function
      | [] -> []
      | (p,t)::q ->
          let t' = UnificationTrie.filter (fun elt -> elt.active == Active) t in
          if UnificationTrie.is_empty t'
          then cleanup_deactivated_unify_trie q
          else (p,t')::(cleanup_deactivated_unify_trie q)

    let cleanup_deactivated set =
      if set.nb_total != 0 && (set.nb_deactive * 100) / set.nb_total > !Param.cleanup_threshold
      then
        begin
          let f elt = (elt.active == Active) in
	  if !Param.feature then
            set.trie <- FeatureTrie.filter f set.trie;
          set.unify_trie <- cleanup_deactivated_unify_trie set.unify_trie;
          set.elt_list <- List.filter f set.elt_list;
          set.nb_total <- set.nb_total - set.nb_deactive;
          set.nb_deactive <- 0
        end

    let iter f set =
      List.iter (fun elt ->
	if elt.active == Active then f elt
	    ) set.elt_list

    let iter_unifiable f set = function
      | Pred(p,args) ->
          try
            let tree = List.assq p set.unify_trie in
            UnificationTrie.iter_unify (fun elt ->
              if elt.active == Active then f elt
            ) tree args
          with Not_found -> ()

    let length set = set.nb_total - set.nb_deactive

    let to_list set =
      let rec to_list_rec acc = function
        | [] -> List.rev acc
        | elt::q ->
	    if elt.active == Active then
	      let (clause, _) = elt.annot_clause in
	      to_list_rec (clause::acc) q
	    else
	      to_list_rec acc q
      in
      to_list_rec [] set.elt_list

    let exists f set = List.exists (fun elt -> elt.active == Active && f (fst elt.annot_clause)) set.elt_list
  end

(***********************************
    Queue of clauses
************************************)

module type QueueSig =
  sig

    type clause
    type subsumption_data
    type annot_clause = clause * feature_vector * subsumption_data
    type t

    (* Generate a new queue *)
    val new_queue : unit -> t

    (* [add q annot_cl] adds to the queue [q] the annotated clause [cl] *)
    val add : t -> annot_clause -> unit

    (* [get q] takes the first clause of the queue with its respective feature
      vector and implication data. Note that the resulting clause is always activated. *)
    val get : t -> annot_clause option

    (* [implies q annot_cl] checks whether an active clause from [q] implies the
       annotated clause [cl]. *)
    val implies : t -> annot_clause -> bool

    (* [deactivate_implied_by q annot_cl] deactivates the clauses from [q]
       that are implied by the annotated clause [cl] *)
    val deactivate_implied_by : t -> annot_clause -> unit

    (* [cleanup_deactivated q] removes the deactivated clauses in [q]. *)
    val cleanup_deactivated : t -> unit

    (* [iter f q] applies [f] on each active clause of the queue [q]. *)
    val iter : (annot_clause -> unit) -> t -> unit

    (* [length q] returns the number of clauses in [q]. *)
    val length : t -> int
  end

module MakeQueue (C:ClauseSig) (S:SubsumptionSig with type hyp_fact = C.hyp_fact and type clause = C.t) =
  struct

    type clause = C.t
    type subsumption_data = S.subsumption_data
    type annot_clause = clause * feature_vector * subsumption_data

    type element =
      {
        mutable prev : element option;
        mutable next : element option;
        mutable active : bool;
	mutable annot_clause : annot_clause
      }

    type t =
      {
        mutable qstart : element option;
        mutable qend : element option;
        mutable trie : element FeatureTrie.t;
        mutable nb_total : int;
        mutable nb_deactive : int
      }

    let empty_annot_clause = (C.empty_clause, [], S.empty_sub_data)

    let new_queue () = { qstart = None; qend = None; trie = FeatureTrie.empty; nb_total = 0; nb_deactive = 0 }

    let add queue ((_, vector, _) as annot_cl) = match queue.qend with
      | None ->
          let elt = { prev = None; next = None; active = true; annot_clause = annot_cl } in
          queue.qstart <- Some elt;
          queue.qend <- Some elt;
	  if !Param.feature then
            queue.trie <- FeatureTrie.add queue.trie elt vector;
          queue.nb_total <- queue.nb_total + 1
      | Some q ->
          let elt = { prev = Some q; next = None; active = true; annot_clause = annot_cl } in
          q.next <- Some elt;
          queue.qend <- Some elt;
	  if !Param.feature then
            queue.trie <- FeatureTrie.add queue.trie elt vector;
          queue.nb_total <- queue.nb_total + 1

    let get queue = match queue.qstart with
      | None -> None
      | Some q ->
          match q.next with
            | None ->
                queue.qend <- None;
                queue.qstart <- None;
                queue.trie <- FeatureTrie.empty;
                queue.nb_total <- 0;
                queue.nb_deactive <- 0;
                Some q.annot_clause
            | Some q' ->
                q.active <- false;
                queue.qstart <- q.next;
                q'.prev <- None;
                queue.nb_deactive <- queue.nb_deactive + 1;
                Some q.annot_clause

    let length queue = queue.nb_total - queue.nb_deactive

    let iter f queue =
      let rec iterrec = function
        | None -> ()
        | Some q ->
            f q.annot_clause;
            iterrec q.next
      in
      iterrec queue.qstart

    let implies queue (cl, vector, sub_data) =
      let test_fun elt =
	let (elt_cl,_,elt_sub_data) = elt.annot_clause in
        elt.active && S.implies_no_test elt_cl elt_sub_data cl sub_data
      in
      if !Param.feature then
	FeatureTrie.exists_leq test_fun vector queue.trie
      else
	let rec existsrec q =
	  match q with
	    None -> false
	  | Some q' -> (test_fun q') || (existsrec q'.next)
	in
	existsrec queue.qstart

    let deactivate_implied_by queue (cl, vector, sub_data) =
      let iter_fun elem =
	let (elt_cl,_,elt_sub_data) = elem.annot_clause in
        if elem.active && S.implies_no_test cl sub_data elt_cl elt_sub_data
        then
          begin
            (* Clause need to be removed *)
	    elem.annot_clause <- empty_annot_clause; (* Remove the clause, so that it can be garbage collected *)
            elem.active <- false;
            queue.nb_deactive <- queue.nb_deactive + 1;
            match elem.prev, elem.next with
              | None, None ->
                  (* The queue contains a unique element *)
                  queue.qstart <- None;
                  queue.qend <- None
              | Some elem', None ->
                  (* [elem] is the last element of the queue so
                  [elem'] becomes the last element *)
                  queue.qend <- elem.prev;
                  elem'.next <- elem.next
              | None, Some elem' ->
                  (* [elem] is the first element of the queue so
                  [elem'] becomes the first element *)
                  queue.qstart <- elem.next;
                  elem'.prev <- elem.prev
              | Some elem_p, Some elem_n ->
                  elem_p.next <- elem.next;
                  elem_n.prev <- elem.prev
          end
      in
      if !Param.feature then
	FeatureTrie.iter_geq iter_fun vector queue.trie
      else
	let rec iterrec = function
        | None -> ()
        | Some q ->
	    let next = q.next in
            iter_fun q;
            iterrec next
	in
	iterrec queue.qstart

    let cleanup_deactivated queue =
      if queue.nb_total != 0 && (queue.nb_deactive * 100) / queue.nb_total > !Param.cleanup_threshold
      then
        begin
	  if !Param.feature then
            queue.trie <- FeatureTrie.filter (fun elt -> elt.active) queue.trie;
          queue.nb_total <- queue.nb_total - queue.nb_deactive;
          queue.nb_deactive <- 0
        end
  end

(* Database *)

module type DBSig =
  sig
    type clause
    type queue
    type 'a set

    type t =
      {
        queue : queue;
        mutable count : int;
        mutable base_ns : bool set;
        mutable base_sel : int set
      }

    val create : unit -> t

    val add_rule : t -> clause -> unit

    val display_initial_queue : t -> unit

    val display_rule_during_completion : t -> (clause * int) -> unit

    val display_dynamic_statistics : t -> unit
  end

module MakeDatabase
  (C:ClauseSig)
  (S:SubsumptionSig with type hyp_fact = C.hyp_fact and type clause = C.t)
  (F:FeatureGenerationSig with type clause = C.t and type subsumption_data = S.subsumption_data)
  (Set:SetSig with type clause = C.t and type subsumption_data = S.subsumption_data)
  (Queue:QueueSig with type clause = C.t and type subsumption_data = S.subsumption_data)
  =
  struct
    type clause = C.t
    type queue = Queue.t
    type 'a set = 'a Set.t

    type t =
      {
        queue : Queue.t;
        mutable count : int;
        mutable base_ns : bool Set.t; (* The boolean indicate whether this rule can be used for redundancy *)
        mutable base_sel : int Set.t (* The integer represents the index of the selected fact *)
      }

    let create () =
      {
        queue = Queue.new_queue ();
        count = 0;
        base_ns = Set.create ();
        base_sel = Set.create ();
      }

    let get_stat_string database =
      let size_base_ns = Set.length database.base_ns in
      let size_base_sel = Set.length database.base_sel in
      Printf.sprintf "%d rules inserted. Base: %d rules (%d with conclusion selected). Queue: %d rules."
        database.count
        (size_base_ns + size_base_sel)
        size_base_ns
        (Queue.length database.queue)
      
    let display_dynamic_statistics database =
      if !Param.verbose_dynamic_statistics
      then 
        Display.dynamic_display (get_stat_string database)

    let add_rule database rule =
      let annot_cl = F.generate_feature_vector_and_subsumption_data rule in

      (* Check that the rule is not already in the rule base or in the queue *)
      if Set.implies database.base_ns annot_cl ||
         Set.implies database.base_sel annot_cl ||
         Queue.implies database.queue annot_cl
      then ()
      else
        begin
	  let rule' = C.simplify_remove_hyp rule in
	  let annot_cl' = F.generate_feature_vector_and_subsumption_data rule' in

          (* We deactivate the clauses that are implied by rule (semantically, it is the same as
             removing the clauses but for efficiency, they are not always directly removed
             from the database but only deactivated.) *)
          Set.deactivate_implied_by true database.base_ns annot_cl';
          Set.deactivate_implied_by 0 database.base_sel annot_cl';
          Queue.deactivate_implied_by database.queue annot_cl';

          (* We check the rule *)
          C.check rule;

          (* We add the rule *)
          Queue.add database.queue annot_cl';

          (* Cleanup that will remove the deactivated clauses when needed. *)
          Set.cleanup_deactivated database.base_ns;
          Set.cleanup_deactivated database.base_sel;
          Queue.cleanup_deactivated database.queue;

          (* Display statistics *)
          display_dynamic_statistics database
        end

    let display_base_sel database =
      let count = ref 1 in
      Set.iter (fun { annot_clause = (clause, _); additional_data = sel; active = active; selected_fact; _ } ->
        Display.auto_cleanup_display (fun () ->
          Display.Text.print_string ((string_of_int !count)^" -- (hyp "^(string_of_int sel)^" selected: ");
          Display.Text.display_fact selected_fact;
          Display.Text.print_line "):";
          C.display clause
	    );
        incr count
	  ) database.base_sel

    let display_base_ns database =
      let count = ref 1 in
      Set.iter (fun { annot_clause = (clause, _); active = active } ->
        Display.Text.print_string ((string_of_int !count)^" -- ");
        C.display_indep clause;
        incr count
  	    ) database.base_ns

    let display_initial_queue database =
      Display.Text.print_line "------------ Initial queue ----------";
      let count = ref 0 in
      Queue.iter (fun (rule, _, _) ->
        Display.Text.print_string ((string_of_int (!count + 1))^" -- ");
        C.display_indep rule;
        incr count;
      ) database.queue;
      Display.Text.print_line "------------------------------------"

    let display database =
      Display.Text.print_line "------------ Resulting base and rules added in queue ----------";
      Display.Text.print_line "*** Rules with the conclusion selected";
      display_base_ns database;
      Display.Text.print_line "*** Rules with an hypothesis selected";
      display_base_sel database;
      Display.Text.print_line "*** Rules in queue";
      let count = ref 0 in
      Queue.iter (fun (rule, _, _) ->
        Display.Text.print_string ((string_of_int (!count + 1))^" -- ");
        C.display_indep rule;
        incr count;
      ) database.queue;
      Display.Text.print_line "------------------------------------"

    let display_rule_during_completion database (rule,sel_index) =
      let display_stat () =
	print_string (get_stat_string database);
        Display.Text.newline()
      in

      (* Display the rule *)
      if !Param.verbose_rules || !Param.verbose_base
      then
        begin
	  Display.stop_dynamic_display ();
          Display.auto_cleanup_display (fun () ->
            if sel_index >= 0
            then
              begin
                let (hypl,_,_,_) = C.get_reduction rule in
                Display.Text.newline ();
                Display.Text.print_string ("Rule with hypothesis fact "^(string_of_int sel_index)^" selected: ");
                Display.Text.display_fact (List.nth hypl sel_index);
                Display.Text.newline ();
              end
            else
              begin
                Display.Text.newline ();
                Display.Text.print_line "Rule with conclusion selected:";
              end;

            C.display rule;
            database.count <- database.count + 1;
            display_stat ()
          );

          if !Param.verbose_base then display database
        end
      else
        begin
          database.count <- database.count + 1;
          if database.count mod 200 = 0
          then
	    begin
	      Display.stop_dynamic_display ();
	      display_stat ()
	    end
        end
  end

(* The generated modules *)

module Clause : ClauseSig with type hyp_fact = fact and type t = reduction =
  struct
    type hyp_fact = fact
    type t = reduction
    let empty_clause = ([], Param.dummy_fact, Empty(Param.dummy_fact), { neq = []; is_nat = []; is_not_nat = []; geq = [] })
    let get_reduction r = r
    let match_facts = Terms.match_facts
    let fact_of_hyp_fact f = f
    let get_clause_with_hyp_fact r = r
    let simplify_remove_hyp = remove_ground_public_terms
    let check = check_rule
    let display = Display.Text.display_rule
    let display_indep = Display.Text.display_rule_indep
    let display_hyp_fact = Display.Text.display_fact
  end
module SubClause = MakeSubsumption(Clause)
module FeatureGenClause = MakeFeatureGeneration(Clause)(SubClause)
module SetClause = MakeSet(Clause)(SubClause)
module QueueClause = MakeQueue(Clause)(SubClause)
module DB = MakeDatabase(Clause)(SubClause)(FeatureGenClause)(SetClause)(QueueClause)

module OrdClause : ClauseSig with type hyp_fact = fact * ordering_function and type t = ordered_reduction =
  struct
    type hyp_fact = fact * ordering_function
    type t = ordered_reduction

    let empty_clause = { rule = Clause.empty_clause; order_data = None }
    let get_reduction r = r.rule

    let match_facts (f1,ord_fun1) (f2,ord_fun2) =
      Terms.match_facts f1 f2;
      implies_ordering_function ord_fun1 ord_fun2

    let fact_of_hyp_fact (f,_) = f

    let get_clause_with_hyp_fact r =
      let (hypl,concl,hist,constra) = r.rule in
      let hypl' = match r.order_data with
        | None -> List.map (fun f -> f,[]) hypl
        | Some ord_data -> List.map2 (fun f (ord_fun,_) -> (f,ord_fun)) hypl ord_data
      in
      (hypl',concl,hist,constra)

    let rec ord_remove_ground_public_terms_rec accu hypl ordl =
      List.fold_right2 (fun hyp1 ord1 (hypl,ordl,nl,histl) -> match hyp1 with
      | Pred(chann,t::q) ->
	  if chann.p_prop land Param.pred_ATTACKER != 0 && is_ground_public t && List.for_all (equal_terms t) q
	  then
	    let (hypl',nl',histl') = remove_sure_ground_public_terms (hypl,nl,histl) [hyp1] in
	    (hypl',ordl,nl',histl')
	  else (hyp1::hypl, ord1::ordl, nl-1, histl)
      | _ -> (hyp1::hypl, ord1::ordl, nl-1, histl)
	    ) hypl ordl accu

    let simplify_remove_hyp r =
      match r.order_data with
        | None -> { rule = remove_ground_public_terms r.rule; order_data = None }
	| Some ord_data ->
	    let (hypl,concl,hist,constra)= r.rule in
	    let (hypl',ordl',_,hist') =
	      ord_remove_ground_public_terms_rec ([],[],(List.length hypl)-1,hist) hypl ord_data
	    in
	    { rule = (hypl',concl,hist',constra); order_data = Some ordl' }

    let check = check_rule_ordered

    let display = Display.Text.display_ordered_rule

    let display_indep = Display.Text.display_ordered_rule_indep

    let display_hyp_fact (fact,_) = Display.Text.display_fact fact
  end
module SubOrdClause = MakeSubsumption(OrdClause)
module FeatureGenOrdClause = MakeFeatureGeneration(OrdClause)(SubOrdClause)
module SetOrdClause = MakeSet(OrdClause)(SubOrdClause)
module QueueOrdClause = MakeQueue(OrdClause)(SubOrdClause)
module DBOrd = MakeDatabase(OrdClause)(SubOrdClause)(FeatureGenOrdClause)(SetOrdClause)(QueueOrdClause)

(* A specific module for Saturated clause. It is typically a subset of function from SetClause
   where we only need to work with unification *)

module SetSatClause =
  struct

    type t = (predicate * (saturated_reduction UnificationTrie.t)) list

    let empty = []

    let rec update_in_list p f = function
      | [] -> [p,f (UnificationTrie.empty)]
      | (p',tree)::q when p == p' -> (p',f tree)::q
      | t::q -> t::(update_in_list p f q)

    let of_list sat_rules =
      List.fold_left (fun acc_tree ({ sat_rule = (_,Pred(p,args),_,_); _ } as sat_rule) ->
        update_in_list p (fun tree -> UnificationTrie.add tree sat_rule args) acc_tree;
      ) [] sat_rules

    let iter_unifiable f set = function
      | Pred(p,args) ->
          try
            let tree = List.assq p set in
            UnificationTrie.iter_unify f tree args
          with Not_found -> ()
  end
