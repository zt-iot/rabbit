open Types
open Parsing_helper
open Terms

exception HistoryUnifyError of string

(* add a rule and return its history *)

let rule_hash = Hashtbl.create 7

let change_type_attacker p t =
  match p.p_info with
    Attacker(n,_) -> Param.get_pred (Attacker(n,t))
  | AttackerBin(n,_) -> Param.get_pred (AttackerBin(n,t))
  | AttackerGuess _ -> Param.get_pred (AttackerGuess(t))
  | Compromise _ -> Param.get_pred (Compromise(t))
  | UserPred(Polym(s,i,tl)) -> Param.get_pred (UserPred(Polym(s,i,Terms.copy_n (List.length tl) t)))
  | UserPred(Monom) ->
      if !Param.typed_frontend then
        Parsing_helper.internal_error "Non-polymorphic user-defined predicates should not be declared data in the typed front-end"
      else
        p
  | _ -> Parsing_helper.internal_error "Unexpected predicate in change_type_attacker"

let get_rule_hist descr =
  try
    Hashtbl.find rule_hash descr
  with Not_found ->
    let (hyp,concl,constra,hdescr) =
      match descr with
        RElem(preds, ({ p_type = [t1;t2] } as p)) ->
          let v = Terms.new_var_def_term t1 in
          let v' = Terms.new_var_def_term t2 in
          (List.map (fun p' -> Pred(change_type_attacker p' t1, [v])) preds,
           Pred(p, [v;v']),
           true_constraints, Elem(preds,p))
      | RApplyFunc(f,p) ->
          let rec gen_vars n =
            if n = 0 then
              []
            else
              (FunApp(f, Terms.var_gen (fst f.f_type))) :: (gen_vars (n-1))
          in
          let concl = gen_vars (List.length p.p_type) in
          let hypl = reorganize_fun_app f concl in
          let tag = match f.f_cat with
            | Name _ -> Init (* Called only when removing public ground attacker facts *)
            | _ -> Apply(f,p)
          in
          (List.map (fun h -> Pred((change_type_attacker p (Terms.get_term_type (List.hd h))), h)) hypl,
           Pred((change_type_attacker p (Terms.get_term_type (List.hd concl))), concl), true_constraints,
           tag)
      | RApplyProj(f,nproj,p) ->
          let rec gen_vars n =
            if n = 0 then
              []
            else
              (FunApp(f, Terms.var_gen (fst f.f_type))) :: (gen_vars (n-1))
          in
          let hyp = gen_vars (List.length p.p_type) in
          let concl = List.nth (reorganize_fun_app f hyp) nproj in
          ([Pred((change_type_attacker p (Terms.get_term_type (List.hd hyp))),hyp)],
           Pred((change_type_attacker p (Terms.get_term_type (List.hd concl))), concl), true_constraints,
           Apply(Terms.projection_fun(f,nproj+1), p))
      | RFail(left,({ p_info = AttackerBin(_,t) | AttackerGuess t; _ } as p)) ->
          let x = Terms.new_var_def_term t
          and fail = Terms.get_fail_term t in
          let hyp = if left then [Pred(p, [x; fail])] else [Pred(p, [fail; x])] in
          let concl = Pred(Param.bad_pred, []) in

          (hyp,concl,Terms.true_constraints,Rfail(p))
      | _ ->
          internal_error "unsupported get_rule_hist"
    in
    let hist = Rule(-1, hdescr, hyp, concl, constra) in
    Hashtbl.add rule_hash descr hist;
    hist

(* History simplification *)

(* We use a hash table that associates to each fact all trees that
   derive it. To avoid recomputing hashes, we store them together with
   the considered fact. *)

module HashFact =
  struct

    type t =
        { hash : int;
          fact : fact }

    let equal a b = Termslinks.equal_facts_with_links a.fact b.fact

    type skel_f =
      SFixed of string
    | SRenamable of string * int

    type skel_term =
        SVar of string * int
      |	SFun of skel_f * skel_term list

    type skel_fact =
        SPred of string * skel_term list

    let skel_f f =
      match f.f_name with
        Fixed s -> SFixed s
      | Renamable id -> SRenamable(id.name, id.idx)

    let rec skeleton_term = function
        Var b ->
          begin
            match b.link with
              TLink t -> skeleton_term t
            | NoLink -> SVar(b.vname.name, b.vname.idx)
            | _ -> Parsing_helper.internal_error "unexpected link in skeleton_term"
          end
      |	FunApp(f,l) ->
          match f.f_cat with
            Name _ -> SFun(skel_f f,[])
          | _ -> SFun(skel_f f, List.map skeleton_term l)

    let skeleton_fact = function
      | Pred(p,l) -> SPred(p.p_name, List.map skeleton_term l)

    let hash a = a.hash

    (* build a HashFact.t from a fact *)

    let build f = { hash = Hashtbl.hash(skeleton_fact f);
                    fact = f }

  end

module TreeHashtbl = Hashtbl.Make(HashFact)

let tree_hashtbl = TreeHashtbl.create 7

let seen_fact hf =
  if !Param.simplify_derivation_level = Param.AllFacts then
    TreeHashtbl.find tree_hashtbl hf
  else
  match hf.HashFact.fact with
    Pred(p,_) when p.p_prop land Param.pred_ATTACKER != 0 ->
      TreeHashtbl.find tree_hashtbl hf
  | _ -> raise Not_found
               (* Remove proofs of the same fact only for attacker facts,
                  several proofs of the same fact may be useful for attack
                  reconstruction for other facts: for mess facts, in particular
                  several outputs of the same message on the same channel
                  may be needed for private channels. *)

let rec unroll_rwp t =
  match t.desc with
    FRemovedWithProof t' -> unroll_rwp t'
  | _ -> t

let equal_son t t' =
  unroll_rwp t == unroll_rwp t'

let equal_lemma l1 l2 =
  List.length l1 == List.length l2 &&
  List.for_all2 (fun (i1,constra1,ft_l1) (i2,constra2,ft_l2) ->
    i1 == i2 && (Termslinks.equal_constra constra1 constra2) && List.for_all2 equal_son ft_l1 ft_l2
  ) l1 l2

let seen_tree hf t =
  if !Param.simplify_derivation_level != Param.AttackerSameTree then
    begin
      TreeHashtbl.add tree_hashtbl hf t;
      t
    end
  else
    match t.thefact with
      Pred(p,_) when p.p_prop land Param.pred_ATTACKER != 0 ->
          (* If t was already proved, it would have been removed by seen_fact when it
             concludes an attacker fact *)
        TreeHashtbl.add tree_hashtbl hf t;
        t
    | _ ->
        try
          let r = TreeHashtbl.find_all tree_hashtbl hf in
          let t' =
            List.find (fun t' -> match t.desc, t'.desc with
                FHAny, FHAny -> true
              | FRemovedWithMaxHyp, FRemovedWithMaxHyp -> true
              | FEmpty, FEmpty -> true
              | FRule(n, tags, constra, sons,constra_a,sons_a), FRule(n', tags', constra', sons',constra_a',sons_a') ->
                  (n == n') && (Termslinks.equal_tags tags tags') && (Termslinks.equal_constra constra constra') &&
                  (List.length sons == List.length sons') && (List.for_all2 equal_son sons sons') &&
                  (Termslinks.equal_constra constra_a constra_a') &&
                  (List.length sons_a == List.length sons_a') && (List.for_all2 equal_son sons_a sons_a')
              | FEquation son, FEquation son' ->
                  equal_son son son'
              | FRemovedWithProof _, _ -> internal_error "Unexpected FRemovedWithProof"
              | _ -> false
            ) r
          in
          { t with desc = FRemovedWithProof t' }
        with Not_found ->
          TreeHashtbl.add tree_hashtbl hf t;
          t

let rec simplify_tree t =
  let hf = HashFact.build t.thefact in
  match t.desc with
    FRemovedWithProof t' ->
      begin
        try
          { t with desc = FRemovedWithProof (TreeHashtbl.find tree_hashtbl hf) }
        with Not_found ->
          simplify_tree t'
      end
  | FHAny | FEmpty | FRemovedWithMaxHyp ->
      begin
        try
          { t with desc = FRemovedWithProof (seen_fact hf) }
        with Not_found ->
          seen_tree hf t
      end
  | FRule(n, tags, constra, sons, constra_a, sons_a) ->
      begin
        try
          { t with desc = FRemovedWithProof (seen_fact hf) }
        with Not_found ->
          let sons' = List.rev_map simplify_tree (List.rev sons) in
          let sons_a' = List.rev_map simplify_tree (List.rev sons_a) in
          seen_tree hf { t with desc = FRule(n, tags, constra, sons',constra_a,sons_a') }
      end
  | FEquation son ->
      begin
        try
          { t with desc = FRemovedWithProof (seen_fact hf) }
        with Not_found ->
          let son' = simplify_tree son in
          seen_tree hf { t with desc = FEquation son' }
      end

(* Find hypothesis number n in the history tree *)

type res = FindSuccess of fact_tree
         | FindFailure of int

let rec get_desc_rec t n = match t.desc with
  | FEmpty -> if n = 0 then FindSuccess(t) else FindFailure(n-1)
  | FHAny | FRemovedWithProof _ | FRemovedWithMaxHyp -> FindFailure(n)
  | FRule(_,_,_,l,_,l_a) ->
      begin match get_desc_list_rec l n with
        | FindSuccess t' -> FindSuccess t'
        | FindFailure n' -> get_desc_list_rec l_a n'
      end
  | FEquation h -> get_desc_rec h n

and get_desc_list_rec l n =
  match l with
    [] -> FindFailure(n)
  | (a::l') ->
      match get_desc_rec a n with
        FindSuccess d -> FindSuccess d
      | FindFailure n' -> get_desc_list_rec l' n'

let get_desc s t n =
  match get_desc_rec t n with
    FindSuccess d -> d
  | FindFailure n' ->
      print_string ("Hypothesis " ^ (string_of_int n) ^ " not found (" ^ s ^ ")\n");
      Display.Text.display_history_tree "" t;
      internal_error ("failed to find history hypothesis (" ^ s ^ ")")

(* Rebuild the derivation tree *)

let rec get_subterm t pos_l =
  match t, pos_l with
  | _, [] -> t
  | Var { link = TLink t' }, _ -> get_subterm t' pos_l
  | Var _, _ -> Parsing_helper.internal_error "[history.ml >> get_subterm] Incorrect position"
  | FunApp(_,args),i::q_pos ->
      let t' = List.nth args (i-1) in
      get_subterm t' q_pos

let copy_injectivity = function
  | DoubleIndex (n1,n2) -> DoubleIndex (n1,n2)
  | SingleIndex(concl,f,n) -> SingleIndex(copy_fact concl,copy_fact f,n)
  | NoIndex(concl) -> NoIndex(copy_fact concl)

let rec search_first_rule tree = match tree.desc with
  | FRule(n,label,constra,sons,constra_a,sons_a) -> tree, n,label,constra,sons,constra_a,sons_a
  | FEquation tree -> search_first_rule tree
  | _ -> Parsing_helper.internal_error "[history.ml >> search_first_rule] When adding an additional hypothesis, there must be a rule at the top."

let rec build_fact_tree = function
    Empty(f) ->
      let tmp_bound_vars = !current_bound_vars in
      current_bound_vars := [];
      let f' = copy_fact2 f in
      cleanup();
      current_bound_vars := tmp_bound_vars;
      { desc = FEmpty; thefact = f' }
  | Any(n, h) ->
      let t = build_fact_tree h in
      let d = get_desc "any" t n in
      begin
        try
          match d.thefact with
            Pred(p, a::r) when p.p_prop land Param.pred_ANY_STRICT != 0
              && p.p_prop land Param.pred_ANY == 0 ->
              (* The arguments of "any" facts must all be equal *)
              List.iter (fun b -> unify a b) r
          | _ -> ()
        with Unify -> raise (HistoryUnifyError("HistoryAny"))
      end;
      d.desc <- FHAny;
      t
  | HMaxHyp(n,h) ->
      let t = build_fact_tree h in
      let d = get_desc "maxhyp" t n in
      d.desc <- FRemovedWithMaxHyp;
      t
  | Removed(rem_count, dup_count, h) ->
      let t = build_fact_tree h in
      let d1 = get_desc "removed" t rem_count in
      let d2 = get_desc "removed" t dup_count in

      begin
      try
        unify_facts d1.thefact d2.thefact
      with Unify -> raise (HistoryUnifyError("HistoryRemoved"))
      end;
      d1.desc <- FRemovedWithProof d2;
      t
  | HEquation(n,leq,req,h) ->
     let t = build_fact_tree h in
     (* Copy the facts *)
     let tmp_bound_vars = !current_bound_vars in
     current_bound_vars := [];
     let leq' = copy_fact2 leq in
     let req' = copy_fact2 req in
     cleanup();
     current_bound_vars := tmp_bound_vars;
     if n = -1 then
       begin
        begin
          try
            unify_facts req' t.thefact
          with Unify -> raise (HistoryUnifyError("HistoryEquation"))
        end;
        { desc = FEquation(t); thefact = leq' }
       end
     else
       begin
         let d = get_desc "equation" t n in
         begin
           try
             unify_facts leq' d.thefact
           with Unify -> raise (HistoryUnifyError("HistoryEquation2"))
         end;
         d.desc <- FEquation({ desc = FEmpty; thefact = req' });
         t
       end
  | Rule(n,descr,hyp,concl,constra) ->
      let tmp_bound = !current_bound_vars in
      current_bound_vars := [];
      let rhyp = List.map copy_fact hyp in
      let rconcl = copy_fact concl in
      let rconstra = copy_constra constra in
      let rdescr =
        match descr with
          ProcessRule(hypspec,name_params) ->
            ProcessRule(hypspec,List.map copy_term name_params)
        | x -> x
      in
      cleanup();
      current_bound_vars := tmp_bound;
      {
        desc = FRule(n, rdescr, rconstra, List.map (fun f -> { desc = FEmpty; thefact = f }) rhyp, true_constraints, []);
        thefact = rconcl;
      }
  | Resolution(h1, n, h2) ->
      let t1 = build_fact_tree h1 in
      let t2 = build_fact_tree h2 in
      let d = get_desc "resolution" t2 n in
      begin
        try
          unify_facts t1.thefact d.thefact
        with Unify -> raise (HistoryUnifyError("HistoryResolution"))
      end;
      d.desc <- t1.desc;
      t2
  | TestUnifTrue(n, h2) ->
      let t2 = build_fact_tree h2 in
      let d = get_desc "test_unif_true" t2 n in
      d.desc <- FRule(-1, TestUnif, true_constraints, [],true_constraints,[]);
      t2
  | HLemma(id_lem,matching_list,matching_sub_list,concl_lem,h) ->
      let t1 = build_fact_tree h in

      begin
        try
          let (m_l',sub_l',hyp_cl',constra_cl',eqs_cl') =
            Terms.auto_cleanup (fun () ->
              (* Create a copy of the lemma informations *)
              let m_l' = List.map (fun (i,f) -> (i,copy_fact f)) matching_list in
              let sub_l' = List.map (fun (t,t',pos_l) -> (copy_term t,copy_term t',pos_l)) matching_sub_list in
              let (hyp_cl,constra_cl,eqs_cl) = concl_lem in
              let hyp_cl' = List.map copy_fact hyp_cl in
              let constra_cl' = copy_constra constra_cl in
              let eqs_cl' = List.map (fun (t1,t2) -> copy_term t1, copy_term t2) eqs_cl in
              (m_l',sub_l',hyp_cl',constra_cl',eqs_cl')
            )
          in

          let fact_list_concl = Terms.fact_list_of_conclusion t1.thefact in

          (* Match the fact of the lemma's premise with the hypotheses of the clause *)
          List.iter (fun (i,fact_lem) ->
            let fact =
              if i < 0
              then List.nth fact_list_concl (-i-1)
              else Terms.unblock_predicate_fact ((get_desc "lemma" t1 i).thefact)
            in
            let fact_lem' = match fact_lem, fact with
              | Pred(f1,[ev]), Pred(f2,_) when f1 == Param.event_pred && f2 == Param.inj_event_pred ->
                              Pred(Param.inj_event_pred,[ev;Var(Terms.new_var "endocc" Param.occurrence_type)])
              | _, _ -> fact_lem
            in
            (* Printf.printf "History building: ";
            Display.Text.display_fact fact_lem';
            Printf.printf " and ";
            Display.Text.display_fact fact;
            Printf.printf "\n"; *)
            unify_facts_phase fact_lem' fact
          ) m_l';

          (* Match the subterm fact of the lemma's premise *)
          List.iter (fun (t_sub,t,pos_l) ->
            let t_at_pos = get_subterm t pos_l in
            unify t_sub t_at_pos
          ) sub_l';

          (* Unify the equalities *)
          List.iter (fun (t1,t2) -> unify t1 t2) eqs_cl';
          (* Copy, applying the substitution to the conclusion of the lemma *)
          let hyp_cl'' = List.map copy_fact4 hyp_cl' in
          let constra_cl'' = copy_constra4 constra_cl' in

          let (t2,n,label,constra,sons,constra_a,sons_a) = search_first_rule t1 in

          t2.desc <- FRule(n,label,constra,sons,wedge_constraints constra_a constra_cl'',sons_a @ (List.map (fun f -> { desc = FEmpty; thefact = f}) hyp_cl''));
          t1
        with Unify -> raise (HistoryUnifyError("HLemma"))
      end
  | HCaseDistinction(concl,hypl,subst,constra,h) ->
      let tree = build_fact_tree h in

      begin
        try
          (* Create a copy of the informations *)
          let (concl',hypl',subst',constra') =
            Terms.auto_cleanup (fun () ->

              let concl' = copy_fact concl in
              let hypl' = List.map copy_fact hypl in
              let subst' = List.map (fun (t1,t2) -> copy_term t1, copy_term t2) subst in
              let constra' = copy_constra constra in
              (concl',hypl',subst',constra')
            )
          in

          (* Unify the conclusion *)
          unify_facts tree.thefact concl';

          (* Unify the hypotheses *)
          List.iteri (fun n f ->
            let d = get_desc "verification" tree n in
            unify_facts d.thefact f
          ) hypl';

          (* Unify the equalities from the substitutions *)
          List.iter (fun (t1,t2) -> unify t1 t2) subst';

          (* Copy the added elements *)
          let constra'' = copy_constra4 constra' in

          let (tree',n,label,constra,sons,constra_a,sons_a) = search_first_rule tree in

          tree'.desc <- FRule(n,label,constra,sons,wedge_constraints constra_a constra'',sons_a);
          tree
        with Unify -> raise (HistoryUnifyError("HVerification"))
      end
  | HInjectivity(injectivity,h) ->
      let tree = build_fact_tree h in

      begin
        try
          (* Create a copy of the informations *)
          let injectivity' = Terms.auto_cleanup (fun () -> copy_injectivity injectivity) in

          begin match injectivity' with
            | DoubleIndex(n1,n2) ->
                let d1 = get_desc "HInjectivity" tree n1 in
                let d2 = get_desc "HInjectivity" tree n2 in
                unify_facts d1.thefact d2.thefact
            | SingleIndex(concl,f,n) ->
                let d = get_desc "HInjectivity" tree n in
                unify_facts tree.thefact concl;
                unify_facts d.thefact f
            | NoIndex(concl) -> unify_facts tree.thefact concl
          end;

          tree
        with Unify -> raise (HistoryUnifyError("HInjectivity"))
      end
  | HNested(n_list,nb_f_in_concl,h) ->
      let tree = build_fact_tree h in

      begin
        try
          let fact_list_concl = Terms.fact_list_of_conclusion tree.thefact in
          let fact_list_concl2 =
            List.map (function
              | Pred(p,[ev]) when p == Param.event_pred -> Pred(Param.event_pred_block,[ev])
              | Pred(p,[ev;occ]) when p == Param.inj_event_pred -> Pred(Param.inj_event_pred_block,[ev;occ])
              | pred -> pred
            ) fact_list_concl
          in

          List.iteri (fun i i_match ->
            let fact =
              if i_match < 0
              then List.nth fact_list_concl2 (-i_match-1)
              else (get_desc "nested" tree i_match).thefact
            in
            let fact_nested = List.nth fact_list_concl2 (i+nb_f_in_concl) in
            unify_facts fact fact_nested
          ) n_list;

          tree
        with Unify -> raise (HistoryUnifyError("HNested"))
      end


(** [revise_tree step_name recheck tree] checks that the derivation [tree]
    is still an attack against the considered property.
It rechecks inequality constraints.
It also rechecks that the derivation still contradicts the desired security
property.
For non-interference or weak secrets, that's ok: we still have a
derivation of "bad".
For correspondences, that may be wrong, because unification may
make arguments of some events equal, for instance.
In case [tree] does not satisfy these checks, [revise_tree] raises
[TermsEq.FalseConstraint].
When it does, [revise_tree] returns an updated version of [tree].

    [recheck] is either [None] or [Some recheck_fun], where [recheck_fun] is
    a function that takes a clause as argument and returns false when
    the clause contradicts the current query, true when it does not
    contradict it. **)

(* [get_clause_from_derivation] rebuilds a Horn clause from a derivation *)

let get_clause_from_derivation tree =
  let concl = tree.thefact in
  let hyp = ref [] in
  let constra = ref true_constraints in

  let rec rebuild_hyp tree = match tree.desc with
    | FEmpty ->
        if not (List.exists (Termslinks.equal_facts_with_links tree.thefact) (!hyp)) then
          hyp := tree.thefact :: (!hyp)
    | FHAny | FRemovedWithProof _ | FRemovedWithMaxHyp -> ()
    | FEquation son -> rebuild_hyp son
    | FRule(_, _, rconstra, sons,constra_a,sons_a) ->
        List.iter rebuild_hyp sons;
        List.iter rebuild_hyp sons_a;
        constra := wedge_constraints rconstra !constra;
        constra := wedge_constraints constra_a !constra
  in
  rebuild_hyp tree;

  let (hyp', concl', constra') =
    (List.map Terms.copy_fact4 (!hyp),
     Terms.copy_fact4 concl,
     Terms.copy_constra4 !constra)
  in
  let (hyp'',concl'',constra'') =
    try
      TermsEq.simplify_constraints (fun c ->
        hyp', concl', c
      ) (fun c ->
        List.map Terms.copy_fact4 hyp', Terms.copy_fact4 concl', c
      ) (concl'::hyp') constra'
    with TermsEq.FalseConstraint ->
      Parsing_helper.internal_error "False constraints should have been excluded by revise_tree"
  in
  let hist = Rule(-1, LblNone, hyp'', concl'', constra'') in

  (hyp'', concl'', hist, constra'')

exception Loop

let rec find_fact f t =
  if
    (match t.desc with
      FHAny | FEmpty | FRemovedWithProof _ | FRemovedWithMaxHyp -> false
    | _ -> true) && (Reduction_helper.equal_facts_modulo f t.thefact) then t else
  match t.desc with
    FEquation son -> find_fact f son
  | FRule(_,_,_,sons,_,sons_a) ->
      begin
        try
          find_fact_list f sons
        with Not_found -> find_fact_list f sons_a
      end
  | _ -> raise Not_found

and find_fact_list f = function
    [] -> raise Not_found
  | a::l ->
      try
        find_fact f a
      with Not_found ->
        find_fact_list f l


type recheck_t = (reduction -> bool) option

let revise_tree stepname recheck tree =
  let rec revise_tree_rec accu_constraint no_loop t =
    if List.memq t no_loop then
      raise Loop
    else
      { desc =
        begin
          match t.desc with
            FHAny | FEmpty | FRemovedWithMaxHyp ->
              begin
                match t.thefact with
                  Pred(p, l) when List.for_all (fun t' -> (match Reduction_helper.follow_link t' with Var _ -> true | _ -> false)) l -> t.desc
                | Pred(p,_) when p == Param.event_pred_block || p == Param.inj_event_pred_block || p == Param.event2_pred_block -> t.desc (* begin facts cannot be proved anyway *)
                | _ ->
                    (* When unification has lead to instantiating a fact that need not be proved before, try to find a proof for it. *)
                    try
                      (revise_tree_rec accu_constraint (t::no_loop) (find_fact t.thefact tree)).desc
                    with Not_found | Loop -> FEmpty
              end
          | FRule(n, tags, constra, sons, constra_a, sons_a) ->
              accu_constraint := wedge_constraints constra_a (wedge_constraints constra !accu_constraint);
              FRule(n, tags, constra, List.map (revise_tree_rec accu_constraint no_loop) sons, constra_a, List.map (revise_tree_rec accu_constraint no_loop) sons_a)
          | FRemovedWithProof t ->  FRemovedWithProof t
          | FEquation son -> FEquation(revise_tree_rec accu_constraint no_loop son)
        end;
        thefact = t.thefact
       }
  in
  let accu_constra = ref true_constraints in
  let tree' = revise_tree_rec accu_constra [] tree in
  begin
    try
      let constra = Terms.auto_cleanup (fun () -> Terms.copy_constra2 !accu_constra) in
      TermsEq.check_constraints constra
    with TermsEq.FalseConstraint ->
      Display.Def.print_line "Unification made an inequality become false.";
      raise TermsEq.FalseConstraint
  end;
  match recheck with
    None -> tree'
  | Some recheck_fun ->
      let cl' = get_clause_from_derivation tree' in
      Display.Def.print_line ("The clause after " ^ stepname ^ " is");
      if !Param.html_output then
        Display.Html.display_rule cl'
      else
        Display.Text.display_rule cl';
      if Terms.auto_cleanup (fun () -> recheck_fun cl') then
        begin
          (* cl' no longer contradicts the query *)
          Display.Def.print_line "This clause does not correspond to an attack against the query.";
          raise TermsEq.FalseConstraint
        end
      else
        begin
          Display.Def.print_line "This clause still contradicts the query.";
          tree'
        end

(* Display a derivation *)

let display_derivation new_tree1 = 
  incr Param.derivation_number;
  if !Param.html_output then
    begin

      let qs = string_of_int (!Param.derivation_number) in
      if !Param.abbreviate_derivation then
        begin
          let (abbrev_table, new_tree2) = Display.abbreviate_derivation new_tree1 in
          (* Display short derivation *)
          Display.auto_assign_abbrev_table (fun () ->
            Display.LangHtml.openfile ((!Param.html_dir) ^ "/derivation" ^ qs ^ ".html") ("ProVerif: derivation for query " ^ qs);
            Display.Html.print_string "<H1>Derivation</H1>\n";
            Display.Html.display_abbrev_table abbrev_table;
            Display.Html.display_history_tree "" new_tree2;
            Display.LangHtml.close();
            Display.Html.print_string ("<A HREF=\"derivation" ^ qs ^ ".html\">Derivation</A> ");
              (* Display explained derivation *)
            Display.LangHtml.openfile ((!Param.html_dir) ^ "/derivationexplained" ^ qs ^ ".html") ("ProVerif: derivation for query " ^ qs);
            Display.Html.print_string "<H1>Explained derivation</H1>\n";
            Display.Html.display_abbrev_table abbrev_table;
            Display.Html.explain_history_tree new_tree2;
            Display.LangHtml.close();
            Display.Html.print_string ("<A HREF=\"derivationexplained" ^ qs ^ ".html\">Explained derivation</A><br>\n")
              ) abbrev_table
        end
      else
        begin
          (* Display short derivation *)
          Display.LangHtml.openfile ((!Param.html_dir) ^ "/derivation" ^ qs ^ ".html") ("ProVerif: derivation for query " ^ qs);
          Display.Html.print_string "<H1>Derivation</H1>\n";
          Display.Html.display_history_tree "" new_tree1;
          Display.LangHtml.close();
          Display.Html.print_string ("<A HREF=\"derivation" ^ qs ^ ".html\">Derivation</A> ");
          (* Display explained derivation *)
          Display.LangHtml.openfile ((!Param.html_dir) ^ "/derivationexplained" ^ qs ^ ".html") ("ProVerif: derivation for query " ^ qs);
          Display.Html.print_string "<H1>Explained derivation</H1>\n";
          Display.Html.explain_history_tree new_tree1;
          Display.LangHtml.close();
          Display.Html.print_string ("<A HREF=\"derivationexplained" ^ qs ^ ".html\">Explained derivation</A><br>\n")
        end
    end
  else if !Param.display_derivation then
    begin
      Display.Text.newline ();
      Display.Text.print_line "Derivation:";
      if !Param.abbreviate_derivation then
        let (abbrev_table, new_tree2) = Display.abbreviate_derivation new_tree1 in
        Display.auto_assign_abbrev_table (fun () ->
          Display.Text.display_abbrev_table abbrev_table;
          if !Param.explain_derivation then
            Display.Text.explain_history_tree new_tree2
          else
            Display.Text.display_history_tree "" new_tree2
              ) abbrev_table
      else
        if !Param.explain_derivation then
          Display.Text.explain_history_tree new_tree1
        else
          Display.Text.display_history_tree "" new_tree1;
      Display.Text.newline()
    end

(* [build_history recheck clause] builds a derivation for the clause
   [clause] using the history stored in that clause.
   When the depth or number of hypotheses of clauses is bounded,
   it may in fact return a derivation for an instance of [clause].
   In this case, it uses [recheck] to verify that the obtained
   clause still contradicts the desired security property.
   Raises [Not_found] in case of failure *)

let build_history recheck (subgoals, orig_fact, hist_done, constra) =
  assert (!current_bound_vars == []);
  if not (!Param.reconstruct_derivation) then
    begin
      if !Param.typed_frontend then
        Display.Text.print_line "I do not reconstruct derivations.\nIf you want to reconstruct them, add\n   set reconstructDerivation = true. \nto your script."
      else
        Display.Text.print_line "I do not reconstruct derivations.\nIf you want to reconstruct them, add\n   param reconstructDerivation = true. \nto your script.";
      raise Not_found
    end
  else
  try
    let new_tree0 = build_fact_tree hist_done in
    let new_tree1 =
      if !Param.simplify_derivation then
        begin
          TreeHashtbl.clear tree_hashtbl;
          let r = simplify_tree new_tree0 in
          TreeHashtbl.clear tree_hashtbl;
          r
        end
      else
        new_tree0
    in
    display_derivation new_tree1;
    if ((!Param.max_hyp) >= 0) || ((!Param.max_depth) >= 0) then
      begin
        try
          revise_tree "construction of derivation" recheck new_tree1
        with TermsEq.FalseConstraint ->
          print_string "You have probably found a false attack due to the limitations\non depth of terms and/or number of hypotheses.\nI do not know if there is a real attack.\n";
          if !Param.html_output then
            Display.Html.print_line "You have probably found a false attack due to the limitations\non depth of terms and/or number of hypotheses.\nI do not know if there is a real attack.";
          cleanup();
          raise Not_found
      end
    else
      new_tree1
  with HistoryUnifyError s ->
      if ((!Param.max_hyp) >= 0) || ((!Param.max_depth) >= 0) then
      begin
        print_string "You have probably found a false attack due to the limitations\non depth of terms and/or number of hypotheses.\nI do not know if there is a real attack.\n";
        if !Param.html_output then
          Display.Html.print_line "You have probably found a false attack due to the limitations\non depth of terms and/or number of hypotheses.\nI do not know if there is a real attack.";
        cleanup();
        raise Not_found
      end
      else
        internal_error ("Unification failed in history rebuilding ("^s^")")


(* [unify_derivation next_f recheck tree] implements a heuristic
   to find traces more often, especially with complex protocols:
   it unifies rules of the derivation [tree] when possible.
   It calls [next_f] with the obtained derivation.
   Note that success is not guaranteed; however, when the heuristic fails,
   the derivation does not correspond to a trace.

This heuristic can break inequality constraints.
We recheck them after modifying the derivation tree.
We also recheck that the derivation still contradicts the security
property after unification, using the function [recheck].

When the heuristic fails or these checks fail, we still try to reconstruct
a trace from the original derivation, by calling [next_f tree]. *)

(* [simplify_tree] unifies facts with same session identifier *)

(* [first] is true when this is the first call to simplify_tree.
   In this case, if we find no unification to do, we do not need to call
   revise_tree, since the derivation has not been modified at all *)

module HashFactId =
  struct

    type factIdElem =
        HypSpec of hypspec
      |	Term of term

    type t =
      { hash : int;
        factId : factIdElem list;
        hyp_spec : hypspec list
      }

    let equalFactIdElem a b =
      match (a,b) with
        HypSpec h, HypSpec h' -> h = h'
      |	Term t, Term t' -> Termslinks.equal_terms_with_links t t'
      |	_ -> false

    let equal a b =
      (List.length a.factId == List.length b.factId) &&
      (List.for_all2 equalFactIdElem a.factId b.factId)

    type skel_f =
      SFixed of string
    | SRenamable of string * int

    type skel_term =
        SVar of string * int
      |	SFun of skel_f * skel_term list

    type skel_factIdElem =
        SHypSpec of hypspec
      |	STerm of skel_term

    let skel_f f =
      match f.f_name with
        Fixed s -> SFixed s
      | Renamable id -> SRenamable(id.name, id.idx)

    let rec skeleton_term = function
        Var b ->
          begin
            match b.link with
              TLink t -> skeleton_term t
            | NoLink -> SVar(b.vname.name, b.vname.idx)
            | _ -> Parsing_helper.internal_error "unexpected link in skeleton_term"
          end
      |	FunApp(f,l) ->
          match f.f_cat with
            Name _ -> SFun(skel_f f,[])
          | _ -> SFun(skel_f f, List.map skeleton_term l)

    let skeleton_factIdElem = function
        HypSpec x -> SHypSpec x
      |	Term t -> STerm(skeleton_term t)

    let hash a = a.hash

    (* build a HashFactId.t from a fact id *)

    let build fid hyp_spec = 
      { hash = Hashtbl.hash(List.map skeleton_factIdElem fid);
        factId = fid;
        hyp_spec = hyp_spec }

  end

module FactHashtbl = Hashtbl.Make(HashFactId)

let display_unified_variables useful_vars =
  (* Swap links to avoid displaying useless variables *)
  let old_links = ref [] in
  List.iter (fun x ->
    match x.link with
    | TLink t ->
	let rec follow_var = function
	  | Var y ->
	      begin
		match y.link with
		| TLink t' -> follow_var t'
		| NoLink -> Some y
		| _ -> assert false
	      end
	  | _ -> None
	in
	begin
	match follow_var t with
	| Some y ->
	    if not (List.memq y useful_vars) then
	      begin
		old_links := (x, x.link) :: (y, NoLink) :: (!old_links);
		y.link <- TLink (Var x);
		x.link <- NoLink
	      end
	| None -> ()
	end
    | _ -> ()
	    ) useful_vars;
  (* Display the unification *)
  let has_unif = ref false in
  List.iter (fun x -> 
    match x.link with
    | NoLink -> ()
    | TLink t ->
	has_unif := true;
	if !Param.html_output then
	  begin
            Display.Html.print_string "Unified ";
            Display.Html.display_var x;
            Display.Html.print_string " with ";
            Display.Html.WithLinks.term t;
            Display.Html.newline()
	  end
	else
	  begin
	    Display.Text.print_string "Unified ";
            Display.Text.display_var x;
            Display.Text.print_string " with ";
            Display.Text.WithLinks.term t;
            Display.Text.newline()
	  end
    | _ -> Parsing_helper.internal_error "[history.ml >> display_unified_variables] Unexpected link."
	    ) useful_vars;
  (* Restore the links *)
  List.iter (fun (x,l) ->
    x.link <- l
	    ) (!old_links);
  !has_unif

let f_err f1 f2 hyp_spec () =
  let loc_found, occ, loc_precise =
    match hyp_spec with
    | (OutputTag occ | InsertTag occ | InputPTag occ | OutputPTag occ | EventTag occ) :: _ 
    | BeginFact :: (EventTag occ) :: _ ->
	"", occ, "Try adding a [precise] option on a previous input, table lookup or let...suchthat."
    | (InputTag occ) :: _ ->
	"at the input ", occ, "Try adding a [precise] option on it."
    | (GetTag occ) :: _ ->
	"at the table lookup ", occ, "Try adding a [precise] option on it."
    | (PreciseTag occ) :: _ ->
	"", occ, "You have already put a [precise] at that occurrence, but apparently, it was not enough."
    | (LetFilterTag occ) :: _ ->
	"at the let...suchthat ", occ, "Try adding a [precise] option on it."
    | _ -> assert false
  in
  if !Param.html_output then
    begin
      Display.Html.print_string "Unification of ";
      Display.Html.display_fact f1;
      Display.Html.print_string " and ";
      Display.Html.display_fact f2;
      Display.Html.print_string (" failed or made a constraint become false "^loc_found^"at occurrence ");
      Display.Html.display_occ occ;
      Display.Html.newline ();
      Display.Html.print_line loc_precise
    end
  else
    begin
      Display.Text.print_string "Unification of ";
      Display.Text.WithLinks.fact f1;
      Display.Text.print_string " and ";
      Display.Text.WithLinks.fact f2;
      Display.Text.print_string (" failed or made a constraint become false "^loc_found^"at occurrence ");
      Display.Text.display_occ occ;
      Display.Text.newline ();
      Display.Text.print_line loc_precise
    end
      
let constraint_satisfiable constra = 
  try 
    TermsEq.check_constraints constra;
    true
  with TermsEq.FalseConstraint -> false

let simplify_tree_precise restwork_success restwork_failed err_msg_op constra tree =

  let rec one_round_unification useful_vars last_hashtbl = 
    let fact_hashtbl = FactHashtbl.create 7 in

    let add_and_cleanup_hashtbl f_next fact_id fact  = 
      try
        FactHashtbl.add fact_hashtbl fact_id fact;
        let r = f_next () in
        FactHashtbl.remove fact_hashtbl fact_id;
        r
      with x ->
        FactHashtbl.remove fact_hashtbl fact_id;
        raise x
    in

    let unify_fact restwork useful_vars f1 f2 =
      if f1 == f2 
      then restwork useful_vars
      else
        match f1, f2 with
        | Pred(p1,[t1;_]),Pred(p2,[t2;_]) when p1 == p2 && Param.inj_event_pred_block == p1 ->
	    let useful_vars_ref = ref useful_vars in
	    TermsEq.collect_unset_vars useful_vars_ref t1;
	    TermsEq.collect_unset_vars useful_vars_ref t2;
	    let useful_vars' = !useful_vars_ref in
            let record_current_bound_vars = !Terms.current_bound_vars in
            TermsEq.unify_modulo_save (fun () ->
              if record_current_bound_vars != !Terms.current_bound_vars && not (constraint_satisfiable constra)
              then raise Unify;
              restwork useful_vars'
            ) t1 t2
        | Pred(p1,l1), Pred(p2,l2) when p1 == p2 ->
	    let useful_vars_ref = ref useful_vars in
	    List.iter (TermsEq.collect_unset_vars useful_vars_ref) l1;
	    List.iter (TermsEq.collect_unset_vars useful_vars_ref) l2;
	    let useful_vars' = !useful_vars_ref in
            let record_current_bound_vars = !Terms.current_bound_vars in
            TermsEq.unify_modulo_list_save (fun () ->
              if record_current_bound_vars != !Terms.current_bound_vars && not (constraint_satisfiable constra)
              then raise Unify;
              restwork useful_vars'
            ) l1 l2
        | _ ->
            (** DEBUG : How can this happen ? Branch Else vs Branch Then ? **)
            Display.Def.print_line "Trying to unify incompatible facts in unifyDerivation; skipping this impossible unification.";
	    restwork useful_vars
    in

    let update_err_msg f = 
      match !err_msg_op with
      | Some _ -> ()
      | None -> err_msg_op := Some f
    in

    let unif_from_hash restwork useful_vars factId fact hyp_spec = 
      let fact_id = HashFactId.build factId hyp_spec in

      try 
        let fact' = FactHashtbl.find fact_hashtbl fact_id in
	try 
          unify_fact restwork useful_vars fact fact'
	with Unify -> 
          update_err_msg (f_err fact fact' hyp_spec);
          raise Unify
      with Not_found ->
	add_and_cleanup_hashtbl (fun () -> restwork useful_vars) fact_id fact
    in

    match last_hashtbl with
    | None -> 
        (* When it is the first time, we explore the tree *)

        let rec check_coherent restwork useful_vars factId (concl, hyp_spec, name_params, sons) =
          match hyp_spec with
            [] -> restwork useful_vars
          | h1::l1 ->
              let factId' = (HashFactId.HypSpec h1) :: factId in

              match h1 with
                ReplTag (occ,count_params) ->
                  (* the session identifier(s) is(are) part of the fact id *)
                  check_coherent restwork useful_vars ((HashFactId.Term (List.nth name_params count_params)) :: factId')
                    (concl, l1, name_params, sons)
              | OutputTag occ | InsertTag occ | InputPTag occ | OutputPTag occ | EventTag occ ->
                  if l1 == [] 
                  then
                    (* I'm reaching the conclusion *)
                    unif_from_hash restwork useful_vars factId' concl hyp_spec
                  else
                    check_coherent restwork useful_vars factId' (concl, l1, name_params, sons)
              | LetTag occ | TestTag occ | LetFilterTagElse occ | TestUnifTag2 occ | GetTagElse occ ->
                  check_coherent restwork useful_vars factId' (concl, l1, name_params, sons)
              | InputTag _ | GetTag _ | LetFilterTag _ | BeginFact | PreciseTag _ -> 
                  let fact = (List.hd sons).thefact in
                  unif_from_hash (fun useful_vars' ->
                    check_coherent restwork useful_vars' factId' (concl, l1, name_params, List.tl sons)
		  ) useful_vars factId' fact hyp_spec
              | TestUnifTag _ ->
                  check_coherent restwork useful_vars factId' (concl, l1, name_params, List.tl sons)
        in

        let rec check_coherent_tree restwork useful_vars t = 
          match t.desc with
          | FRule(_, ProcessRule(hyp_spec, name_params), constra, sons, _, _) ->
              check_coherent (fun useful_vars' ->
                check_coherent_tree_list restwork useful_vars' sons
              ) useful_vars [] (t.thefact, List.rev hyp_spec, List.rev name_params, List.rev sons);
          | FRule(_,_,_,sons,_,_) -> check_coherent_tree_list restwork useful_vars sons
          | FEquation son -> check_coherent_tree restwork useful_vars son
          | _ -> restwork useful_vars
        
        and check_coherent_tree_list restwork useful_vars = function
          | [] -> restwork useful_vars
          | t::q ->
              check_coherent_tree (fun useful_vars' ->
                check_coherent_tree_list restwork useful_vars' q
              ) useful_vars t
        in

        let record_current_bound_vars = !Terms.current_bound_vars in

        begin try
          check_coherent_tree (fun useful_vars' ->
            if record_current_bound_vars == !Terms.current_bound_vars
            then 
              (* No new unification *)
              restwork_success useful_vars'
            else
              (* Some unification occurred so check again for additional terms to unify *) 
              one_round_unification useful_vars' (Some fact_hashtbl)
          ) useful_vars tree
        with Unify -> 
          (* The unification failed the precise checks *)
          restwork_failed ()
        end
    | Some prev_hashtbl ->
        (* When we have a previous hashtbl, we can retrieve the element from the hashtbl. 
           Since we do not a iter by continuation, we first retrieve the element of the hash in a list  *)

        let elements = ref [] in
        FactHashtbl.iter (fun fact_id fact ->
          elements := (fact_id.factId,fact,fact_id.hyp_spec) :: !elements
        ) prev_hashtbl;

        let record_current_bound_vars = !Terms.current_bound_vars in

        let rec iter_tail useful_vars = function
          | [] -> 
              if record_current_bound_vars == !Terms.current_bound_vars
              then
                (* No variable instantiated so new unification possible *)
                restwork_success useful_vars
              else 
                (* Some unification occurred so check again for additional terms to unify *) 
                one_round_unification useful_vars (Some fact_hashtbl)
          | (factId,fact,hyp_spec)::q ->
              unif_from_hash (fun useful_vars' ->
                iter_tail useful_vars' q
              ) useful_vars factId fact hyp_spec
        in
        
        iter_tail useful_vars !elements
  in
  
  one_round_unification [] None
    
let rec simplify_tree_attacker restwork useful_vars constra tree =
  match tree.desc with
  | FEmpty | FHAny ->
      begin match tree.thefact with
        | Pred({p_info = AttackerGuess _ | AttackerBin _ }, [t1;t2]) ->
            if t1 == t2 || not (Terms.is_public t1) || not (Terms.is_public t2)
            then restwork useful_vars
            else 
              let record_current_bound_vars = !Terms.current_bound_vars in
              begin try
		let useful_vars_ref = ref useful_vars in
		TermsEq.collect_unset_vars useful_vars_ref t1;
		TermsEq.collect_unset_vars useful_vars_ref t2;
		let useful_vars' = !useful_vars_ref in
                TermsEq.unify_modulo_save (fun () ->
                  if record_current_bound_vars != !Terms.current_bound_vars && not (constraint_satisfiable constra)
                  then raise Unify;
                  restwork useful_vars'
                ) t1 t2
              with Unify -> 
                (* We try without unifying the two terms *)
                restwork useful_vars
              end
        | _ -> restwork useful_vars
      end
  | FRule(_,_,_,sons,_,_) -> simplify_tree_attacker_list restwork useful_vars constra sons
  | FEquation son -> simplify_tree_attacker restwork useful_vars constra son
  | _ -> restwork useful_vars
  
and simplify_tree_attacker_list restwork useful_vars constra = function
  | [] -> restwork useful_vars
  | t::q ->
      simplify_tree_attacker (fun useful_vars' ->
        simplify_tree_attacker_list restwork useful_vars' constra q
      ) useful_vars constra t

let simplify_tree restwork recheck tree = 
  let constra = Reduction_helper.collect_constraints tree in
  
  let err_msg = ref None in

  (* We apply a first simplification for precise *)
  simplify_tree_precise (fun useful_vars ->
    (* We check that the tree still satisfies the query before continuing. *)
    try 
      let has_unif = display_unified_variables useful_vars in
      let tree' = 
        if has_unif
        then revise_tree "UnifyDerivationPrecise" recheck tree 
        else tree
      in

      (* At that point, we try to unify unproved attackerBin and attackerGuess with public arguments. 
	 These unifications should not unify sid variables, so it is not necessary 
	 to retry [simplify_tree_precise].  *)
      simplify_tree_attacker (fun useful_vars ->
        try 
          let has_unif = display_unified_variables useful_vars in
          let tree'' = 
            if has_unif
            then revise_tree "UnifyDerivationAttackerBinGuess" recheck tree' 
            else tree'
          in
          restwork tree''
        with TermsEq.FalseConstraint -> 
          (* We do not try different combinations. To improve the search, one could check other combinations. *)
          Display.Def.print_line "Trying with the derivation tree after precise simplification instead.";
          restwork tree'
      ) [] constra tree'
    with TermsEq.FalseConstraint -> 
      (* No need to raise Unify to try different unifications as the verification of the query 
        is done modulo the equational theory. So in theory (could be checked) it should not be possible
        for the query to be falsified in another branch. *)
      Display.Def.print_line "Trying with the initial derivation tree instead.";
      Display.Def.print_line "Most probably, adding precise options may remove this derivation.";
      restwork tree
  ) (fun () ->
    (* When the unification for precise fails, we try with the initial tree *)
    begin match !err_msg with
      | None -> ()
      | Some f -> f ()
    end;
    Display.Def.print_line "Trying with the initial derivation tree instead.";
    restwork tree
  ) err_msg constra tree

let unify_derivation restwork recheck tree =
  let restwork tree' = 
    auto_cleanup (fun () -> restwork tree') 
  in
  auto_cleanup (fun () ->
    if !Param.unify_derivation then
      begin
        (* print_string "Starting unifyDerivation.\n"; *)
        if !Param.html_output then
          begin
            let qs = string_of_int (!Param.derivation_number) in
            Display.Html.print_string ("<A HREF=\"unifyDeriv" ^ qs ^ ".html\" TARGET=\"unifderiv\">Unify derivation</A><br>\n");
            Display.LangHtml.openfile ((!Param.html_dir) ^ "/unifyDeriv" ^ qs ^ ".html") ("ProVerif: unifying derivation for query " ^ qs);
            Display.Html.print_string "<H1>Unifying the derivation</H1>\n"
          end;

        simplify_tree (fun tree' ->
          if !Param.html_output then
            Display.LangHtml.close();
          restwork tree'
        ) recheck tree
      end
    else
      restwork tree
  )
