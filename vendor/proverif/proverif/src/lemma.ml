open Types
open Pitypes
open Reduction_helper

(****************************************
  Simplification of queries into lemmas
*****************************************)

(* The function [simplify_lemmas pi_st] considers the queries of [pi_st]
   and simplifies the lemmas accordingly into implied lemmas.
   For equivalence queries, a lemma is transformed into a restricted lemma
   (without events in its conclusion.).
   When the simplified lemma is of the form F => true then the exception
   [Useless_lemma] is raised.

   Applied only on encoded queries.
*)

exception Useless_lemma

let rec simplify_conclusion_query pi_state = function
  | QTrue -> QTrue
  | QFalse -> QFalse
  | QEvent(QSEvent(inj,ord_fun,occ,at,FunApp(f,args))) ->
      assert(inj = None && ord_fun = [] && occ = None && at = None);
      QEvent(QSEvent(None,[],None,None,FunApp(f,args)))
  | QEvent(QSEvent _) -> Parsing_helper.internal_error "Events should be function applications (lemma.ml, simplify_conclusion_query)"
  | QEvent _ | QConstraints _ as qev -> qev
  | NestedQuery _ -> Parsing_helper.internal_error "[lemma.ml >> simplify_conclusion_query] Lemmas should not contain nested queries."
  | QAnd(concl1,concl2) ->
      let concl1' = simplify_conclusion_query pi_state concl1
      and concl2' = simplify_conclusion_query pi_state concl2 in
      make_qand concl1' concl2'
  | QOr(concl1,concl2) ->
      let concl1' = simplify_conclusion_query pi_state concl1
      and concl2' = simplify_conclusion_query pi_state concl2 in
      make_qor concl1' concl2'

let simplify_realquery pi_state = function
  | Before(ev_l,concl_q) ->
      let concl_q' = simplify_conclusion_query pi_state concl_q in

      if concl_q' = QTrue
      then raise Useless_lemma;

      Before(ev_l,concl_q')

let simplify_query pi_state = function
  | RealQuery(q,[]), ext -> RealQuery(simplify_realquery pi_state q,[]), ext
  | _ -> Parsing_helper.internal_error "[lemma.ml >> simplify_query] Lemmas should have been encoded at that point, i.e. they should only be real query without public variables."

let simplify_lemmas pi_state =
  let original_axioms = ref [] in

  let rec simplify_t_lemma_list = function
    | [] -> []
    | t_lem :: q ->
        let q' = simplify_t_lemma_list q in
        try
          { t_lem with ql_query = simplify_query pi_state t_lem.ql_query } :: q'
        with Useless_lemma -> q'
  in

  let rec simplify_lemma_state = function
    | [] -> []
    | (LemmaToTranslate _) :: _ -> Parsing_helper.internal_error "[lemma.ml >> simplify_lemmas] Lemmas should have been translated at that point."
    | (Lemma lem_state)::q ->
        if lem_state.is_axiom = KAxiom || lem_state.is_axiom = KRestriction
        then
          original_axioms :=
            List.fold_left (fun acc lem -> match lem.ql_query with
              | RealQuery(rq,[]),ext -> ((rq,ext),lem_state.is_axiom = KAxiom)::acc
              | _ -> Parsing_helper.internal_error "[lemma.ml >> simplify_lemmas] Lemmas should have been encoded at that point."
            ) !original_axioms lem_state.lemmas;

        if lem_state.verif_app = LANone && lem_state.sat_app = LANone
        then simplify_lemma_state q
        else
          let lemmas_1 = simplify_t_lemma_list lem_state.lemmas in

          if lemmas_1 = []
          then simplify_lemma_state q
          else (Lemma { lem_state with lemmas = lemmas_1 }) :: (simplify_lemma_state q)
  in
  let simplified_lemmas = simplify_lemma_state pi_state.pi_lemma in

  { pi_state with
    pi_lemma = simplified_lemmas;
    pi_original_axioms = !original_axioms
  }

(* The function [simplify_queries_for_induction pi_st] consider the query
   of [pi_st] and simplifies it to see if it can be proved by induction.

   The function [Piauth.simplify_query] must provide a stronger query than
   the simplified queries produced in [Lemma.simplify_queries_for_induction],
   using [Lemma.simplify_induction_conclusion_query], because the proof of
   the query obtained by [Piauth.simplify_query] allows us to apply the
   inductive lemma.
   In particular, we simplify nested queries [e ==> concl] into conjunctions
   [e && concl] in both functions. *)

let rec simplify_induction_conclusion_query pi_state = function
  | QTrue -> QTrue
  | QFalse -> QFalse
  | QEvent(QSEvent(_,_,_,_,FunApp(f,args))) ->
      let fstatus = Pievent.get_event_status pi_state f in
      if fstatus.begin_status = WithOcc || fstatus.end_status = WithOcc
      then QTrue
      else QEvent(QSEvent(None,[],None,None,FunApp(f,args)))
  | QEvent(QSEvent _) ->
     Parsing_helper.internal_error "Events should be function applications (lemma.ml, simplify_induction_conclusion_query)"
  | QEvent(QFact(p,_,_,at)) as qev ->
      assert(at = None);
      qev
  | QEvent(QNeq((t1,_),_) | QEq((t1,_),_) | QGeq((t1,_),_) | QGr((t1,_),_)) when Terms.get_term_type t1 == Param.time_type -> QTrue
  | QEvent(QGr _) -> Parsing_helper.internal_error "[lemma.ml >> simplify_induction_conclusion_query] Strict inequalities can only occur between variables of type time."
  | QEvent(QSEvent2 _ | QNeq _ | QEq _ | QGeq _ | QIsNat _ ) | QConstraints _ as qev -> qev
  | NestedQuery(Before([e],concl)) ->
      simplify_induction_conclusion_query pi_state (QAnd(QEvent e, concl))
  | NestedQuery _ -> Parsing_helper.internal_error "[lemma.ml >> simplify_induction_conclusion_query] Nested queries should have exactly one premise."
  | QAnd(concl1,concl2) ->
      let concl1' = simplify_induction_conclusion_query pi_state concl1
      and concl2' = simplify_induction_conclusion_query pi_state concl2 in
      make_qand concl1' concl2'
  | QOr(concl1,concl2) ->
      let concl1' = simplify_induction_conclusion_query pi_state concl1
      and concl2' = simplify_induction_conclusion_query pi_state concl2 in
      make_qor concl1' concl2'

(* We are currently not allowing in the premise of the query injective event nor events with occurrences. *)
let allowed_pred = function
  | QSEvent(None,_,None,_,_) -> true
  | QSEvent _ -> false
  | QSEvent2 _ -> true
  | QFact(p,_,_,_) ->
      begin match p.p_info with
        | Attacker _ | Mess _ | Table _ | AttackerBin _ | MessBin _ | TableBin _ | UserPred _ -> true
        | _ -> false
      end
  | QNeq _ | QGeq _ | QIsNat _ -> true
  | QEq _ | QGr _ -> Parsing_helper.internal_error "[lemma.ml >> vars_and_allowed_pred] Equalities and strict inequalities between time variables should not occur in the premise of the query."

let simplify_queries_for_induction pi_state =
  let (_,q) = Param.get_process_query pi_state in

  let analyze q_l solve_status =
    let sat_app =
      (* When we want to prove all queries, or when there is a single
         query, we can apply it as induction hypothesis in the saturation *)
      if solve_status.s_max_subset && List.length q_l > 1
      then LANone
      else solve_status.s_ind_sat_app
    in

    if (sat_app = LANone && solve_status.s_ind_verif_app = LANone) || not solve_status.s_induction
    then pi_state
    else
      let (simplified_queries,_) =
        List.fold_left (fun (acc,i) -> function
          | (RealQuery(Before(evl,concl),[]), ext) ->
              if List.for_all allowed_pred evl
              then
                let simp_concl = simplify_induction_conclusion_query pi_state concl in
                if simp_concl <> QTrue
                then ({ ql_query = (RealQuery(Before(evl,simp_concl),[]),ext) ; ql_original_query = None; ql_real_or_random = None; ql_index_query_for_induction = Some i; ql_application_side = AllSide }::acc,i+1)
                else (acc,i+1)
              else (acc,i+1)
          | _ -> (acc,i+1)
        ) ([],0) q_l
      in

      if simplified_queries = []
      then pi_state
      else
        let lem_state =
          {
            lemmas = simplified_queries;
            is_axiom = KLemma;
            max_subset = solve_status.s_max_subset;
            verif_app = solve_status.s_ind_verif_app;
            sat_app = sat_app;
            induction = true;
            keep_axiom = false;
            remove_events = RENone;
          }
        in
        { pi_state with pi_lemma = (Lemma lem_state)::pi_state.pi_lemma}
  in

  match q with
    | CorrespQuery(q_l,solve_status) -> analyze q_l solve_status
    | CorrespQEnc(qql,solve_status) -> analyze (List.map (fun (_,q) -> q) qql) solve_status
    | NonInterfQuery _
    | WeakSecret _
    | ChoiceQuery | ChoiceQEnc _ -> pi_state
    | _ -> Parsing_helper.internal_error "[lemma.ml >> simplify_queries_for_induction] Queries should have been translated"

(****************************************************
  Detection of a lemma with choice for monoprocess
*****************************************************)

(* [convert_lemma_for_monoprocess lem] checks whether the bilemma corresponds in fact to
   a lemma on one side of the biprocess. If it is the case, it returns the lemma for the
   corresponding side of the biprocess (ql_application_side is set to LeftSide or RightSide).
   When it is not the case, [lem] is returned.

   Note that technically, a lemma could correspond to both sides of the biprocess.
    ex : lemma event(A(x,y)) ==> event(B(x',y'))
   But in this case, it is sufficient to prove only one side of the lemma. In the case
   the lemma would be proved on one side but not on the other, it means that the biprocess
   diverges before the premises are triggered and so the lemma would not help anyway in the
   proof of equivalence. *)
let convert_lemma_for_monoprocess lemma =

  let explore_one_side left_side evl concl_q =
    let vars_side_to_keep = ref [] in
    let vars_side_to_check = ref [] in

    let add_variables vars =
      (* We check that terms in side_to_check are just distinct variables *)
      List.iter (function
        | Var v ->
            if List.memq v !vars_side_to_check || List.memq v !vars_side_to_keep
            then raise Not_found;
            vars_side_to_check := v :: !vars_side_to_check
        | _ -> raise Not_found
      ) vars
    in

    let rec check_keep_variables = function
      | Var v ->
          if List.memq v !vars_side_to_check
          then raise Not_found;

          if not (List.memq v !vars_side_to_keep)
          then vars_side_to_keep := v :: !vars_side_to_keep
      | FunApp(_,args) -> List.iter check_keep_variables args
    in

    let analyse_events = function
      | QSEvent2(FunApp(f1,args1),FunApp(f2,args2)) ->
          assert (f1 == f2);
          let (side_to_check,side_to_keep) =  if left_side then (args2,args1) else (args1,args2) in
          add_variables side_to_check;
          List.iter check_keep_variables side_to_keep;
          QSEvent(None,[],None,None,FunApp(f1,side_to_keep))
      | QSEvent2 _ -> Parsing_helper.internal_error "[lemma.ml >> is_for_monoprocess] Argument of events should be a function application"
      | QFact(pred,_,args,at) ->
          assert(at = None);
          let (new_pred,side_to_check, side_to_keep) = match pred.p_info, args with
            | AttackerBin(n,ty), [t1;t2] ->
                let (side_to_check,side_to_keep) = if left_side then ([t2],[t1]) else ([t1],[t2]) in
                Param.get_pred (Attacker(n,ty)), side_to_check, side_to_keep
            | MessBin(n,ty), [tc1;t1;tc2;t2] ->
                let (side_to_check,side_to_keep) = if left_side then ([tc2;t2],[tc1;t1]) else ([tc1;t1],[tc2;t2]) in
                Param.get_pred (Mess(n,ty)), side_to_check, side_to_keep
            | TableBin n, [FunApp(tbl1,args1);FunApp(tbl2,args2)] ->
                let (side_to_check,side_to_keep) = if left_side then (args2,[FunApp(tbl1,args1)]) else (args1,[FunApp(tbl2,args2)]) in
                Param.get_pred (Table n), side_to_check, side_to_keep
            | Attacker _, _
            | Mess _, _
            | Table _, _
            | Subterm _, _ -> pred, [], args
            | _ , _ -> Parsing_helper.internal_error "[lemma.ml >> is_for_monoprocess] User defined predicates are not allowed for equivalence queries."
          in

          add_variables side_to_check;
          List.iter check_keep_variables side_to_keep;
          QFact(new_pred,[],side_to_keep,None)
      | (QNeq((t1,_),(t2,_)) | QEq((t1,_),(t2,_)) | QGeq((t1,_),(t2,_))) as p ->
          check_keep_variables t1;
          check_keep_variables t2;
          p
      | QIsNat t as p ->
          check_keep_variables t;
          p
      | QGr _ -> Parsing_helper.internal_error "[lemma.ml >> is_for_monoprocess] Should not have temporal comparison at this point."
      | QSEvent _ -> Parsing_helper.internal_error "[lemma.ml >> is_for_monoprocess] Event should have been translated into bievents at that point."
    in

    let rec analyse_concl = function
      | QTrue -> QTrue
      | QFalse -> QFalse
      | QConstraints constr -> Terms.iter_constraints check_keep_variables constr; QConstraints constr
      | QEvent ev -> QEvent (analyse_events ev)
      | NestedQuery _ -> Parsing_helper.internal_error "[lemma.ml >> is_for_monoprocess] Lemmas should not contain nested queries."
      | QAnd(concl1,concl2) -> QAnd(analyse_concl concl1, analyse_concl concl2)
      | QOr(concl1,concl2) -> QOr(analyse_concl concl1, analyse_concl concl2)
    in

    RealQuery(Before(List.map analyse_events evl, analyse_concl concl_q),[])
  in

  match lemma.ql_query with
    | (RealQuery(Before(evl,concl_q),_),ext) ->
        (* We try the left side *)
        begin
          try
            let rq = explore_one_side true evl concl_q in
            { lemma with ql_application_side = LeftSide; ql_query = (rq,ext) }
          with Not_found ->
            (* We try the right side *)
            try
              let rq = explore_one_side false evl concl_q in
              { lemma with ql_application_side = RightSide; ql_query = (rq,ext) }
            with Not_found -> lemma
        end
    | _ -> Parsing_helper.internal_error "[lemma.ml >> is_for_monoprocess] Lemmas should only be correspondence queries."

(****************************************
  Translate to bi-lemmas
*****************************************)

(* [encode_event_equiv qev] transforms the query event [qev] into a fact for
   biprocess. Note that we do not allow disequalities, inequalities and equalities
   to contain choice. Moreover, since we do not allow user defined predicates for
   equivalence proofs, only Attacker, Mess and Table can have choice. Finally,
   user defined predicates are always considered as true when used for equivalence proofs. *)
let encode_event_equiv min_choice_phase next_f = function
  | QSEvent(_,_,_,_,ev) ->
      let ev1 = Terms.choice_in_term 1 ev
      and ev2 = Terms.choice_in_term 2 ev in
      next_f (QSEvent2(ev1,ev2))
  | QSEvent2 _ -> Parsing_helper.internal_error "[lemma.ml >> encode_event_equiv] Event for biprocess should not occur before encoding."
  | QFact({p_info = Subterm _; _}, _,_,_) as pred -> next_f pred
  | QFact(pred,_,args,_) ->
      let n, bin_pred_spec =
        match pred.p_info with
        | Attacker(n,ty) -> n, AttackerBin(n,ty)
        | Mess(n,ty) -> n, MessBin(n,ty)
        | Table n -> n, TableBin n
        | _ -> raise Useless_lemma
      in
      let l1 = List.map (Terms.choice_in_term 1) args
      and l2 = List.map (Terms.choice_in_term 2) args in
      if n < min_choice_phase then
        TermsEq.unify_modulo_list (fun () -> next_f (QFact(pred,[],l1,None))) l1 l2
      else
        next_f (QFact(Param.get_pred bin_pred_spec,[], l1 @ l2,None))
  | (QNeq((t1,_),(t2,_)) | QGeq((t1,_),(t2,_))) as ev0 ->
      if Terms.has_choice t1 || Terms.has_choice t2
      then Parsing_helper.internal_error "Disequalities and inequalities in queries should not contain choice.";
      next_f ev0
  | (QIsNat t) as ev0 ->
      if Terms.has_choice t
      then Parsing_helper.internal_error "Predicates is_nat in queries should not contain choice.";
      next_f ev0
  | QEq _ | QGr _ ->
      Parsing_helper.internal_error "[lemma.ml >> encode_event_equiv] equalities and strict inequalities between time variables cannot occur before ==> in queries"

let rec encode_event_equiv_list min_choice_phase next_f = function
    [] -> next_f []
  | a::l ->
      encode_event_equiv min_choice_phase (fun a' ->
        encode_event_equiv_list min_choice_phase (fun l' -> next_f (a'::l')) l
          ) a

let rec encode_conclusion_query min_choice_phase = function
  | QTrue -> QTrue
  | QFalse -> QFalse
  | QConstraints q as constr -> 
    if Terms.exists_constraints Terms.has_choice q 
      then Parsing_helper.internal_error "Constraints should not contain choice.";
    constr
  | (QEvent e) as ev0 ->
      begin
        match e with
        | QSEvent(_,_,_,_,ev) ->
            let ev1 = Terms.choice_in_term 1 ev
            and ev2 = Terms.choice_in_term 2 ev in
            QEvent(QSEvent2(ev1,ev2))
        | QNeq((t1,_),(t2,_)) | QEq((t1,_),(t2,_)) | QGeq((t1,_),(t2,_)) ->
            if Terms.has_choice t1 || Terms.has_choice t2
            then Parsing_helper.internal_error "Disequalities, inequalities and equalities in queries should not contain choice.";
            ev0
        | QIsNat t ->
            if Terms.has_choice t
            then Parsing_helper.internal_error "Predicates is_nat in queries should not contain choice.";
            ev0
        | QFact(pred,_,args,_) ->
            begin
              try
                let n, bin_pred_spec = match pred.p_info with
                  | Attacker(n,ty) -> n, AttackerBin(n,ty)
                  | Mess(n,ty) -> n, MessBin(n,ty)
                  | Table n -> n, TableBin n
                  | _ -> raise Useless_lemma
                in
                let l1 = List.map (Terms.choice_in_term 1) args
                and l2 = List.map (Terms.choice_in_term 2) args in
                if n < min_choice_phase then
                  let f_tuple = Terms.get_tuple_fun (List.map Terms.get_term_type l1) in
                  let eq_fact = QEq((FunApp(f_tuple,l1),Parsing_helper.dummy_ext),(FunApp(f_tuple,l2),Parsing_helper.dummy_ext)) in
                  let qfact = QFact(pred,[],l1,None) in
                  QAnd(QEvent eq_fact,QEvent qfact)
                else
                  QEvent (QFact(Param.get_pred bin_pred_spec,[], l1 @ l2,None))
              with Useless_lemma -> QTrue
            end
        | _ -> QTrue
      end
  | NestedQuery _ -> Parsing_helper.internal_error "[lemma.ml >> encode_conclusion_query] Lemmas should not contain nested queries."
  | QAnd(concl1,concl2) ->
      let concl1' = encode_conclusion_query min_choice_phase concl1
      and concl2' = encode_conclusion_query min_choice_phase concl2 in
      make_qand concl1' concl2'
  | QOr(concl1,concl2) ->
      let concl1' = encode_conclusion_query min_choice_phase concl1
      and concl2' = encode_conclusion_query min_choice_phase concl2 in
      make_qor concl1' concl2'

let translate_to_bi_lemma pi_state =
  match pi_state.pi_min_choice_phase with
  | Unset ->
      (* When pi_min_choice_phase is unset at this point, the process is not a biprocess *)
      if (Reduction_helper.get_process pi_state).bi_pro then
        Parsing_helper.internal_error "[lemma.ml >> translate_to_bi_lemma] pi_min_choice_phase should be set";
      pi_state
  | Set min_choice_phase ->
      let new_lemmas =
        List.fold_left (fun acc1 -> function
          | LemmaToTranslate _ -> Parsing_helper.internal_error "[lemma.ml >> translate_to_bi_lemma] Lemmas should have been translated."
          | Lemma lem_state ->
              let lemma_list =
                List.fold_left (fun acc2 lem -> match lem.ql_query with
                | (RealQuery(Before(evl,concl_q),pubvars),ext) ->
                    begin
                      let concl_q' = encode_conclusion_query min_choice_phase concl_q in
                      if concl_q' = QTrue then
                        acc2
                      else
                        let accu = ref acc2 in
                      (* Generate all lemmas with the various unification possibilities
                         for terms *)
                        try
                          Terms.auto_cleanup (fun () ->
                            encode_event_equiv_list min_choice_phase (fun evl' ->
                              accu :=
                                { lem with
				  ql_query = (RealQuery(Terms.copy_realquery2 (Before(evl',concl_q')),pubvars), ext);
				  ql_original_query =
				  match lem.ql_original_query with
				  | (Some _) as previous_original -> previous_original
				  | None -> Some(lem.ql_query) } :: (!accu);
                              raise Terms.Unify) evl
					     )
                        with
                        | Terms.Unify ->
                            if !accu == acc2 then
                              begin
                                let l0 = Parsing_helper.get_extent_string true ext in
                                Display.Text.print_string l0;
                                Display.Text.print_string "Warning: lemma ";
                                Display.Text.display_corresp_secret_putbegin_query (fst lem.ql_query);
                                Display.Text.print_string " ignored because it uses choice in phases without choice, and the two sides do not unify.\n";
                                if !Param.html_output then
                                  begin
                                    Display.Html.print_string l0;
                                    Display.Html.print_string "Warning: lemma ";
                                    Display.Html.display_corresp_secret_putbegin_query (fst lem.ql_query);
                                    Display.Html.print_string " ignored because it uses choice in phases without choice, and the two sides do not unify.\n"
                                  end;
                              end;
                            !accu
                        | Useless_lemma -> acc2
                    end
                | _ -> acc2
                      ) [] lem_state.lemmas
              in
              if lemma_list = []
              then acc1
              else (Lemma { lem_state with lemmas = List.rev lemma_list })::acc1
                                                                               ) [] pi_state.pi_lemma
      in
      { pi_state with pi_lemma = List.rev new_lemmas }

(****************************************
  Encode lemmas
*****************************************)

let encode_lemmas pi_state pubvars ror_opt =
  let new_lemmas =
    List.fold_left (fun acc1 -> function
      | LemmaToTranslate _ -> Parsing_helper.internal_error "[lemma.ml >> encode_lemmas_for_correspondence] Lemmas should have been translated."
      | Lemma lem_state ->
          let lemma_list =
            List.fold_left (fun acc2 lem ->
              let same_ror = match ror_opt, lem.ql_real_or_random with
                | None, None -> true
                | Some vl, Some vl' -> Terms.same_term_lists vl vl'
                | _ -> false
              in
              if same_ror
              then
                begin match lem.ql_query with
                  | RealQuery(rq,pubvars'),ext when Terms.same_term_lists pubvars' pubvars ->
                      if pubvars = []
                      then lem::acc2
                      else { ql_query = (RealQuery(rq,[]), ext); ql_original_query = Some(lem.ql_query); ql_real_or_random = lem.ql_real_or_random; ql_index_query_for_induction = None; ql_application_side = AllSide } :: acc2
                  | _ ->
                      (* Lemmas that do not have the same public vars are ignored. *)
                      acc2
                end
              else
                (* Lemmas that do not correspond to the same query secret real_or_random are ignored. *)
                acc2
            ) [] lem_state.lemmas
          in
          if lemma_list = []
          then acc1
          else (Lemma { lem_state with lemmas = List.rev lemma_list })::acc1
    ) [] pi_state.pi_lemma
  in
  { pi_state with pi_lemma = List.rev new_lemmas }

let encode_lemmas_for_equivalence_queries pi_state =
  let new_lemmas =
    List.fold_left (fun acc1 -> function
      | LemmaToTranslate _ -> Parsing_helper.internal_error "[lemma.ml >> encode_lemmas_for_correspondence] Lemmas should have been translated."
      | Lemma lem_state ->
          let lemma_list =
            List.filter (fun lem -> match lem.ql_query, lem.ql_real_or_random with
              | (RealQuery(_,[]),_), None -> true
              | _ -> false
            ) lem_state.lemmas
          in
          if lemma_list = []
          then acc1
          else (Lemma { lem_state with lemmas = lemma_list })::acc1
    ) [] pi_state.pi_lemma
  in
  { pi_state with pi_lemma = List.rev new_lemmas }

(****************************************
  Translation of lemmas for horn clauses
*****************************************)

(* Copy functions *)

let copy_event = function
  | QSEvent(b,ord_fun,occ,at,t) -> QSEvent(b,ord_fun,Terms.copy_term_option occ,Terms.copy_term_e_option at,Terms.copy_term t)
  | QSEvent2(t1,t2) -> QSEvent2(Terms.copy_term t1, Terms.copy_term t2)
  | QFact(p,ord_fun,tl,at) -> QFact(p,ord_fun,List.map Terms.copy_term tl,Terms.copy_term_e_option at)
  | QNeq(t1,t2) -> QNeq(Terms.copy_term_e t1, Terms.copy_term_e t2)
  | QEq(t1,t2) -> QEq(Terms.copy_term_e t1, Terms.copy_term_e t2)
  | QGeq(t1,t2) -> QGeq(Terms.copy_term_e t1, Terms.copy_term_e t2)
  | QIsNat t -> QIsNat (Terms.copy_term t)
  | QGr _ -> Parsing_helper.internal_error "[lemma.ml >> copy_event] Lemma should not contain strict inequalities on time variables."

let rec copy_conclusion_query = function
  | QTrue -> QTrue
  | QFalse -> QFalse
  | QConstraints q -> QConstraints (Terms.map_constraints Terms.copy_term q)
  | QEvent e -> QEvent(copy_event e)
  | QAnd(concl1,concl2) -> QAnd(copy_conclusion_query concl1,copy_conclusion_query concl2)
  | QOr(concl1,concl2) -> QOr(copy_conclusion_query concl1,copy_conclusion_query concl2)
  | NestedQuery _ -> Parsing_helper.internal_error "[lemma.ml >> copy_hypelem] Lemma should not have nested queries."

let copy_realquery = function
  | Before(el, concl_q) -> Before(List.map copy_event el, copy_conclusion_query concl_q)

let copy_query = function
  | RealQuery(rq,[]),ext -> RealQuery(copy_realquery rq,[]),ext
  | _ -> Parsing_helper.internal_error "[lemma.lm >> copy_query] Should be a real query without public vars"

let copy_lemma lemma = { lemma with ql_query = copy_query lemma.ql_query }

let copy_lemma_state lem_state = { lem_state with lemmas = List.map copy_lemma lem_state.lemmas }

(* Verification of conditions on lemmas and queries *)

(* In a query 'F ==> H', F can contain function symbols
    that can be reduced by the equational theory only if 
    it does not introduce ambiguity in the conclusion.

    The query \psi ==> \phi must satisfy the following condition:
    if \rho is a fresh renaming of the variables of \psi
    then
      forall substitutions \sigma,
      \psi\sigma =_E \psi\rho\sigma implies \phi\sigma =_E \phi\rho\sigma
*)

let create_equations_premises_op_term acc = function
  | None -> ()
  | Some t -> acc := (t,Terms.copy_term t) :: !acc

let create_equations_premises_op_term_e acc = function
  | None -> ()
  | Some (t,_) -> acc := (t,Terms.copy_term t) :: !acc

let create_equations_premises acc = function
  | QSEvent(_,_,occ,x_t,ev) ->
      acc := (ev,Terms.copy_term ev) :: !acc;
      create_equations_premises_op_term acc occ;
      create_equations_premises_op_term_e acc x_t
  | QSEvent2(t1,t2) 
  | QGeq ((t1,_),(t2,_)) | QNeq ((t1,_),(t2,_)) ->
      acc := (t1,Terms.copy_term t1) :: (t2,Terms.copy_term t2) :: !acc
  | QFact(_,_,args,x_t) ->
      List.iter (fun t ->
        acc := (t,Terms.copy_term t) :: !acc 
      ) args;
      create_equations_premises_op_term_e acc x_t
  | QIsNat t ->
      acc := (t,Terms.copy_term t) :: !acc
  | _ -> Parsing_helper.internal_error "[lemma.ml >> create_equations_premisses] Unexpected element in the premises of queries, lemmas and axioms."

let rec follow_vlink = function
  | Var {link = VLink v; _ } -> Var v
  | FunApp(f,args) -> FunApp(f,List.map follow_vlink args)
  | t -> t

let create_equations_concl_term acc t = acc := (t,follow_vlink t) :: !acc

let create_equations_concl_term_e acc (t,_) = create_equations_concl_term acc t

let create_equations_concl_op_term acc = function
  | None -> ()
  | Some t -> acc := (t,follow_vlink t) :: !acc

let create_equations_concl_op_term_e acc = function
  | None -> ()
  | Some (t,_) -> acc := (t,follow_vlink t) :: !acc

let create_equations_concl_event acc = function
  | QSEvent(_,_,occ,x_t,ev) ->
      acc := (ev,follow_vlink ev) :: !acc;
      create_equations_concl_op_term acc occ;
      create_equations_concl_op_term_e acc x_t
  | QSEvent2(t1,t2) ->
      acc := (t1,follow_vlink t1) :: (t2,follow_vlink t2) :: !acc
  | QFact(_,_,args,x_t) ->
      List.iter (fun t ->
        acc := (t,follow_vlink t) :: !acc 
      ) args;
      create_equations_concl_op_term_e acc x_t
  | QNeq(t1,t2)
  | QEq(t1,t2)
  | QGeq(t1,t2)
  | QGr(t1,t2) ->
      create_equations_concl_term_e acc t1;
      create_equations_concl_term_e acc t2
  | QIsNat t -> acc := (t,follow_vlink t) :: !acc

let rec create_equations_concl acc = function
  | QTrue | QFalse -> ()
  | QConstraints q -> Terms.iter_constraints (create_equations_concl_term acc) q
  | QEvent ev -> create_equations_concl_event acc ev
  | NestedQuery (Before (evl,concl)) ->
      List.iter (create_equations_concl_event acc) evl;
      create_equations_concl acc concl
  | QAnd(concl1,concl2)
  | QOr(concl1,concl2) ->
      create_equations_concl acc concl1;
      create_equations_concl acc concl2


let rec put_constants2 = function
  | Var v ->
      begin match v.link with
        | TLink t -> put_constants2 t
        | NoLink ->
            v.link <- TLink (FunApp({ f_name = Renamable v.vname;
                                      f_type = [], v.btype;
                                      f_cat = SpecVar v;
                                      f_initial_cat = SpecVar v;
                                      f_private = false;
                                      f_options = 0;
                                      f_record = Param.fresh_record () }, []));
            Terms.current_bound_vars := v :: (!Terms.current_bound_vars)
        | _ -> Parsing_helper.internal_error "[terms.ml >> put_constants] Unexpected link."
      end
  | FunApp(f,l) -> List.iter put_constants2 l

let verify_deterministic cat (query,ext) = match query with
  | PutBegin _ | QSecret _ -> ()
  | RealQuery (Before(el,concl),_) -> 
      let eqs_premise = ref [] in 
      let eqs_concl = ref [] in   

      Terms.auto_cleanup (fun () ->
        List.iter (create_equations_premises eqs_premise) el;
        create_equations_concl eqs_concl concl
      );

      let (l1,l2) = List.split !eqs_premise in
    
      try 
        TermsEq.unify_modulo_list (fun () ->
          begin 
            Terms.auto_cleanup (fun () ->
              List.iter (fun (t1,t2) ->
                put_constants2 t1;
                put_constants2 t2
                  ) !eqs_concl;
              List.iter (fun (t1,t2) ->
		try 
                  TermsEq.unify_modulo (fun () -> ()) t1 t2
		with Terms.Unify -> 
		  print_string (Parsing_helper.get_extent_string true ext);
		  print_string ("Error in the "^cat^": ");
		  Display.Text.display_corresp_secret_putbegin_query query;
		  print_string ".\nThe term ";
		  Display.Text.display_term t1; (* Does not follow links, so displays the original term in the query *)
		  print_string (" in the conclusion of this "^cat^" is not determined by the premise of this "^cat^": it can take different values for the same value of the premise, due to the equational theory.\n");
		  Parsing_helper.user_error "Incorrect query"
                ) !eqs_concl
              )
          end;
          (* We raise unify to try all unifiers of the premise. *)
          raise Terms.Unify
        ) l1 l2
      with Terms.Unify -> () 

let verify_conditions_query query =
  verify_deterministic "query" query

let verify_conditions_lemma lem_state =
  List.iter (fun lem ->
    verify_deterministic "lemma or axiom" lem.ql_query
      ) lem_state.lemmas

(* Native axioms *)

let precise_action equiv ev_act id =
  let ty = match fst ev_act.f_type with
    | [_;ty] -> ty
    | _ -> Parsing_helper.internal_error "[lemma.ml >> precise_action] Event precise action should only have two arguments."
  in

  if equiv
  then
    let occ = Var(Terms.new_var ~orig:false "occ" Param.occurrence_type)
    and x = Var(Terms.new_var ~orig:false "x" ty)
    and y = Var(Terms.new_var ~orig:false "y" ty)
    and x' = Var(Terms.new_var ~orig:false "x'" ty)
    and y' = Var(Terms.new_var ~orig:false "y'" ty) in

    let ev1 = Pred(Param.event2_pred,[FunApp(ev_act,[occ;x]);FunApp(ev_act,[occ;x'])])
    and ev2 = Pred(Param.event2_pred,[FunApp(ev_act,[occ;y]);FunApp(ev_act,[occ;y'])]) in

    {
      l_index = id;
      l_premise = [ev1;ev2];
      l_subterms = [];
      l_constra = Terms.true_constraints;
      l_conclusion = [([],Terms.true_constraints,[x,y; x',y'])];
      l_verif_app = LAOnlyWhenInstantiate;
      l_sat_app = LAOnlyWhenInstantiate;
      l_induction = None;
      l_remove_events = RENone;
    }
  else
    let occ = Var(Terms.new_var ~orig:false "occ" Param.occurrence_type)
    and x = Var(Terms.new_var ~orig:false "x" ty)
    and y = Var(Terms.new_var ~orig:false "y" ty) in

    let ev1 = Pred(Param.event_pred,[FunApp(ev_act,[occ;x])])
    and ev2 = Pred(Param.event_pred,[FunApp(ev_act,[occ;y])]) in

    {
      l_index = id;
      l_premise = [ev1;ev2];
      l_subterms = [];
      l_constra = Terms.true_constraints;
      l_conclusion = [([],Terms.true_constraints,[x,y])];
      l_verif_app = LAOnlyWhenInstantiate;
      l_sat_app = LAOnlyWhenInstantiate;
      l_induction = None;
      l_remove_events = RENone;
    }

(* Translating functions *)

(* The translation of a lemma will apply the blocking predicates on the conclusion
  of the query but will leave the premise of the lemma with non-blocking predicates
  (this includes events). We could have made a exception for events but it seems
  better for uniformity. 
*)

type transl_state_lemma =
  {
    l_facts : fact list;
    l_constra : constraints;
  }

let transl_premise_event next_f = function
  | QSEvent(inj,ord_fun,occ,at,t) ->
      assert(inj = None && ord_fun = [] && occ = None && at = None);
      TermsEq.close_term_eq (fun t1 -> next_f (Pred(Param.event_pred,[t1]))) t
  | QSEvent2(t1,t2) ->
      TermsEq.close_term_eq (fun t1' ->
        TermsEq.close_term_eq (fun t2' ->
          next_f (Pred(Param.event2_pred,[t1';t2']))
        ) t2
      ) t1
  | QFact(p,_,tl,at) ->
      assert(at = None);
      TermsEq.close_term_list_eq (fun tl1 -> next_f (Pred(p,tl1))) tl
  | _ -> Parsing_helper.internal_error "[lemma.ml >> transl_premise_event] Premise of a lemma should not contain equalities or disequalities"

let rec transl_premise next_f = function
  | [] -> next_f [] Terms.true_constraints
  | QNeq ((t1,_),(t2,_)) ::q ->
      transl_premise (fun q' constra' -> 
        next_f q' (Terms.wedge_constraints (Terms.constraints_of_neq t1 t2) constra')  
      ) q
  | QGeq ((t1,_),(t2,_)) ::q ->
      transl_premise (fun q' constra' -> 
        next_f q' (Terms.wedge_constraints (Terms.constraints_of_geq t1 t2) constra')  
      ) q
  | QIsNat t ::q ->
      transl_premise (fun q' constra' -> 
        next_f q' (Terms.wedge_constraints (Terms.constraints_of_is_nat t) constra')  
      ) q
  | ev::q ->
      transl_premise_event (fun fact ->
        transl_premise (fun q' constra' -> next_f (fact::q') constra'
        ) q
      ) ev

(* All events and facts are replaced by their blocking predicate counterpart in
  the conclusion of the lemma. *)
let rec transl_conclusion_query next_f pi_state cur_state = function
  | QConstraints q -> next_f { cur_state with l_constra = Terms.wedge_constraints q cur_state.l_constra }
  | QTrue -> next_f cur_state
  | QFalse -> ()
  | QEvent(QSEvent(inj,ord_fun,occ,at,(FunApp(f,_) as t))) ->
      assert(inj = None && ord_fun = [] && occ = None && at = None);
      let fstatus = Pievent.get_event_status pi_state f in
      if fstatus.begin_status = WithOcc
      then
        let occ = Terms.new_var ~orig:false "o" Param.occurrence_type in
        TermsEq.close_term_eq (fun t1 ->
          next_f { cur_state with l_facts = Pred(Param.inj_event_pred_block,[t1;Var occ]) :: cur_state.l_facts }
        ) t
      else
        TermsEq.close_term_eq (fun t1 ->
          next_f { cur_state with l_facts = Pred(Param.event_pred_block,[t1]) :: cur_state.l_facts }
        ) t
  | QEvent(QSEvent _) -> Parsing_helper.internal_error "[lemma.ml >> transl_conclusion] Unexpected event"
  | QEvent(QSEvent2(t1,t2)) ->
      TermsEq.close_term_eq (fun t1' ->
        TermsEq.close_term_eq (fun t2' ->
          next_f { cur_state with l_facts = Pred(Param.event2_pred_block,[t1';t2']) :: cur_state.l_facts }
        ) t2
      ) t1
  | QEvent(QFact(p,ord_fun,args,at)) ->
      TermsEq.close_term_list_eq (fun args1 ->
        let block_p = Terms.get_blocking_predicate p in
        next_f { cur_state with l_facts = Pred(block_p,args1) :: cur_state.l_facts }
      ) args
  | QEvent(QNeq((t1,_),(t2,_))) -> next_f { cur_state with l_constra = { cur_state.l_constra with neq = [t1,t2] :: cur_state.l_constra.neq } }
  | QEvent(QGeq((t1,_),(t2,_))) ->
      assert(Terms.get_term_type t1 == Param.nat_type);
      TermsEq.close_term_eq (fun t1' ->
        TermsEq.close_term_eq (fun t2' ->
          next_f { cur_state with l_constra = { cur_state.l_constra with geq = (t1',0,t2') :: cur_state.l_constra.geq } }
        ) t2
      ) t1
  | QEvent(QGr _) -> Parsing_helper.internal_error "[lemma.ml >> transl_conclusion] Lemma should not contain strict inequalities."
  | QEvent(QIsNat t) ->
      assert(Terms.get_term_type t == Param.nat_type);
      TermsEq.close_term_eq (fun t' ->
        next_f { cur_state with l_constra = { cur_state.l_constra with is_nat = t' :: cur_state.l_constra.is_nat } }
      ) t
  | QEvent(QEq((t1,_),(t2,_))) ->
      TermsEq.close_term_eq (fun t1' ->
        TermsEq.close_term_eq (fun t2' ->
          try
            Terms.auto_cleanup (fun () ->
              Terms.unify t1' t2';
              next_f cur_state
            )
          with Terms.Unify -> ()
        ) t2
      ) t1
  | NestedQuery _ -> Parsing_helper.internal_error "[lemma.ml >> transl_conclusion] Lemma should not have nested queries."
  | QAnd(concl1,concl2) ->
      transl_conclusion_query (fun cur_state1 ->
        transl_conclusion_query next_f pi_state cur_state1 concl2
      ) pi_state cur_state concl1
  | QOr(concl1,concl2) ->
      transl_conclusion_query next_f pi_state cur_state concl1;
      transl_conclusion_query next_f pi_state cur_state concl2

let transl_realquery next_f pi_state = function
  | Before(ev_l,concl_q) ->
      transl_premise (fun premise constra_premise ->
        let vars_premise = ref [] in
        List.iter (Terms.get_vars_fact vars_premise) premise;

        let concl_accu = ref [] in
        let cur_state_0 = { l_facts = []; l_constra = Terms.true_constraints } in

        try
          transl_conclusion_query (fun cur_state1 ->
            try
              (* Follow the links *)
              let constra1 = Terms.copy_constra4 cur_state1.l_constra in
              let fact_list1 = List.map Terms.copy_fact4 cur_state1.l_facts in

              let keep_vars = ref !vars_premise in
              List.iter (Terms.get_vars_fact keep_vars) fact_list1;
              List.iter (fun v -> match v.link with
                | TLink t -> Terms.get_vars keep_vars (Terms.copy_term4 t)
                | _ -> ()
              ) !vars_premise;

              let next_step constra =
                let eq_list1 =
                  List.fold_left (fun acc v ->
                    match v.link with
                      | NoLink -> acc
                      | TLink t -> (Var v,Terms.copy_term4 t)::acc
                      | _ -> Parsing_helper.internal_error "[lemma.ml >> transl_realquery] Unexpected link."
                  ) [] !vars_premise
                in

                (* Removing simple equations *)

                Terms.auto_cleanup (fun () ->
                  let eq_list2 =
                    List.fold_left (fun acc (t1,t2) -> match t2 with
                      | Var v when v.link = NoLink && not (List.memq v !vars_premise) ->
                          Terms.link v (TLink t1);
                          acc
                      | _ -> (t1,t2)::acc
                    ) [] eq_list1
                  in

                  let eq_list3 = List.map (fun (t1,t2) -> t1, Terms.copy_term3 t2) eq_list2 in
                  let constra3 = Terms.copy_constra3 constra in
                  let fact_list2 = List.map Terms.copy_fact3 fact_list1 in

                  if eq_list3 = [] && Terms.is_true_constraints constra3 && fact_list2 = []
                  then
                    (* The conclusion is true so the we can discard this lemma as it is of the
                      form F_1 && ... && F_n ==> true || \phi *)
                    raise Useless_lemma;

                  concl_accu := (fact_list2,constra3,eq_list3) :: !concl_accu
                )
              in

              TermsEq.simplify_constraints_keepvars next_step next_step !keep_vars constra1
            with Terms.Unify | TermsEq.FalseConstraint -> ()
          ) pi_state cur_state_0 concl_q;
          next_f premise constra_premise !concl_accu
        with Useless_lemma -> ()
      ) ev_l

let rec transl_lemmas horn_state pi_state =
  let h_lemmas = ref [] in
  let pred_prove = ref horn_state.h_pred_prove in
  let nb_lemmas = ref 0 in
  let equiv = horn_state.h_solver_kind = Solve_Equivalence in

  let add_pred p =
    if not (List.memq p (!pred_prove)) then
      pred_prove := p :: (!pred_prove)
  in

  (* Adding the native precise actions *)
  List.iter (fun ev ->
    let lemma = precise_action equiv ev !nb_lemmas in
    incr nb_lemmas;
    h_lemmas := lemma :: !h_lemmas
  ) pi_state.pi_precise_actions;

  List.iter (function
    | Lemma lem_state ->
        let lem_state' = Terms.auto_cleanup (fun _ -> copy_lemma_state lem_state ) in
        (* Check that the lemmas does not contain destructor. Moreover, we also check that the
           function symbols of the premises are not reduced by the equational theory. *)
        verify_conditions_lemma lem_state';

        List.iter (fun lem -> match lem.ql_query with
        | RealQuery(rq,[]),_ ->
            (* Add predicates to [pred_prove]
               The predicates in assumptions of lemmas must be added
               to [pred_prove] because, when we apply a lemma,
               we must be sure that the predicate is actually true.
               Therefore, we must not resolve on this predicate in
               elimination of redundant clauses, to avoid removing
               a clause that does not have this predicate in hypothesis.

               Note that the predicates in conclusion of lemmas do not need to be
               added to [pred_prove] as they are all blocking predicates. In the
               theory, they are added to the set S_p of allowed predicates but
               this is mostly to ensures the satisfiability of the derivation.
               [pred_prove] is mostly used for the global redundancy so only need
               to contain non-blocking predicates.

               Queries proved by induction are already included in lemmas
               at this stage, so we do not need to handle them separately. *)
            let Before(hyp,_) = rq in
            List.iter (function
              | QSEvent _ | QSEvent2 _ | QFact({p_info = Subterm _; _},_,_,_) -> ()
              | QFact(p,_,_,_) -> add_pred p
              | QNeq _ | QGeq _ | QIsNat _ -> ()
              | _ -> Parsing_helper.internal_error "[lemma.ml >> transl_lemmas] Premise of a lemma should not contain equalities "
            ) hyp;

            transl_realquery (fun premise constra_premise concl ->
              let (subterm_facts,other_facts) = List.partition (function Pred({p_info = Subterm _;_},_) -> true | _ -> false) premise in
              let subterms =
                List.map (function
                  | Pred(_,[t1;t2]) -> (t1,t2)
                  | _ -> Parsing_helper.internal_error "[lemma.ml >> transl_lemmas] Unexpected number of arguments."
                ) subterm_facts
              in
              let lemma =
                {
                  l_index = !nb_lemmas;
                  l_premise = other_facts;
                  l_subterms = subterms;
                  l_constra = constra_premise;
                  l_conclusion = concl;
                  l_verif_app = lem_state.verif_app;
                  l_sat_app = lem_state.sat_app;
                  l_induction = lem.ql_index_query_for_induction;
                  l_remove_events = lem_state.remove_events;
                }
              in
              incr nb_lemmas;
              h_lemmas := lemma :: !h_lemmas
            ) pi_state rq
          | _ -> Parsing_helper.internal_error "[lemma.ml >> transl_lemmas] Unexpected query"
        ) lem_state.lemmas
    | LemmaToTranslate _ -> Parsing_helper.internal_error "[pitransl.ml >> transl_lemmas_for_correspondence] Lemma should be translated at this point."
  ) pi_state.pi_lemma;

  { horn_state with
    h_lemmas = List.rev !h_lemmas;
    h_pred_prove = !pred_prove }

(************************************************
  Verification of axioms on reconstructed trace
*************************************************)

let continue_searching ev state =
  match ev with
  | QFact({ p_info = Mess(n,_) | MessBin(n,_) | Table(n) | TableBin(n); _},_,_,_)
      when state.current_phase < n -> false
  | QEq _ | QNeq _ | QGeq _ | QIsNat _ -> false
  | _ -> true

let unify_hyp f_next ev state = match ev with
  (* attacker can occur only the premise of axioms and restrictions.
   When it occurs, we should look for terms that the attacker can compute
   and prove the axiom/restriction for all these terms.
   That's too complicated, so we exclude this case below and just do
   not verify such axioms/restrictions.
  | QFact({ p_info = [Attacker(n,_)]; _},_,[tq],_) when state.current_phase <= n->
      begin match state.comment with
        | RInput_Success(_,_,_,_,t)
        | ROutput_Success(_,_,_,t)
            (* RIO/RIO_PatRemove send on a public channel only when the adversary
               is passive. When the channel is public, the recipe is set to "Some ..." *)
        | RIO(_,_,_,_,_,Some _,t,_)
        | RIO_PatRemove(_,_,_,_,_,Some _,t,_,_) ->
            (* In case we work with biprocesses, in a phase < min_choice_phase,
               we may have a fact Attacker and still a biterm in the trace. *)
            let t1 = Terms.choice_in_term 1 t in
            let t2 = Terms.choice_in_term 2 t in
            TermsEq.unify_modulo_list f_next [tq;t2] [t1;t1]
        | _ -> raise Terms.Unify
      end
  | QFact({ p_info = [AttackerBin(n,_)]; _},_,[tq1;tq2],_) when state.current_phase <= n->
      begin match state.comment with
        | RInput_Success(_,_,_,_,t)
        | ROutput_Success(_,_,_,t)
            (* RIO/RIO_PatRemove send on a public channel only when the adversary
               is passive. When the channel is public, the recipe is set to "Some ..." *)
        | RIO(_,_,_,_,_,Some _,t,_)
        | RIO_PatRemove(_,_,_,_,_,Some _,t,_,_) ->
            let t1 = Terms.choice_in_term 1 t in
            let t2 = Terms.choice_in_term 2 t in
            TermsEq.unify_modulo_list f_next [tq1;tq2] [t1;t2]
        | _ -> raise Terms.Unify
      end
        *)
  | QFact({ p_info = Mess(n,_); _},_,[c;tq],_) when state.current_phase = n ->
      begin match state.comment with
        | RInput_Success(_,tc,_,_,t)
        | ROutput_Success(_,tc,_,t)
        | RIO(_,tc,_,_,_,_,t,_)
        | RIO_PatRemove(_,tc,_,_,_,_,t,_,_) ->
            (* In case we work with biprocesses, in a phase < min_choice_phase,
               we may have a fact Mess and still biterms in the trace. *)
            let t1 = Terms.choice_in_term 1 t in
            let t2 = Terms.choice_in_term 2 t in
            let tc1 = Terms.choice_in_term 1 tc in
            let tc2 = Terms.choice_in_term 2 tc in
            TermsEq.unify_modulo_list f_next [c;tc2;tq;t2] [tc1;tc1;t1;t1]
        | _ -> raise Terms.Unify
      end
  | QFact({ p_info = MessBin(n,_); _},_,[c1;tq1;c2;tq2],_) when state.current_phase = n ->
      begin match state.comment with
        | RInput_Success(_,tc,_,_,t)
        | ROutput_Success(_,tc,_,t)
        | RIO(_,tc,_,_,_,_,t,_)
        | RIO_PatRemove(_,tc,_,_,_,_,t,_,_) ->
            let t1 = Terms.choice_in_term 1 t in
            let t2 = Terms.choice_in_term 2 t in
            let tc1 = Terms.choice_in_term 1 tc in
            let tc2 = Terms.choice_in_term 2 tc in
            TermsEq.unify_modulo_list f_next [c1;c2;tq1;tq2] [tc1;tc2;t1;t2]
        | _ -> raise Terms.Unify
      end
  | QFact({ p_info = Table(n); _},_,[tq],_) when state.current_phase = n ->
      begin match state.comment with
        | RInsert_Success(_,t,_) ->
            (* In case we work with biprocesses, in a phase < min_choice_phase,
               we may have a fact Table and still a biterm in the trace. *)
            let t1 = Terms.choice_in_term 1 t in
            let t2 = Terms.choice_in_term 2 t in
            TermsEq.unify_modulo_list f_next [t1;t1] [tq;t2]
        | _ -> raise Terms.Unify
      end
  | QFact({ p_info = TableBin(n); _},_,[tq1;tq2],_) when state.current_phase = n ->
      begin match state.comment with
        | RInsert_Success(_,t,_) ->
            let t1 = Terms.choice_in_term 1 t in
            let t2 = Terms.choice_in_term 2 t in
            TermsEq.unify_modulo_list f_next [tq1;tq2] [t1;t2]
        | _ -> raise Terms.Unify
      end
  | QFact(p,_,args,_) when p.p_prop land Param.pred_BLOCKING != 0 ->
      (* The trace satisfies the blocking predicate in question,
         but we can not sure that the trace actually exists
         (because it depends on the real semantics of the blocking predicate).
         ProVerif will say "cannot be proved" anyway for this reason. *)
      begin match state.comment with
        | RLetFilter_In(_,[],[],Pred(p',args')) when p == p' -> TermsEq.unify_modulo_list f_next args args'
        | _ -> raise Terms.Unify
      end
  | QSEvent(_,_,_,_,ev') ->
      begin match state.comment with
        | REvent_Success(_,ev'',_) -> TermsEq.unify_modulo f_next ev' ev''
        | _ -> raise Terms.Unify
      end
  | QSEvent2(ev1,ev2) ->
      begin match state.comment with
        | REvent_Success(_,ev'',_) ->
            let ev1'' = Terms.choice_in_term 1 ev'' in
            let ev2'' = Terms.choice_in_term 2 ev'' in
            TermsEq.unify_modulo_list f_next [ev1;ev2] [ev1'';ev2'']
        | _ -> raise Terms.Unify
      end
  | QEq((t1,_),(t2,_)) -> TermsEq.unify_modulo f_next t1 t2
        (* Constraints QNeq, QGeq, QIs_nat are collected in [match_conclusion] and
           proved in [check_one_axiom], so we need not verify them here. *)
  | _ -> raise Terms.Unify

(* Event in match conclusion should be ground (no variables) *)
let rec match_conclusion restwork state ev =
  try
    unify_hyp restwork ev state
  with Terms.Unify ->
    if continue_searching ev state
    then
      match state.previous_state with
        | None -> raise Terms.Unify
        | Some state' -> match_conclusion restwork state' ev
    else raise Terms.Unify

let rec match_conclusion_query restwork state constra = function
  | QTrue -> restwork constra
  | QFalse -> raise Terms.Unify
  | QConstraints q -> restwork (Terms.wedge_constraints q constra)
  | QEvent (QNeq((t1,_),(t2,_))) ->
      restwork { constra with neq = [t1,t2]::constra.neq }
  | QEvent (QGeq((t1,_),(t2,_))) ->
      TermsEq.close_term_eq_synt (fun t1' ->
        TermsEq.close_term_eq_synt (fun t2' ->
          restwork { constra with geq = (t1',0,t2)::constra.geq }
        ) t2
      ) t1
  | QEvent (QIsNat t) ->
      TermsEq.close_term_eq_synt (fun t' ->
        restwork { constra with is_nat = t'::constra.is_nat }
      ) t
  | QEvent ev ->
      match_conclusion (fun () -> restwork constra) state ev
  | NestedQuery _ -> Parsing_helper.internal_error "[lemma.ml >> match_conclusion_query] Axioms should not contain nested correspondence"
  | QAnd(concl1,concl2) ->
      match_conclusion_query (fun constra1 ->
        match_conclusion_query restwork state constra1 concl2
      ) state constra concl1
  | QOr(concl1,concl2) ->
      try
        match_conclusion_query restwork state constra concl1
      with Terms.Unify ->
        match_conclusion_query restwork state constra concl2

let rec match_one_premise f_next state ev =
  try
    unify_hyp f_next ev state;
    raise Terms.Unify
  with Terms.Unify ->
    if continue_searching ev state
    then
      match state.previous_state with
        | None -> ()
        | Some state' -> match_one_premise f_next state' ev

let rec not_ground = function
  | Var { link = TLink t } -> not_ground t
  | Var _ -> true
  | FunApp(_,args) -> List.exists not_ground args

exception AxiomNotVerified

let rec cannot_be_verified_conclusion_query = function
  | QTrue | QFalse | QConstraints _ (* constraints can always be verified *)
  | QEvent(QNeq _ | QEq _ | QGeq _ | QIsNat _ | QSEvent _ | QSEvent2 _) -> false
  | QEvent(QFact({ p_info = UserPred _; _} as p,_,_,_)) when p.p_prop land Param.pred_BLOCKING != 0 -> false
  | QEvent(QFact({ p_info = Mess _ | MessBin _ | Table _ | TableBin _; _},_,_,_)) -> false
  | QEvent(QFact({ p_info = Attacker _ | AttackerBin _ | UserPred _ ; _},_,_,_)) -> true
  | QEvent(QFact _) -> Parsing_helper.internal_error "[lemma.ml >> cannot_be_verified_conclusion_query] Axioms and restrictions should only contain attacker, mess, table facts, events, user-defined predicates, inequalities, disequalities and equalities in their conclusion"
  | QEvent(QGr _) -> Parsing_helper.internal_error "[lemma.ml >> cannot_be_verified_conclusion_query] Axioms and restrictions should not contain time inequalities."
  | QAnd(concl1,concl2)
  | QOr(concl1,concl2) ->
      cannot_be_verified_conclusion_query concl1 ||
      cannot_be_verified_conclusion_query concl2
  | NestedQuery _ -> Parsing_helper.internal_error "[lemma.ml >> cannot_be_verified_conclusion_query] A lemma should not contain nested queries."

let cannot_be_verified_premise = function
  | QFact({ p_info = Subterm _ | Attacker _ | AttackerBin _ | UserPred _ ; _},_,_,_) -> true
  | QFact({ p_info = Mess _ | MessBin _ | Table _ | TableBin _; _},_,_,_) -> false
  | QNeq _ | QGeq _ | QIsNat _ -> false
  | QSEvent _ | QSEvent2 _ -> false
  | QFact _ | QEq _ | QGr _ -> Parsing_helper.internal_error "axioms and restrictions should only contain subterm, attacker, mess, table facts, events, user-defined predicates, disequalities, inequalities between natural numbers, or is_nat in their premise"

let cannot_be_verified = function
  | Before(evl,concl_q) as ax ->
      Reduction_helper.has_name_q ax ||
      List.exists cannot_be_verified_premise evl ||
      cannot_be_verified_conclusion_query concl_q

let check_one_axiom final_state is_axiom = function
  | Before(evl,concl_q) as ax, ext ->
      let str_axiom = if is_axiom then "axiom" else "restriction" in
      let display_warning () =
        Display.Text.newline();
        begin
          match Parsing_helper.get_extent true ext with
          | None ->
              Display.Text.print_line ("Warning: We could not verify that the following "^str_axiom^" is satisfied by the attack trace.");
          | Some s ->
              Display.Text.print_line ("Warning: We could not verify that the following "^str_axiom^", declared at "^s^", is satisfied by the attack trace.")
        end;
        Display.Text.display_corresp_query (Before(evl,concl_q));
        Display.Text.newline();
      in

      let rec match_premises constra_prem state = function
        | [] -> 
            (* Premise have been matched excepted the constraints *)
            let constra_prem1 = Terms.map_constraints TermsEq.remove_syntactic_term constra_prem in
            if not (TermsEq.check_closed_constraints constra_prem1)
            then raise Terms.Unify;

            (* All premise have been matched *)
            let exists_existential_vars = ref false in

            begin
            try
              match_conclusion_query (fun constra ->
                try
                  let constra1 = Terms.map_constraints TermsEq.remove_syntactic_term constra in
                  let constra2 =
                    TermsEq.simplify_constraints_keepvars (fun c -> c) (fun _ ->
                      Parsing_helper.internal_error "[lemma.ml >> check_one_axiom] Should not occur since we have kept no variables."
                    ) [] constra1
                  in
                  TermsEq.check_constraints constra2;

                  (* When there are still natural number in the constra, we cannot
                      correctly verify that the axiom is not verified by the trace.
                      In such a case, we will display a warning saying that we could not verify
                      the axiom *)

                  if Terms.exists_constraints not_ground constra2
                  then
                    begin
                      exists_existential_vars := true;
                      raise Terms.Unify
                    end;
                with TermsEq.FalseConstraint -> raise Terms.Unify
              ) state Terms.true_constraints concl_q;
            with Terms.Unify ->
              if !exists_existential_vars
              then
                begin
                  display_warning ();
                  if not is_axiom then raise AxiomNotVerified
                end
              else
                begin
                  Display.Text.newline();
                  begin
                    match Parsing_helper.get_extent true ext with
                    | None ->
                        Display.Text.print_line ("The attack trace does not satisfy the following declared "^str_axiom^":")
                    | Some s ->
                        Display.Text.print_line ("The attack trace does not satisfy the following "^str_axiom^", declared at "^s^":")
                  end;
                  Display.Text.display_corresp_query (Before(evl,concl_q));
                  Display.Text.newline();
                  raise AxiomNotVerified
                end
            end
        | QNeq ((t1,_),(t2,_))::q_ev ->
            match_premises (Terms.wedge_constraints (Terms.constraints_of_neq t1 t2) constra_prem) state q_ev
        | QGeq ((t1,_),(t2,_))::q_ev ->
            match_premises (Terms.wedge_constraints (Terms.constraints_of_geq t1 t2) constra_prem) state q_ev
        | QIsNat t :: q_ev ->
            match_premises (Terms.wedge_constraints (Terms.constraints_of_is_nat t) constra_prem) state q_ev
        | ev::q_ev ->
            match_one_premise (fun () ->
              match_premises constra_prem state q_ev
            ) state ev

      and match_state state prev_ev = function
        | [] ->
            begin match state.previous_state with
              | None -> ()
              | Some state' -> match_state state' [] evl
            end
        | ev::q_ev ->
            try
              unify_hyp (fun () -> match_premises Terms.true_constraints state (prev_ev @ q_ev)) ev state;
              raise Terms.Unify
            with Terms.Unify -> match_state state (ev::prev_ev) q_ev
      in

      try
        if cannot_be_verified ax
        then
          begin
            (* When an axiom contains a subterm fact or some bound names, we assume that it is verified. However, if it is
               a restriction, we assume that it is false.
               TODO : Improve the verification when there is no equational theory for subterms
               Similarly, when an axiom or restriction contains attacker(..) as premise, it is
               hard to verify, because we must prove that it is true for all values that the
               attacker can compute. We leave that for the future. *)
            display_warning ();
            is_axiom
          end
        else
          begin
            match_state final_state [] evl;
            true
          end
      with AxiomNotVerified ->
        false

let check_axioms final_state axioms =
  (* First check restrictions *)
  let restrictions_ok = List.for_all (fun (rq,is_axiom) ->
    if not is_axiom then check_one_axiom final_state is_axiom rq else true
      ) axioms
  in
  (* Check axioms if restrictions are ok.
     By checking axioms only if the restrictions are satisfied,
     we allow the user to specify axioms that are valid only
     on the traces that satisfy the restrictions. *)
  if restrictions_ok then
    List.iter (fun (rq,is_axiom) ->
      if is_axiom then
        if not (check_one_axiom final_state is_axiom rq) then
          Parsing_helper.user_error "False axiom."
            ) axioms;
  restrictions_ok

(************************************************
   Verification that lemmas do not contain PGLink
 *************************************************)

let rec no_bound_name_term = function
  | Var { link = PGLink _ } -> false
  | Var { link = TLink t } -> no_bound_name_term t
  | Var _ -> true
  | FunApp(_,args) -> List.for_all no_bound_name_term args

let no_bound_name_term_option = function
  | None -> true
  | Some t -> no_bound_name_term t

let no_bound_name_term_e_option = function
  | None -> true
  | Some (t,_) -> no_bound_name_term t

let no_bound_name_event = function
  | QSEvent(_,_,occ,at,t) -> no_bound_name_term_option occ && no_bound_name_term_e_option at && no_bound_name_term t
  | QIsNat t -> no_bound_name_term t
  | QFact(_,_,args,at) -> List.for_all no_bound_name_term args && no_bound_name_term_e_option at
  | QNeq((t1,_),(t2,_))
  | QEq((t1,_),(t2,_))
  | QGeq((t1,_),(t2,_))
  | QSEvent2(t1,t2) -> no_bound_name_term t1 && no_bound_name_term t2
  | QGr _ -> Parsing_helper.internal_error "[lemma.ml >> no_bound_name_event] Lemma should not contain strict disequalities."

let rec no_bound_name_conclusion_query = function
  | QTrue
  | QFalse -> true
  | QConstraints q -> Terms.forall_constraints no_bound_name_term q
  | QEvent ev -> no_bound_name_event ev
  | NestedQuery r -> no_bound_name_realquery r
  | QAnd(concl1,concl2)
  | QOr(concl1,concl2) -> no_bound_name_conclusion_query concl1 && no_bound_name_conclusion_query concl2

and no_bound_name_realquery = function
  | Before(evl,concl) ->
      List.for_all no_bound_name_event evl &&
      no_bound_name_conclusion_query concl

let no_bound_name_query = function
  | RealQuery(q,_),_ -> no_bound_name_realquery q
  | _ -> Parsing_helper.internal_error "[lemma.ml >> no_bound_name_query] Unexpected query."

let no_bound_name_t_lemmas = function
  | LemmaToTranslate _ -> Parsing_helper.internal_error "[lemma.ml >> no_bound_name_t_lemmas] Lemma should be translated at that point."
  | Lemma lem_st -> List.for_all (fun lem -> no_bound_name_query lem.ql_query) lem_st.lemmas
