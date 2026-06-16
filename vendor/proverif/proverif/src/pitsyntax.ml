open Parsing_helper
open Ptree
open Pitptree
open Types
open Pitypes
open Stringmap


let no_param_option = function
  | (s,ext), None -> (s,ext)
  | (s,ext), _ -> input_error "This option should not have any parameter." ext

let check_no_param_option ((s,ext),arg) =
  if arg != None
  then input_error ("The option "^ s ^" should not have any parameter.") ext

let get_param_option ((s,ext),arg) = match arg with
  | None -> input_error ("The option "^ s ^" expects a parameter.") ext
  | Some i -> i

let no_param_option_list = List.map no_param_option

(* We put the next functions

   get_need_vars_in_names
   transl_query
   get_not
   get_nounif

   first in this module, because they must not
   use the state of the parsing function. They appear in the state
   returned by the parsing function and are called afterwards. *)

(* Functions to access the environment *)

let special_functions = ["choice"; "||"; "&&"; "="; "<>"; "<"; ">"; "<="; ">="]

let args_to_string tl =
  let l = List.length tl in
  if l=0 then
    "0 argument"
  else if l=1 then
    "1 argument of type " ^ (Terms.tl_to_string ", " tl)
  else
    (string_of_int l) ^ " arguments of types " ^ (Terms.tl_to_string ", " tl)

let get_apply_symb env (s,ext) tl =
  match s, tl with
    "=", [t1;t2] ->
      if t1 != t2 then
        input_error ("function " ^ s ^ " expects two arguments of same type but is here given " ^
          (args_to_string tl)) ext;
      (EFun (Terms.equal_fun t1), Param.bool_type)
  | "<>", [t1;t2] ->
      if t1 != t2 then
        input_error ("function " ^ s ^ " expects two arguments of same type but is here given " ^
          (args_to_string tl)) ext;
      (EFun (Terms.diff_fun t1), Param.bool_type)
  | "choice", [t1;t2] ->
      if t1 != t2 then
        input_error ("function " ^ s ^ " expects two arguments of same type but is here given " ^
          (args_to_string tl)) ext;
      (EFun (Param.choice_fun t1), t1)
  | ("=" | "<>" | "choice"), _ ->
      input_error (s ^ "expects two arguments") ext
  | str,[t] when str.[0] = '-' ->
      if (t != Param.nat_type)
      then input_error ("function minus expects 1 argument of type nat but is here given " ^ (args_to_string tl)) ext;

      let n = int_of_string (String.sub str 2 ((String.length str) - 2)) in
      (EFun (Terms.minus_fun n), Param.nat_type)
  | _ ->
  try
    match StringMap.find s env with
    | (EFun r) as x ->
        if not (Terms.eq_lists (fst r.f_type) tl) then
          input_error ("function " ^ s ^ " expects " ^
                       (args_to_string (fst r.f_type)) ^
                       " but is here given " ^
                       (args_to_string tl)) ext;
        (x, snd r.f_type)
    | (EPred r) as x ->
        if not ((List.length r.p_type == List.length tl) &&
                (List.for_all2 (fun t1 t2 -> t1 == t2 || t1 == Param.any_type) r.p_type tl)) then
          input_error ("predicate " ^ s ^ " expects " ^
                       (args_to_string r.p_type) ^
                       " but is here given " ^
                       (args_to_string tl)) ext;
        if List.exists (fun t -> t == Param.any_type) r.p_type then
          (EPred (Param.get_pred (UserPred(Polym(r.p_name, r.p_prop, tl)))), Param.bool_type)
        else
          (x, Param.bool_type)
    | (ELetFun (func_proc_layer, arg_type_list, result_type)) as x ->
        if not (Terms.eq_lists tl arg_type_list) then
          input_error ("letfun function " ^ s ^ " expects " ^
                       (args_to_string arg_type_list) ^
                       " but is here given " ^
                       (args_to_string tl)) ext;
        (x, result_type)
    | x -> (x, Param.any_type) (* This case will cause an error in the caller of get_apply_symb *)
  with Not_found ->
    input_error (s ^ " not defined") ext

(* The difference with the previous get_fun is that =, <>, &&, ||, choice are allowed
   get_fun returns the function symbol and the type of the result.
   (The type of the result is often (snd r.f_type), but
   this is not true for choice when we ignore types: in that case,
   (snd r.f_type) is Param.any_type, while the real return type is the
   type of the argument of choice.) *)
let get_fun env (s,ext) tl =
  match get_apply_symb env (s,ext) tl with
    (EFun r, result_type) -> (r, result_type)
  | _ -> input_error (s ^ " should be a function") ext

(* The only difference with the previous get_pred is in error messages:
   when using =, <>, choice, you get "should be a predicate" rather than "not defined". *)
let get_pred env (c, ext) tl =
  match get_apply_symb env (c,ext) tl with
    (EPred r, result_type) -> r
  | _ -> input_error (c ^ " should be a predicate") ext

let get_event_fun env (s,ext) tl =
  try
    let r = StringMap.find s env in
    match r with
      EEvent p ->
        if not (Terms.eq_lists (fst p.f_type) tl) then
          input_error ("function " ^ s ^ " expects " ^
                       (args_to_string (fst p.f_type)) ^
                       " but is here given " ^
                       (args_to_string tl)) ext;
        p
    | _ -> input_error (s ^ " should be an event") ext
  with Not_found ->
    input_error ("event " ^ s ^ " not defined") ext

let get_table_fun env (s,ext) tl =
  try
    let r = StringMap.find s env in
    match r with
      ETable p ->
        if not (Terms.eq_lists (fst p.f_type) tl) then
          input_error ("table " ^ s ^ " expects " ^
                       (args_to_string (fst p.f_type)) ^
                       " but is here given " ^
                       (args_to_string tl)) ext;
        p
    | _ -> input_error (s ^ " should be a table") ext
  with Not_found ->
    input_error ("table " ^ s ^ " not defined") ext

let get_type_polym env polym sid_allowed ?(time_allowed=false) (s, ext) =
  if s = "any_type" then
    if polym then
      Param.any_type
    else
      input_error "polymorphic type not allowed here" ext
  else if s = "sid" then
    if sid_allowed then
      Param.sid_type
    else
      input_error "sid type not allowed here" ext
  else if s = "time" then
    if time_allowed then
      Param.time_type
    else
      input_error "time type not allowed here" ext
  else
    try
      if s = "nat"
      then Param.has_integer := true;

      match StringMap.find s env with
        EType t -> t
      | _ -> input_error (s ^ " should be a type") ext
    with Not_found ->
      input_error ("type " ^ s ^ " not declared") ext

let add_env ?(time_allowed=false) sid_allowed env l =
  let env_ref = ref env in
  List.iter (fun ((s,ext),ty) ->
      let t = get_type_polym env false sid_allowed ~time_allowed:time_allowed ty in
      begin
        try
          match StringMap.find s (!env_ref) with
            EVar _ -> input_error ("variable " ^ s ^ " already defined") ext
          | _ -> input_warning ("identifier " ^ s ^ " rebound") ext
        with Not_found -> ()
      end;
      let v = Terms.new_var s t in
      env_ref := StringMap.add s (EVar v) (!env_ref)
    ) l;
  !env_ref

(* State for the functions get_need_vars_in_names, transl_query, transl_lemma, get_not,
   and get_nounif. *)

type t_q_state =
    { q_env : envElement StringMap.t;
      q_glob_table : (string, funsymb) Hashtbl.t;
      q_glob_table_var_name : (string, term) Hashtbl.t;
      q_max_phase : int;
      q_name_args_exact : bool;
      q_choice_message : string option; (* Error message displayed when Choice is used and it should not. None when Choice is allowed. *)
      q_is_lemma : Pitptree.lemma_kind option;
      q_is_equivalence_query : bool;
      q_must_encode_names : bool;
      q_in_root_premise: bool;
      q_in_premise: bool
     }

let build_q_state must_encode_names pi_state =
  match pi_state.pi_global_env, pi_state.pi_glob_table, pi_state.pi_glob_table_var_name with
    Set global_env, Set glob_table, Set glob_table_var_name ->
      { q_env = global_env;
        q_glob_table = glob_table;
        q_glob_table_var_name = glob_table_var_name;
        q_max_phase = pi_state.pi_max_used_phase;
        q_name_args_exact = pi_state.pi_name_args_exact;
        q_choice_message = None;
        q_is_lemma = None;
        q_is_equivalence_query = false;
        q_must_encode_names = must_encode_names;
        q_in_root_premise = false;
        q_in_premise = false;
      }
  | _ ->
      Parsing_helper.internal_error "glob_table should be set"

(* [find_name_in_glob_table id] returns the name corresponding to
   identifier [id] in that global environment.
   Raise BadBoundName in case no name corresponds or several
   names correspond. *)

exception BadBoundName of string * Parsing_helper.extent * funsymb list

let find_name_in_glob_table state (s,ext) =
  match Hashtbl.find_all state.q_glob_table s with
  | [n] -> n
  | l -> raise (BadBoundName (s, ext, l))

(* [find_all_var_name_in_glob_table id] returns all names and variables
   corresponding to identifier [id] in that global environment.
   Stop the program in case no name nor variable corresponds. *)

let find_all_var_name_in_glob_table state (s,ext) =
  match Hashtbl.find_all state.q_glob_table_var_name s with
    [] -> input_error (s ^ " should be a bound name or a variable") ext
  | l -> l

(* Compute need_vars_in_names: the list of pairs (restriction, variable name)
   such that the variable "variable name" must occur as argument in the
   pattern that models names created by "restriction", because the
   structure "restriction[... variable name = ... ]" is used in the input
   file. *)

let rec nvn_t state accu (term, ext0) =
  match term with
    PGIdent _ -> accu
  | PGFunApp(_,l,_) | PGPhase(_,l, _,_) | PGTuple l ->
      List.fold_left (nvn_t state) accu l
  | PGName (id,bl) ->
      List.fold_left (fun accu ((s',ext'),t) ->
        (* The replication indices do not need to be added in
           need_vars_in_names, because they are always included as
           arguments of names, whether or not they occur in
           the input file.
           They must not be added to need_vars_in_names, because
           they are not correctly computed by trace reconstruction,
           so adding them would cause bugs in trace reconstruction. *)
        let accu' = nvn_t state accu t in
        if (s' <> "") && (s'.[0] != '!') then
          begin
            let r = find_name_in_glob_table state id in
            (* print_string ("Need " ^ s' ^ " in " ^ r.f_name ^ "\n");  *)
            (r, s',ext') :: accu'
          end
        else
          accu'
            ) accu bl
  | PGLet(_,t,t') -> nvn_t state (nvn_t state accu t') t

let nvn_q state accu (q0, ext) =
  match q0 with
    PRealQuery (q,_) -> nvn_t state accu q
  | PPutBegin _ | PQSecret _ -> accu

let rec nvn_f state accu (f,ext0) =
  match f with
    PFGIdent _ | PFGAny _ -> accu
  | PFGFunApp(_,l) | PFGTuple l ->
      List.fold_left (nvn_f state) accu l
  | PFGName (id,bl) ->
      List.fold_left (fun accu ((s',ext'),t) ->
        (* The replication indices do not need to be added in
           need_vars_in_names, because they are always included as
           arguments of names, whether or not they occur in
           the input file.
           They must not be added to need_vars_in_names, because
           they are not correctly computed by trace reconstruction,
           so adding them would cause bugs in trace reconstruction. *)
        let accu' = nvn_f state accu t in
        if (s' <> "") && (s'.[0] != '!') then
          begin
            let r = find_name_in_glob_table state id in
            (* print_string ("Need " ^ s' ^ " in " ^ r.f_name ^ "\n");  *)
            (r, s',ext') :: accu'
          end
        else
          accu'
            ) accu bl
  | PFGLet(_,t,t') -> nvn_f state (nvn_f state accu t') t

let rec nvn_nounif state accu = function
    BFLet(_,t,nounif) ->  nvn_f state (nvn_nounif state accu nounif) t
  | BFNoUnif(id,fl,n) -> List.fold_left (nvn_f state) accu fl

let get_need_vars_in_names query_list not_list nounif_list pi_state =
  if not pi_state.pi_name_args_exact then
    []
  else
    let q_state = build_q_state false pi_state in
    let accu1 = List.fold_left (fun accu (_, q) -> List.fold_left (nvn_q q_state) accu q) [] query_list in
    let accu2 = List.fold_left (fun accu (_, no) -> nvn_t q_state accu no) accu1 not_list in
    List.fold_left (fun accu (_, nounif,_,_) -> nvn_nounif q_state accu nounif) accu2 nounif_list

(* queries *)

let non_compromised_session = FunApp(Param.session1, [])

(* The exception [MissingNameArg(s,s',ext)] is raised when
   the variable [s'] at position [ext] is not defined at restriction [s],
   and it is needed in a query, not, or nounif declaration *)
exception MissingNameArg of string * string * Parsing_helper.extent

let bad_bound_name_exc_to_msg = function
  | BadBoundName (s, ext, []) -> (s ^ " should be a bound name"), "", ext
  | BadBoundName (s, ext, _) ->
      (s ^ " cannot be used in queries, not, or nounif. Its definition is ambiguous"),
      (" (For example, several restrictions might define " ^ s ^ ".)"),
      ext
  | MissingNameArg(s, s', ext) ->
      ("variable " ^ s' ^ " not defined at restriction " ^ s), "", ext
  | _ -> "unknown error", "", Parsing_helper.dummy_ext

let handle_bad_bound_names_error e =
  let message, message_compl, ext = bad_bound_name_exc_to_msg e in
  input_error (message ^ "." ^ message_compl) ext

let handle_bad_bound_names state action e =
  let message, message_compl, ext = bad_bound_name_exc_to_msg e in
  if state.q_name_args_exact then
    input_error (message ^ "." ^ message_compl) ext
  else
    begin
      input_warning (message ^ " after process transformation." ^ message_compl ^ " " ^ action) ext;
      None
    end

(** Transformation between term and enriched_term *)


let rec term_of_enriched_term et = match et.et_desc with
  | ET_Var { link = TLink t; _ } -> t (* follows links introduced by pattern_of_enriched_pattern, case EP_PatVar *)
  | ET_Var v -> Var v
  | ET_FunApp(f,args) -> FunApp(f,List.map term_of_enriched_term args)
  | ET_Test(econd,ethen,eelse) ->
      let cond = term_of_enriched_term econd in
      if Terms.equal_terms cond Terms.true_term
      then term_of_enriched_term ethen
      else if Terms.equal_terms cond Terms.false_term 
      then term_of_enriched_term eelse
      else 
        let tthen = term_of_enriched_term ethen in
        let telse = term_of_enriched_term eelse in
        let gtest_symb = Terms.gtest_fun ethen.et_type in
        FunApp(gtest_symb, [cond; tthen; telse])
  | ET_Let(epat,eexp,ethen,eelse) ->
      let exp = term_of_enriched_term eexp in
      let telse = term_of_enriched_term eelse in

      pattern_of_enriched_pattern (fun cond_pat ->
        (* The term [cond_pat] is guaranteed to not fail by construction *)
        let tthen = term_of_enriched_term ethen in
        if Terms.equal_terms cond_pat Terms.true_term
        then tthen
        else if Terms.equal_terms cond_pat Terms.false_term 
        then telse 
        else
          let gtest_symb = Terms.gtest_fun ethen.et_type in
          FunApp(gtest_symb, [cond_pat; tthen; telse])
      ) exp epat 
  | _ -> Parsing_helper.internal_error "This function should only be applied on simple enriched term without Restr."

and pattern_of_enriched_pattern f_next exp epat = match epat.ep_desc with
  | EP_PatVar v -> 
      Terms.auto_cleanup (fun () ->
        Terms.link v (TLink exp);
        f_next Terms.true_term
      )
  | EP_PatTuple(f,pargs) ->
      let proj_funs = Terms.get_all_projection_fun f in
      let exp_args = List.map (fun fp -> FunApp(fp,[exp])) proj_funs in

      let first_arg = List.hd exp_args in
      let success_f = Terms.success_fun (Terms.get_term_type first_arg) in
      let cond_pat = FunApp(success_f,[first_arg]) in

      pattern_of_enriched_pattern_list (fun cond_pat_args ->
        let cond_pat' = Terms.make_and cond_pat cond_pat_args in
        f_next cond_pat' 
      ) exp_args pargs

  | EP_PatEqual et ->
      let t = term_of_enriched_term et in
      let cond_pat = FunApp(Terms.equal_no_fail_fun et.et_type,[t;exp]) in
      f_next cond_pat

and pattern_of_enriched_pattern_list f_next exp_l e_patl = match exp_l,e_patl with
  | [],[] -> f_next Terms.true_term
  | [],_ | _,[] -> Parsing_helper.internal_error "The expression and pattern lists should be of same size."
  | exp::eq, pat::pq ->
      pattern_of_enriched_pattern (fun cond_pat ->
        pattern_of_enriched_pattern_list (fun cond_pq ->
          let cond_pat' = Terms.make_and cond_pat cond_pq in
          f_next cond_pat'
        ) eq pq
      ) exp pat

let rec enriched_term_of_term = function
  | Var v -> { et_desc = ET_Var v; et_simple = true; et_simple_no_let = true; et_simple_no_restr = true; et_type = v.btype; et_ext = Parsing_helper.dummy_ext }
  | FunApp(f,args) -> 
      let eargs = List.map enriched_term_of_term args in
      { et_desc = ET_FunApp(f,eargs); et_simple = true; et_simple_no_let = true; et_simple_no_restr = true; et_type = snd f.f_type; et_ext = Parsing_helper.dummy_ext }

(* Note: when check_query, get_queries are applied before the
   translation of the process into Horn clauses has been done,
   the arity of names may not be correctly initialized. In this case,
   update_type_names should be called after the translation of the
   process to update it.  *)

let get_ident_any state (s, ext) =
   try
     match StringMap.find s state.q_env with
         EVar b ->
           begin
             match b.link with
               TLink t -> t, b.btype
             | NoLink -> Var b, b.btype
             | _ -> internal_error "unexpected link in get_ident_any"
           end
       | EName r ->
           FunApp(r, []), snd r.f_type
       | EFun f ->
           begin
             match f.f_cat with
               Eq _ | Tuple -> ()
             | _ ->  input_error ("function " ^ s ^ " is defined by \"reduc\". Such a function should not be used in a query") ext
           end;
           if fst f.f_type == [] then
             FunApp(f,[]), snd f.f_type
           else
             input_error ("function " ^ s ^ " has expects " ^
                          (string_of_int (List.length (fst f.f_type))) ^
                          " arguments but is used without arguments") ext
       | _ -> input_error ("identifier " ^ s ^ " should be a variable, a free name, or a function") ext
   with Not_found ->
     input_error ("identifier " ^ s ^ " not defined") ext
     
let rec check_query_term state (term, ext0) = match term with
  | PGIdent i -> get_ident_any state i
  | PGPhase _ -> input_error ("phase unexpected in query terms") ext0
  | PGFunApp((s,ext),l,None) ->
      if List.mem s ["="; "<>"; "<="; ">="; ">"; "<"; "is_nat"; "==>"; "&&"; "||"; "event"; "inj-event"; "table"] then
        input_error (s ^ " unexpected in query terms") ext;
      let (l', tl') = List.split (List.map (check_query_term state) l) in
      begin match get_apply_symb state.q_env (s,ext) tl' with
      | (EFun f, result_type) -> 
          begin 
            begin match f.f_cat with
            | Eq _ | Tuple -> ()
            
            (* destructors not allowed in premises of queries *)
            | Red _ ->
		if state.q_in_premise then
		  input_error ("function " ^ s ^ " is defined by \"reduc\". Such a function cannot be used in the premise.") ext
            
            (* choice not allowed in some contexts, which directly submit their error messages *)
            | Choice ->
                begin
                  match state.q_choice_message with
                  | None -> ()
                  | Some err_message -> input_error err_message ext
                end
            | _ ->  input_error ("This function cannot be used at this point.") ext
            end;
            (Terms.app f l', result_type)
          end
      | ELetFun (encode_eterm,_,_), result_type ->
          if state.q_in_premise
          then input_error ("You cannot use a letfun in the premise of the query.") ext;
          let el' = List.map enriched_term_of_term l' in
          let result_eterm = encode_eterm el' in
          if not result_eterm.et_simple_no_restr
          then input_error ("To be used in a query, the declaration of the function "^s^" should only contain term, test and let constructs.") ext;
	  let t = term_of_enriched_term result_eterm in
          (* choice not allowed in some contexts, which directly submit their error messages
             We must check it here in case the letfun contains choice *)
	  if Terms.has_choice t then
	    begin
              match state.q_choice_message with
              | None -> ()
              | Some err_message -> input_error err_message ext
            end;
          (t,result_type)
      | _ -> input_error (s ^ " should be a function") ext
      end
  | PGFunApp(_,_,Some (s,ext)) -> input_error ("Unexpected temporal identifier "^s^" in query terms.") ext
  | PGTuple l ->
      let (l', tl') = List.split (List.map (check_query_term state) l) in
      if List.exists (fun ty -> Param.time_type == ty) tl'
      then input_error "terms of time type are not authorised as arguments of a tuple." ext0;
      (FunApp(Terms.get_tuple_fun tl', l'), Param.bitstring_type)
  | PGName ((s,ext) as id,bl) ->
      let r = find_name_in_glob_table state id in
      if fst r.f_type == Param.tmp_type then
        begin
          if state.q_must_encode_names then
            Parsing_helper.input_error ("You are referring to name " ^ s ^ " in this query or secrecy assumption, but this name will never be generated") ext
          else
            let v = Terms.new_var_def (snd r.f_type) in
            v.link <- PGLink (fun () ->
              try
                fst (check_query_term { state with q_must_encode_names = true } (term,ext0))
              with
              | (MissingNameArg _ | BadBoundName _) as e ->
                  handle_bad_bound_names_error e
                    );
            (Var v, snd r.f_type)
        end
      else
        begin
          match r.f_cat with
            | Name { prev_inputs_meaning = sl } ->
                List.iter (fun ((s',ext'),_) ->
                      if not (List.exists (fun m -> Reduction_helper.meaning_encode m = s') sl) then
                  raise (MissingNameArg(s,s',ext))
                        (*input_error ("variable " ^ s' ^ " not defined at restriction " ^ s) ext'*)
                ) bl;
                let p =
                  List.map2 (fun m ty ->
                    match m with
                      | MCompSid -> non_compromised_session
                      | _ -> binding_find state (Reduction_helper.meaning_encode m) ty bl
                  ) sl (fst r.f_type)
                in
                (FunApp(r, p), snd r.f_type)
          | _ -> internal_error "name expected here"
        end
  | PGLet(id,t,t') -> check_query_term (add_binding state (id,t)) t'

and binding_find state s ty = function
    [] -> Terms.new_var_def_term ty
  | ((s',ext),t)::l ->
      if s' = s then
        begin
          let (t', ty') = check_query_term state t in
          if ty' != ty then
            input_error ("this variable is of type " ^ ty.tname ^ " but is given a value of type " ^ ty'.tname) ext;
          if (s <> "") && (s.[0] = '!') then
            begin
              match t' with
                Var _ -> ()
              | _ -> input_error "session identifiers should be variables" ext
            end;
          t'
        end
      else
        binding_find state s ty l

and add_binding state ((i,ext),t) =
  begin
    try
      match StringMap.find i state.q_env with
        EVar _ -> input_error ("variable " ^ i ^ " already defined") ext
      | _ -> ()
    with Not_found -> ()
  end;
  let (t', ty') = check_query_term state t in
  if ty' == Param.time_type
  then input_error "time type not authorised in a variable binding." ext;
  let v = Terms.new_var i ty' in
  v.link <- TLink t';
  { state with q_env = StringMap.add i (EVar v) state.q_env }

let check_subterm_pred state e evl =
  if not state.q_in_root_premise
  then input_error "subterm predicate should only occur in the premise of an axiom or a restriction" e;

  let rec check_choice = function
    | FunApp({ f_cat = Choice; _ },_) -> input_error "subterm predicate should not contain choice" e
    | FunApp(_,args) -> List.iter check_choice args
    | _ -> ()
  in

  match evl with
  | [t1;t2] ->
      let (t1', ty1) = check_query_term state t1 in
      let (t2', ty2) = check_query_term state t2 in
      check_choice t1';
      check_choice t2';
      let subterm_pred = Param.get_pred (Subterm(ty1,ty2)) in
      QFact(subterm_pred,[],[t1';t2'],None)
  | _ -> input_error "arity of predicate subterm should be 2" e

let check_time state = function
  | None -> None
  | Some ((_,ext) as i) ->
      let (t,ty) = get_ident_any state i in
      if ty != Param.time_type
      then input_error "temporal variables should have type time." ext;
      if state.q_is_lemma <> None
      then input_error "Declared axioms and lemmas cannot contain variables of type time." ext;
      Some (t,ext)

let check_mess state e tl at_op n =
  match tl with
    [t1;t2] ->
      let (t1', ty1) = check_query_term state t1 in
      let (t2', ty2) = check_query_term state t2 in
      if ty1 != Param.channel_type then
        input_error ("First argument of mess is of type " ^ ty1.tname ^ " and should be of type channel") e;
      let mess_n = Param.get_pred (Mess((if n = -1 then state.q_max_phase else n),
                                        ty2))
      in
      let at_op' = check_time state at_op in
      QFact(mess_n, [],[t1';t2'],at_op')
  | _ ->
      input_error "arity of predicate mess should be 2" e

let check_attacker state e tl at_op n =
  match tl with
    [t1] ->
      let (t1', ty1) = check_query_term state t1 in
      let att_n = Param.get_pred (Attacker((if n = -1 then state.q_max_phase else n),
                                           ty1))
      in
      let at_op' = check_time state at_op in
      QFact(att_n,[],[t1'],at_op')
  | _ ->
      input_error "arity of predicate attacker should be 1" e

let rec check_table_term state (term, ext0) =
  match term with
  | PGFunApp((s,ext),l,None) ->
      (* FunApp: only tables allowed *)
      if List.mem s ["="; "<>"; "==>"; "&&"; "||"; "event"; "inj-event"; "table"] then
        input_error (s ^ " unexpected in query terms") ext;
      let (l', tl') = List.split (List.map (check_query_term state) l) in
      let f = get_table_fun state.q_env (s,ext) tl' in
      FunApp(f, l')
  | PGFunApp(_,_,Some (s,ext)) -> input_error ("Unexpected temporal identifier "^s^" in query terms.") ext
  | _ -> input_error "Table term expected" ext0

let check_table state e tl at_op n =
  match tl with
    [t1] ->
      let t1' = check_table_term state t1 in
      let table_n = Param.get_pred (Table(if n = -1 then state.q_max_phase else n)) in
      let at_op' = check_time state at_op in
      QFact(table_n,[],[t1'],at_op')
  | _ ->
      input_error "arity of predicate table should be 1" e

let check_inequality_type state ty1 ty2 e =
  if ty1 != ty2
  then input_error "the two arguments of an inequality test should have the same type" e;
  if state.q_is_lemma <> None && ty1 == Param.time_type
  then input_error "Declared axioms and lemmas cannot contain variables of type time" e;
  if ty1 != Param.nat_type && ty1 != Param.time_type
  then input_error "the two arguments of an inequality test should have the type nat or the type time." e

let check_query_term_e state t =
  let (t', ty) = check_query_term state t in ((t', snd t), ty)

let rec check_event state (f,e) = match f with
    (* FunApp: predicates, =, <>, event, inj-event, attacker, mess, table allowed *)
  | PGFunApp(("<>", _), [t1; t2],None) ->
      let state' = { state with q_choice_message = Some "Disequalities in queries, lemmas, and axioms should not contain choice." } in
      let (t1', ty1) = check_query_term_e state' t1 in
      let (t2', ty2) = check_query_term_e state' t2 in
      if ty1 != ty2 then
        input_error "the two arguments of a disequality test should have the same type" e;
      QNeq(t1', t2')
  | PGFunApp(("=", _), [t1; t2],None) ->
      let state' = { state with q_choice_message = Some "Equalities in queries, lemmas, and axioms should not contain choice." } in
      let (t1', ty1) = check_query_term_e state' t1 in
      let (t2', ty2) = check_query_term_e state' t2 in
      if ty1 != ty2 then
        input_error "the two arguments of an equality test should have the same type" e;
      QEq(t1', t2')
  | PGFunApp((">=",_), [t1;t2],None) ->
      let state' = { state with q_choice_message = Some "Inequalities in queries, lemmas, and axioms should not contain choice." } in
      let (t1', ty1) = check_query_term_e state' t1 in
      let (t2', ty2) = check_query_term_e state' t2 in
      check_inequality_type state ty1 ty2 e;
      QGeq(t1', t2')
  | PGFunApp((">",_), [t1;t2],None) ->
      let state' = { state with q_choice_message = Some "Inequalities in queries, lemmas, and axioms should not contain choice." } in
      let (t1', ty1) = check_query_term_e state' t1 in
      let ((t2'', ext2) as t2', ty2) = check_query_term_e state' t2 in
      check_inequality_type state ty1 ty2 e;
      if ty1 == Param.nat_type
      then QGeq(t1', (Terms.sum_nat_term t2'' 1, ext2))
      else QGr(t1',t2')
  | PGFunApp(("<=",_), [t1;t2],None) ->
      let state' = { state with q_choice_message = Some "Inequalities in queries, lemmas, and axioms should not contain choice." } in
      let (t1', ty1) = check_query_term_e state' t1 in
      let (t2', ty2) = check_query_term_e state' t2 in
      check_inequality_type state ty1 ty2 e;
      QGeq(t2', t1')
  | PGFunApp(("<",_), [t1;t2],None) ->
      let state' = { state with q_choice_message = Some "Inequalities in queries, lemmas, and axioms should not contain choice." } in
      let ((t1'', ext1) as t1', ty1) = check_query_term_e state' t1 in
      let (t2', ty2) = check_query_term_e state' t2 in
      check_inequality_type state ty1 ty2 e;
      if ty1 == Param.nat_type
      then QGeq(t2', (Terms.sum_nat_term t1'' 1, ext1))
      else QGr(t2',t1')
  | PGFunApp(("is_nat",_), [t],None) ->
      let state' = { state with q_choice_message = Some "Predicates is_nat in queries, lemmas, and axioms should not contain choice." } in
      let (t', ty) = check_query_term state' t in
      if ty != Param.nat_type then
        input_error "the argument of the predicate is_nat should have the type nat." e;
      QIsNat(t')
  | PGFunApp(("event",e'),tl0,at_op) ->
      let (f,tl) = match tl0 with
        | [PGFunApp(f, tl,None),_] -> (f,tl)
        | [PGIdent f,_] -> (f,[])
        | _ -> input_error "predicate event should have one argument, which is a function application" e'
      in
      let at_op' = check_time state at_op in
      let (tl', tyl') = List.split (List.map (check_query_term state) tl) in
      if !Param.key_compromise == 0 then
        QSEvent(None,[],None,at_op',FunApp((get_event_fun state.q_env f tyl'), tl'))
      else
        QSEvent(None,[],None,at_op',FunApp((get_event_fun state.q_env f (Param.sid_type :: tyl')),(Terms.new_var_def_term Param.sid_type)::tl'))
  | PGFunApp(("inj-event",e'),tl0,at_op) ->
      let (f,tl) = match tl0 with
        | [PGFunApp(f, tl,None),_] -> (f,tl)
        | [PGIdent f,_] -> (f,[])
        | _ -> input_error "predicate inj-event should have one argument, which is a function application" e'
      in
      let at_op' = check_time state at_op in
      let (tl', tyl') = List.split (List.map (check_query_term state) tl) in
      if !Param.key_compromise == 0 then
        QSEvent(Some (Param.fresh_injective_index ()),[],None,at_op',FunApp((get_event_fun state.q_env f tyl'), tl'))
      else
        QSEvent(Some (Param.fresh_injective_index ()),[],None,at_op',FunApp((get_event_fun state.q_env f (Param.sid_type :: tyl')), (Terms.new_var_def_term Param.sid_type)::tl'))
  | PGFunApp(("subterm",_), tl, None) -> check_subterm_pred state e tl
  | PGFunApp(("attacker",_), tl,at_op) ->
      check_attacker state e tl at_op (-1)
  | PGFunApp(("mess",_), tl,at_op) ->
      check_mess state e tl at_op (-1)
  | PGFunApp(("table",_), tl,at_op) ->
      check_table state e tl at_op (-1)
  | PGFunApp((s, ext) as p, tl,None) ->
      if List.mem s ["||"; "&&"; "not"; "==>"; ">"; "<"; ">="; "<="; "is_nat"] then
        input_error (s ^ " unexpected in events") ext;
      let (tl', tyl) = List.split (List.map (check_query_term state) tl) in
      QFact(get_pred state.q_env p tyl,[],tl',None)
  | PGPhase((s, ext), tl, n,at_op) ->
      begin
        match s with
          | "mess" -> check_mess state e tl at_op n
          | "attacker" -> check_attacker state e tl at_op n
          | "table" -> check_table state e tl at_op n
          | _ -> input_error "phases can be used only with attacker, mess, or table" ext
      end
  | PGIdent p ->
      QFact(get_pred state.q_env p [],[],[],None)
  | PGLet(id,t,t') -> check_event (add_binding state (id,t)) t'
  | PGFunApp(_,_,Some (at_id,ext)) -> input_error "only the predicates event, inj-event, attacker, mess and table can have a temporal identifier." ext
  | _ -> input_error "an event should be a predicate application" e

(* The list of events corresponds to the premise of the query *)
let rec check_ev_list state = function
  | PGFunApp(("&&", _), [e1;e2], _), _ ->
      (check_ev_list state e1) @ (check_ev_list state e2)
  | ev ->
      let ev' = check_event state ev in
      let ev'' =
        match ev' with
        | QEq _ -> Parsing_helper.input_error "Equality test should not occur in premise of queries, lemmas, restrictions, or axioms." (snd ev)
        | QNeq ((t1,_),(t2,_)) | QGeq ((t1,_),(t2,_)) | QGr ((t1,_),(t2,_))
          when Terms.get_term_type t1 = Param.time_type || Terms.get_term_type t2 = Param.time_type ->
            Parsing_helper.input_error "Disequalities and inequalities on time variables should not occur in the premise." (snd ev)
	| QGr _ -> Parsing_helper.internal_error "QGr should be used only with time variables"
        | QIsNat _ | QNeq _ | QGeq _ -> ev'
        | QFact(p,_,_,_) ->
            begin match state.q_is_lemma with
              | Some KLemma ->
                  begin match p.p_info with
                    | Attacker _ | Mess _ | Table _ | UserPred _  -> ()
                    | _ -> Parsing_helper.input_error "Declared lemmas should only contain attacker predicates, message predicates, table predicates, events or user defined predicates in their premises." (snd ev)
                  end
              | Some (KAxiom | KRestriction) ->
                  begin match p.p_info with
                    | Attacker _ | Mess _ | Table _ | UserPred _ | Subterm _ -> ()
                    | _ -> Parsing_helper.input_error "Declared restrictions and axioms should only contain attacker predicates, message predicates, table predicates, subterm predicates, events or user defined predicates in their premises." (snd ev)
                  end
              | None ->
                  begin match p.p_info with
                    | Subterm _ -> Parsing_helper.input_error "Subterm predicates can only be used in the premise of an axiom or a restriction." (snd ev)
                    | _ -> ()
                  end
            end;
            ev'
        | QSEvent(Some _,_,_, _,_) when state.q_is_lemma <> None ->
            input_error "Declared lemmas, axioms, and restrictions should not contain injective events in their premise." (snd ev)
        | QSEvent _ when !Param.key_compromise == 0 -> ev'
        | QSEvent(inj, ord_fun,None,at_op,FunApp(f, sid::l)) -> QSEvent(inj, ord_fun,None,at_op,FunApp(f, non_compromised_session::l))
        | QSEvent _
        | QSEvent2 _ ->
            internal_error "Bad format for events in queries"
      in
      [ev'']

let rec check_hyp state = function
    (* FunApp: ==>, ||, && allowed, or what is allowed in events *)
    PGFunApp(("==>", _), [ev; hypll],_), ext ->
      if state.q_is_lemma <> None then
        Parsing_helper.input_error "Declared lemmas, axioms, and restrictions should not contain nested queries." ext;
      let state' = { state with q_in_premise = true } in
      let ev' = check_event state' ev in
      begin
        match ev' with
        | QNeq _ | QEq _ | QGeq _ | QGr _ | QIsNat _ | QFact _ ->
            input_error "Inequalities, disequalities, equalities, is_nat, and facts cannot occur before ==> in nested queries" (snd ev)
        | _ -> ()
      end;
      let hypll' = check_hyp state hypll in
      NestedQuery(Before([ev'], hypll'))
  | PGFunApp(("||", _), [he1;he2],_), _ ->
      QOr(check_hyp state he1,check_hyp state he2)
  | PGFunApp(("&&", _), [he1;he2],_), _ ->
      QAnd(check_hyp state he1,check_hyp state he2)
  | PGIdent("false", _), _ -> QFalse
  | PGIdent("true", _), _ -> QTrue
  | PGLet(id,t,t'), _ -> check_hyp (add_binding state (id,t)) t'
  | ev ->
      let ev' = check_event state ev in
      if state.q_is_lemma <> None then
        begin
          match ev' with
          | QSEvent(Some _,_,_,_,_) -> Parsing_helper.input_error "Declared lemmas, axioms, and restrictions should not contain injective events." (snd ev)
          | _ -> ()
        end;
      QEvent(ev')

(* Check that in the premise in a fact subterm(t,t'), all variables in [t'] must occur in another non-subterm fact from the premise *)
let check_variables_in_premise e evl =
  let (must_be_bound_facts,other_facts) =
    List.partition (function
      | QFact({ p_info = Subterm _; _},_,_,_) 
      | QNeq _ | QGeq _ | QIsNat _ -> true
      | _ ->false
    ) evl
  in
  if other_facts = []
  then input_error "The premise of a query, lemma, axiom or restriction cannot contain only subterm, disequality, or inequality facts." e;

  (* Retrieve the variables from facts other than subterm, inequalities, 
     disequalities, is_nat *)
  let other_facts_vars = ref [] in
  List.iter (function
    | QSEvent(_,_,_,_,ev) -> Terms.get_vars other_facts_vars ev
    | QSEvent2(ev1,ev2) ->
        Terms.get_vars other_facts_vars ev1;
        Terms.get_vars other_facts_vars ev2
    | QFact(_,_,args,_) -> List.iter (Terms.get_vars other_facts_vars) args
    | _ -> internal_error "[pitsyntax.ml >> check_variables_in_subterm_predicates] Expecting a list of predicate corresponding to the premise of a query."
  )  other_facts;

  (* Check the variables of subterm, inequalities, disequalities, is_nat 
     facts *)
  List.iter (function
    | QFact(_,_,[_;t],_) ->
        if not (Terms.occurs_vars_all !other_facts_vars t)
        then input_error "If a fact subterm(t,t') occurs in the premise of an axiom or a restriction then all variables in t' should also occur in another fact (different from a subterm, inequality, disequality fact) in the premise." e
    | QNeq ((t1,_),(t2,_)) | QGeq ((t1,_),(t2,_)) ->
        if not (Terms.occurs_vars_all !other_facts_vars t1) || not (Terms.occurs_vars_all !other_facts_vars t2)
        then input_error "If an inequality or disequality occurs in the premise of an axiom, a restriction, a lemma, or a query then all variables in it should also occur in another fact (different from a subterm, inequality, disequality fact) in the premise." e
    | QIsNat t ->
        if not (Terms.occurs_vars_all !other_facts_vars t)
        then input_error "If a predicate is_nat(t) occurs in the premise of an axiom, a restriction, a lemma, or a query then all variables in t should also occur in another fact (different from a subterm, inequality, disequality fact) in the premise." e
    | _ -> internal_error "[pitsyntax.ml >> check_variables_in_subterm_predicates] Expecting a subterm fact."
  ) must_be_bound_facts

let rec check_real_query_top state = function
    PGFunApp(("==>", _), [evl; hypll],_), e ->
      (* FunApp: ==> allowed, or what is allowed in events (case below) *)
      let state' = { state with q_in_root_premise = true; q_in_premise = true } in
      let evl' = check_ev_list state' evl in
      check_variables_in_premise e evl';
      let hypll' = check_hyp state hypll in
      Before(evl', hypll')
  | PGLet(id,t,t'), _ -> check_real_query_top (add_binding state (id,t)) t'
  | (_,e) as evl ->
      let state' = { state with q_in_root_premise = true; q_in_premise = true } in
      let evl' = check_ev_list state' evl in
      check_variables_in_premise e evl';
      Before(evl', QFalse)

let check_query state = function
  | PRealQuery (q, pub_vars) ->
      let q' = check_real_query_top state q in
      let pub_vars' = List.concat (List.map (find_all_var_name_in_glob_table state) pub_vars) in
      RealQuery(q', pub_vars')
  | PQSecret(v, pub_vars, opt) ->
      if state.q_is_lemma <> None then
        input_error "Lemmas, axioms and restrictions should be correspondence queries." (snd v);
      let v' = find_all_var_name_in_glob_table state v in
      let pub_vars' = List.concat (List.map (find_all_var_name_in_glob_table state) pub_vars) in
      let opt' = ref Reachability in
      List.iter (fun (s,ext) ->
        if s = "reachability" || s = "pv_reachability" then
          opt' := Reachability
        else if s = "real_or_random" || s = "pv_real_or_random" then
          opt' := RealOrRandom
        else if StringPlus.starts_with s "cv_" then
          ()
        else
          input_error "The allowed options for query secret are reachability, pv_reachability, real_or_random, pv_real_or_random, and for compatibility with CryptoVerif, all options starting with cv_" ext
      ) (no_param_option_list opt);
      QSecret(v',pub_vars', !opt')
  | PPutBegin(i, l) ->
      if state.q_is_lemma <> None then
        begin
          match l with
          | (_,ext)::_ -> input_error "Lemmas, axioms and restrictions should be correspondence queries." ext;
          | [] -> internal_error "put_begin with empty list"
        end;
      let l' =
        List.map (fun (s,e) ->
                try
                  match StringMap.find s state.q_env with
                    EEvent r -> r
                  | _ -> input_error (s ^ " should be an event") e
                with Not_found ->
                  input_error ("unknown event " ^s) e
        ) l
      in
      PutBegin(i,l')

let put_user_defined_end_of_premise = function
  | Before(evl,qconcl) ->
      let rec explore accu accu_p = function
        | [] -> (List.rev accu) @ (List.rev accu_p)
        | (QFact(p,_,_,_) as goal) :: q when Terms.is_user_defined p -> explore accu (goal::accu_p) q
        | goal :: q -> explore (goal::accu) accu_p q
      in
      let evl' = explore [] [] evl in
      Before(evl',qconcl)

let check_lemma state (q,ror_opt,pub_vars) =
  let state' =
    if not state.q_is_equivalence_query && ror_opt = None
    then { state with q_choice_message = Some "choice can only be used in lemmas when the main query is an equivalence of (bi)processes,\nor if they have been specified for a query secret with the option real_or_random or pv_real_or_random." }
    else state
  in
  let q' = check_real_query_top state' q in
  let q'' = put_user_defined_end_of_premise q' in
  let pub_vars' = List.concat (List.map (find_all_var_name_in_glob_table state') pub_vars) in
  let ror_opt' = match ror_opt with
    | None -> None
    | Some (v,(s,ext)) ->
        if s <> "real_or_random" && s <> "pv_real_or_random"
        then input_error "A lemma can only be specified to a query secret with the option real_or_random or pv_real_or_random." ext;

        let v' = find_all_var_name_in_glob_table state' v in
        Some v'
  in
  ((RealQuery(q'',pub_vars'), snd q), ror_opt')

let rec map_opt f = function
    [] -> []
  | a::l ->
      match f a with
        None -> map_opt f l
      | Some a' -> a' :: (map_opt f l)

let check_query_list state l =
  map_opt (fun (q, ext) ->
    try
      Some (check_query state q, ext)
    with
    | (MissingNameArg _ | BadBoundName _) as e ->
       handle_bad_bound_names state "Cannot test this query." e
    ) l

let check_lemma_list state l =
  List.map (fun q ->
    try
      Some (check_lemma state q)
    with
    | (MissingNameArg _ | BadBoundName _) as e ->
        handle_bad_bound_names state "Cannot test this query." e
  ) l

let transl_option_lemma_query kind_lemma options =
  let sat_app = ref !Param.sat_application in
  let verif_app = ref !Param.verif_application in
  let max_subset = ref (kind_lemma = None) in
  let induction = ref (
    if kind_lemma <> None
    then !Param.induction_lemmas
    else !Param.induction_queries)
  in
  let remove_events = ref RENone in

  let sat_option = ref false in
  let verif_option = ref false in
  let max_subset_option = ref false in
  let induction_option = ref false in
  let keep = ref false in

  let print_kind_lemma = function
    | None -> "A query"
    | Some KAxiom -> "An axiom"
    | Some KLemma -> "A lemma"
    | Some KRestriction -> "A restriction"
  in

  List.iter (fun (str,ext) -> match str with
    | "removeEvents" ->
        if kind_lemma = None
        then input_error "A query cannot have the option removeEvents. Only lemmas, axioms, and restrictions can." ext;
        if !remove_events = REKeep
        then input_error "The option removeEvents cannot be declared at the same time as keepEvents." ext;
        if !remove_events = RERemove
        then input_error "The option removeEvents has already been declared." ext;
        remove_events := RERemove
    | "keepEvents" ->
           if kind_lemma = None
           then input_error "A query cannot have the option keepEvents. Only lemmas, axioms, and restrictions can." ext;
           if !remove_events = RERemove
           then input_error "The option keepEvents cannot be declared at the same time as removeEvents." ext;
           if !remove_events = REKeep
           then input_error "The option keepEvents has already been declared." ext;
           remove_events := REKeep
    | "maxSubset" ->
        if kind_lemma <> Some KLemma
        then input_error ((print_kind_lemma kind_lemma) ^" cannot have the option maxSubset. Only lemmas can.") ext;
        if !max_subset_option
        then input_error "The option maxSubset was already declared." ext;
        max_subset_option := true;
        max_subset := true
    | "proveAll" ->
        if kind_lemma <> None
        then input_error ((print_kind_lemma kind_lemma) ^" cannot have the option proveAll. Only queries can.") ext;
        if !max_subset_option
        then input_error "The option proveAll was already declared." ext;
        max_subset_option := true;
        max_subset := false
    | "noneSat" ->
        if !sat_option
        then input_error "An option for the application of this lemma during the saturation procedure as already been declared." ext;
        sat_app := LANone;
        sat_option := true
    | "noneVerif" ->
        if !verif_option
        then input_error "An option for the application of this lemma during the verification procedure as already been declared." ext;
        verif_app := LANone;
        verif_option := true
    | "discardSat" ->
        if !sat_option
        then input_error "An option for the application of this lemma during the saturation procedure as already been declared." ext;
        sat_app := LAOnlyWhenRemove;
        sat_option := true
    | "discardVerif" ->
        if !verif_option
        then input_error "An option for the application of this lemma during the verification procedure as already been declared." ext;
        verif_app := LAOnlyWhenRemove;
        verif_option := true
    | "fullSat" ->
        if !sat_option
        then input_error "An option for the application of this lemma during the saturation procedure as already been declared." ext;
        sat_app := LAFull;
        sat_option := true
    | "fullVerif" ->
        if !verif_option
        then input_error "An option for the application of this lemma during the verification procedure as already been declared." ext;
        verif_app := LAFull;
        verif_option := true
    | "instantiateSat" ->
        if !sat_option
        then input_error "An option for the application of this lemma during the saturation procedure as already been declared." ext;
        sat_app := LAOnlyWhenInstantiate;
        sat_option := true
    | "instantiateVerif" ->
        if !verif_option
        then input_error "An option for the application of this lemma during the verification procedure as already been declared." ext;
        verif_app := LAOnlyWhenInstantiate;
        verif_option := true
    | "induction" ->
        if !induction_option
        then input_error "The option induction or noInduction has already been declared." ext;
        induction := true;
        induction_option := true
    | "noInduction" ->
        if !induction_option
        then input_error "The option induction or noInduction has already been declared." ext;
        induction := false;
        induction_option := true
    | "keep" ->
        if kind_lemma = None || kind_lemma = Some KLemma
        then input_error "Only axioms and restrictions can have the option 'keep'." ext;
        if !keep
        then input_error "The option keep has already been declared." ext;
        keep := true
    | _ -> input_error "Unknown option" ext
  ) options;

  (!max_subset,!induction,!sat_app,!verif_app,!keep,!remove_events)

let transl_query (env,q,options) pi_state =
  let q_state = build_q_state false pi_state in
  let q_state =
    { q_state with q_env = add_env ~time_allowed:true true q_state.q_env env;
      q_choice_message = Some "choice cannot be used in queries" }
  in
  let q' = check_query_list q_state q in

  let (max_subset,induction,sat_app,verif_app,_,_) = transl_option_lemma_query None options in

  let solve_status =
    {
      s_max_subset = max_subset;
      s_ind_sat_app = (if induction then sat_app else LANone);
      s_ind_verif_app = (if induction then verif_app else LANone);
      s_induction = induction
    }
  in

  CorrespQuery(List.map (fun (q, ext) -> (Reduction_helper.check_inj_coherent q, ext)) q', solve_status)

(* Translation lemmas and axioms *)

let transl_lemma kind_lemma (env,q,options) pi_state =
  let q_state = build_q_state false pi_state in

  let is_equivalence_query = match pi_state.pi_process_query with
    | Equivalence _ -> true
    | SingleProcessSingleQuery(_,ChoiceQuery) -> true
    | _ -> false
  in

  let q_state =
    { q_state with q_env = add_env ~time_allowed:true true q_state.q_env env;
      q_is_lemma = Some kind_lemma;
      q_is_equivalence_query = is_equivalence_query }
  in

  let q' = check_lemma_list q_state q in

  List.iter2 (fun q1 q1' ->
    match q1, q1' with
    | ((_, ext), _, _), Some ((RealQuery(_,pub_vars),_), ror_opt) ->
        if is_equivalence_query then
          begin
            if (pub_vars != [] || ror_opt != None) then
              input_error "Lemma not used because there is no matching query" ext
          end
        else
          begin
            let queryl =
              match pi_state.pi_process_query with
              | Equivalence _ -> internal_error "Should be handled before"
              | SingleProcessSingleQuery(_,query) -> [query]
              | SingleProcess(_,queryl) -> queryl
            in
            if not (List.exists (function
              | QueryToTranslate _ -> internal_error "transl_lemma: Queries should have been translated"
              | CorrespQEnc _ | ChoiceQEnc _ -> internal_error "transl_lemma: Queries should not have been encoded"
              | ChoiceQuery | NonInterfQuery _ | WeakSecret _ -> pub_vars == [] && ror_opt == None
              | CorrespQuery(ql, _) ->
                  List.exists (fun (q, ext) -> match q with
                    | PutBegin _ -> false
                    | RealQuery(_, pub_vars')
                    | QSecret(_, pub_vars', Reachability) ->
                        (Terms.same_term_lists pub_vars pub_vars') && (ror_opt == None)
                    | QSecret(ror', pub_vars', RealOrRandom) ->
                        (Terms.same_term_lists pub_vars pub_vars') &&
                        (match ror_opt with
                        | None -> false
                        | Some ror -> Terms.same_term_lists ror ror')
                      ) ql
              ) queryl)
            then
              input_error "Lemma not used because there is no matching query" ext
          end
    | _, None -> ()
    | _ -> internal_error "[pitsyntax.ml >> transl_lemma] Lemmas should be encoded as RealQuery."
    ) q q';

  let (max_subset,induction,sat_app,verif_app,keep,remove_events) = transl_option_lemma_query (Some kind_lemma) options in

  let lemma_list =
    map_opt (function
      | Some((RealQuery _,_ as q), ror_opt) ->
          Some {
            ql_query = q;
            ql_real_or_random = ror_opt;
            ql_original_query = None;
            ql_index_query_for_induction = None;
            ql_application_side = AllSide
        }
      | None -> None
      | _ -> internal_error "[pitsyntax.ml >> transl_lemma] Lemmas should be encoded as RealQuery."
    ) q'
  in

  let lemma_state =
    {
      lemmas = lemma_list;
      is_axiom = kind_lemma;
      max_subset = max_subset;
      sat_app = sat_app;
      verif_app = verif_app;
      induction = induction;
      keep_axiom = keep;
      remove_events = remove_events
    }
  in

  Lemma(lemma_state)

(* Not declarations *)

let get_not not_list pi_state =
  let q_state = build_q_state true pi_state in
  map_opt (fun (env, no) ->
    try
      Some (check_event { q_state with q_env = add_env true q_state.q_env env } no)
    with
    | (MissingNameArg _ | BadBoundName _) as e ->
       handle_bad_bound_names q_state "Ignoring this not declaration." e
    ) not_list

(* For Nounif. Very similar to queries, except that *v is allowed
   and events are not allowed *)

let fget_ident_any state (s, ext) =
   try
     match StringMap.find s state.q_env with
         EVar b ->
           begin
             match b.link with
               FLink t -> (t, b.btype)
             | NoLink -> (FVar b, b.btype)
             | _ -> internal_error "unexpected link in fget_ident_any"
           end
       | EName r ->
           (FFunApp(r, []), snd r.f_type)
       | EFun f ->
           begin
             match f.f_cat with
               Eq _ | Tuple -> ()
             | _ ->  input_error ("function " ^ s ^ " is defined by \"reduc\". Such a function should not be used in a \"nounif\" declaration") ext
           end;
           if fst f.f_type == [] then
             (FFunApp(f,[]), snd f.f_type)
           else
             input_error ("function " ^ s ^ " expects " ^
                          (string_of_int (List.length (fst f.f_type))) ^
                          " arguments but is used without arguments") ext
       | _ ->
           input_error ("identifier " ^ s ^ " should be a variable, a function, or a name") ext
   with Not_found ->
     input_error ("identifier " ^ s ^ " not defined") ext

let rec check_gformat state (term, ext0) =
  match term with
    PFGIdent i -> fget_ident_any state i
  | PFGFunApp((s,ext),l) ->
      (* FunApp: only constructors allowed *)
      let (l', tl') = List.split (List.map (check_gformat state) l) in
      let (f, result_type) = get_fun state.q_env (s,ext) tl' in
      begin
        match f.f_cat with
          Eq _ | Tuple | Choice -> ()
        | _ ->  input_error ("function " ^ s ^ " is defined by \"reduc\". Such a function should not be used in a \"nounif\" declaration") ext
      end;
      (Terms.format_app f l', result_type)
  | PFGTuple l ->
      let (l', tl') = List.split (List.map (check_gformat state) l) in
      (FFunApp(Terms.get_tuple_fun tl', l'), Param.bitstring_type)
  | PFGAny (s,ext) ->
      begin
        try
          match StringMap.find s state.q_env with
            EVar b ->
              begin
                match b.link with
                  NoLink -> (FAny b, b.btype)
                | FLink _ -> input_error "variables preceded by * must not be defined by a binding" ext
                | _ -> internal_error "unexpected link in check_gformat"
              end
          | _ -> input_error (s ^ " should be a variable") ext
        with Not_found ->
          input_error ("variable " ^ s ^ " is not defined") ext
      end
  | PFGName ((s,ext) as id,bl) ->
      let r = find_name_in_glob_table state id in
      if fst r.f_type == Param.tmp_type then
        Parsing_helper.input_error ("You are referring to name " ^ s ^ " in this nounif declaration, but this name will never be generated") ext
      else
        begin
          match r.f_cat with
            Name { prev_inputs_meaning = sl } ->
              List.iter (fun ((s',ext'),_) ->
                if not (List.exists (fun m -> Reduction_helper.meaning_encode m = s') sl) then
                  raise (MissingNameArg(s,s',ext))
                           ) bl;
              let p = List.map2 (fun m ty ->
                fbinding_find state (Reduction_helper.meaning_encode m) ty bl) sl (fst r.f_type)
              in
              (FFunApp(r, p), snd r.f_type)
          | _ -> internal_error "name expected here"
        end
  | PFGLet(id,t,t') -> check_gformat (add_fbinding state (id,t)) t'

and fbinding_find state s ty = function
    [] -> FAny (Terms.new_var_def ty)
  | ((s',ext),t)::l ->
      if s' = s then
        begin
          let (t', ty') = check_gformat state t in
          if ty' != ty then
            input_error ("this variable is of type " ^ ty.tname ^ " but is given a value of type " ^ ty'.tname) ext;
          if (s <> "") && (s.[0] = '!') then
            begin
              match t' with
                FVar _ | FAny _ -> ()
              | _ -> input_error "session identifiers should be variables" ext
            end;
          t'
        end
      else
        fbinding_find state s ty l

and add_fbinding state ((i,ext),t) =
  begin
    try
      match StringMap.find i state.q_env with
        EVar _ -> input_error ("variable " ^ i ^ " already defined") ext
      | _ -> ()
    with Not_found -> ()
  end;
  let (t', ty') = check_gformat state t in
  let v = Terms.new_var i ty' in
  v.link <- FLink t';
  { state with q_env = StringMap.add i (EVar v) state.q_env }

let rec check_table_gformat state (term, ext0) =
  match term with
  | PFGFunApp((s,ext),l) ->
      (* FunApp: only tables allowed *)
      let (l', tl') = List.split (List.map (check_gformat state) l) in
      let f = get_table_fun state.q_env (s,ext) tl' in
      FFunApp(f, l')
  | _ -> input_error "Table term expected" ext0

let check_event_gformat state (term, ext0) =
  match term with
  | PFGFunApp((s,ext),l) ->
      (* FunApp: only event allowed *)
      let (l', tl') = List.split (List.map (check_gformat state) l) in
      let f = get_event_fun state.q_env (s,ext) tl' in
      FFunApp(f, l')
  | _ -> input_error "Event term expected" ext0

let check_gfact_format state concl_opt ((s, ext), tl, n) =
  match s with
    "attacker" ->
      begin
        match tl with
          [t1] ->
            let (t1', ty1) = check_gformat state t1 in
            let att_n = Param.get_pred (Attacker((if n = -1 then state.q_max_phase else n), ty1))
            in
            (att_n, [t1'])
        | _ ->
            input_error "arity of predicate attacker should be 1" ext
      end
  | "mess" ->
      begin
        match tl with
          [t1;t2] ->
            let (t1', ty1) = check_gformat state t1 in
            let (t2', ty2) = check_gformat state t2 in
            if ty1 != Param.channel_type then
              input_error ("First argument of mess is of type " ^ ty1.tname ^ " and should be of type channel") ext;
            let mess_n = Param.get_pred (Mess((if n = -1 then state.q_max_phase else n), ty2))
            in
            (mess_n, [t1';t2'])
        | _ ->
            input_error "arity of predicate mess should be 2" ext
      end
  | "table" ->
      begin
        match tl with
          [t1] ->
            let t1' = check_table_gformat state t1 in
            let table_n = Param.get_pred (Table((if n = -1 then state.q_max_phase else n)))
            in
            (table_n, [t1'])
        | _ ->
            input_error "arity of predicate table should be 1" ext
      end
  | "event" ->
      let is_concl = ref false in
      let is_induction_sat = ref false in
      List.iter (function
        | Conclusion -> is_concl := true
        | InductionSat _ -> is_induction_sat := true
        | _ -> ()
      ) concl_opt;
      if not (!is_concl || !is_induction_sat)
      then input_error "Nounif declaration on an event must have the option 'conclusion' or 'inductionOn'" ext;

      if !is_concl && !is_induction_sat
      then input_error "Nounif declaration on an event cannot have both the options 'conclusion' and 'inductionOn'. Make two separate declarations." ext;

      begin
        match tl with
          [t1] ->
            let t1' = check_event_gformat state t1 in
            let p = if !is_concl then Param.event_pred else Param.event_pred_block in
            (p, [t1'])
        | _ ->
            input_error "arity of predicate event should be 1" ext
      end
  | s ->
      let (tl', tyl) = List.split (List.map (check_gformat state) tl) in
      (get_pred state.q_env (s,ext) tyl, tl')

(* [check_induction_format vl f] is [true] if and only if the variables in [vl]
   do not occur in a FAny in [f]. *)
let rec check_induction_format vl = function
  | FFunApp(_,args) -> List.iter (check_induction_format vl) args
  | FAny v' ->
      List.iter (fun (v,(s,ext)) ->
        if v == v'
        then input_error ("The variable " ^ s ^ " declared for induction should not be used with * in the fact.") ext;
      ) vl
  | _ -> ()

(* In [handle_nounif state nounif_op has_concl test_var], the function [test_var]
    verifies that the variables declared with the option [inductionOn] do not
    occur in a FAny position. *)
let rec handle_nounif state nounif_value nounif_op  test_var = function
    BFLet(id,t,nounif) -> handle_nounif (add_fbinding state (id,t)) nounif_value nounif_op test_var nounif
  | BFNoUnif fact ->
      let format = check_gfact_format state nounif_op fact in
      test_var format;
      (format, nounif_value,nounif_op)

let check_nounif_options pi_state nounif_value opt =
  if opt = []
  then [Hypothesis], (fun _ -> ())
  else
    begin
      let hyp_op_decl = ref false in
      let hyp_op = ref false in
      let concl_op = ref false in
      let induc_verif_op = ref false in
      let induc_sat_op = ref None in

      List.iter (fun (i,arg) -> match i with
        | "hypothesis", ext ->
            if !hyp_op_decl
            then input_warning "The option hypothesis has already been declared" ext;
            check_no_param_option (i,arg);
            hyp_op_decl := true;
            hyp_op := true
        | "conclusion", ext ->
            if !concl_op
            then input_warning "The option conclusion has already been declared" ext;
            check_no_param_option (i,arg);
            concl_op := true
        | "ignoreAFewTimes",ext ->
            if !induc_verif_op
            then input_warning "The option ignoreAFewTimes has already been declared" ext;
            begin match nounif_value with
              | NoUnifPosDefault -> input_error "The option ignoreAFewTimes cannot be used with a positive select (or a negative nounif)." ext
              | NoUnifValue n when n > 0 -> input_error "The option ignoreAFewTimes cannot be used with a positive select (or a negative nounif)." ext
              | _ -> ()
            end;
            check_no_param_option (i,arg);
            induc_verif_op := true;
            hyp_op := true
        | "inductionOn",ext ->
            if !induc_sat_op != None
            then input_warning "The option inductionOn has already been declared" ext;
            begin match nounif_value with
              | NoUnifPosDefault -> input_error "The option inductionOn cannot be used with a positive select (or a negative nounif)." ext
              | NoUnifValue n when n > 0 -> input_error "The option inductionOn cannot be used with a positive select (or a negative nounif)." ext
              | _ -> ()
            end;
            induc_sat_op := Some (get_param_option (i,arg));
            hyp_op := true
        | _, ext -> input_error "The only options available for nounif declaration are: hypothesis, conclusion, ignoreAFewTimes and inductionOn. The option inductionOn takes a variable as parameter." ext
      ) opt;

      let op_acc = ref [] in
      if !hyp_op then op_acc := Hypothesis :: !op_acc;
      if !concl_op then op_acc := Conclusion :: !op_acc;
      if !induc_verif_op then op_acc := InductionVerif :: !op_acc;

      match !induc_sat_op with
        | None -> !op_acc, (fun _ -> ())
        | Some bl ->
            let bl_ext =
              List.map (fun (s,ext) ->
                match StringMap.find s pi_state.q_env with
                  | EVar b ->
                      if b.btype != Param.nat_type
                      then input_error ("variable " ^ s ^ " used for inductions should be of type nat but is here of type " ^ b.btype.tname) ext;
                      b, (s,ext)
                 | _ -> input_error (s ^ " should be a variable") ext
              ) bl
            in
            (InductionSat (List.map (fun (b,_) -> b) bl_ext)) :: !op_acc,
            (fun (_,args) ->
              List.iter (check_induction_format bl_ext) args;
              List.iter (fun (b,(s,ext)) ->
                if not (List.exists (Terms.occurs_var_format b) args) then
                  input_error ("The variable " ^ s ^ " declared for induction should occur in the fact.") ext
                    ) bl_ext
                )
    end

let get_nounif nounif_list pi_state =
  let q_state = build_q_state true pi_state in
  map_opt (fun (env, nounif,nounif_value,nounif_op) ->
    try
      let q_state1 = { q_state with q_env = add_env true q_state.q_env env } in

      let (nounif_op',test_var) = check_nounif_options q_state1 nounif_value nounif_op in
      Some (handle_nounif q_state1 nounif_value nounif_op' test_var nounif)
    with
    | (MissingNameArg _ | BadBoundName _) as e ->
       handle_bad_bound_names q_state "Ignoring this nounif declaration." e
    ) nounif_list

(********************************************
 Local state of the main parsing function
*********************************************)

let equations = ref []
let disequations = ref []
let destructors_check_deterministic = ref []
let ids_with_global_refs = ref []

let corresp_query_list = ref ([] : (envdecl * tquery_e list) list)
let query_list = ref ([] : t_query list)
let not_list = ref ([] : (envdecl * gterm_e) list)
let input_clauses = ref ([] : (fact list * fact * constraints * label) list)
let elimtrue = ref ([] : fact list)
let equiv_list = ref ([] : (fact list * fact * int) list)
let nounif_list = ref ([] : (envdecl * nounif_t * nounif_value * options list) list)

let lemma_list = ref ([] : t_lemmas list)

let global_env = ref (StringMap.empty : envElement StringMap.t)

let check_no_def id ext =
  if StringMap.mem id (!global_env) then
    input_error ("identifier " ^ id ^ " already defined (as a free name, a function, a predicate, a type, an event, a table, or a process)") ext
    
(*********************************************
                Parsing files
**********************************************)

let parse filename =
  try
    let ic = open_in filename in
    let lexbuf = Lexing.from_channel ic in
    lexbuf.Lexing.lex_curr_p <- { lexbuf.Lexing.lex_curr_p with
                                  Lexing.pos_fname = filename };
    let ptree =
      try
        Pitparser.all Pitlexer.token lexbuf
      with Parsing.Parse_error ->
        input_error "Syntax error" (extent lexbuf)
    in
    close_in ic;
    ptree
  with Sys_error s ->
    user_error ("File error: " ^ s)

let parse_lib filename =
  let filename =
    if StringPlus.case_insensitive_ends_with filename ".pvl" then
      filename
    else
      filename ^ ".pvl"
  in
  try
    let ic = open_in filename in
    let lexbuf = Lexing.from_channel ic in
    lexbuf.Lexing.lex_curr_p <- { lexbuf.Lexing.lex_curr_p with
                                  Lexing.pos_fname = filename };
    let ptree =
      try
        Pitparser.lib Pitlexer.token lexbuf
      with Parsing.Parse_error ->
        input_error "Syntax error" (extent lexbuf)
    in
    close_in ic;
    ptree
  with Sys_error s ->
    user_error ("File error: " ^ s)

let parse_with_lib filename =
  let rec parse_all_lib = function
    | [] -> parse filename
    | lib::q ->
        let decl_lib = parse_lib lib in
        let (decl_other,p,second_p) = parse_all_lib q in
        (decl_lib @ decl_other, p,second_p)
  in
  (* In [Param.lib_name], the librairies are in the reverse order
     in which they should be included *)
  let libs =
    match !Param.lib_name with
    | [] ->
	(* Use default library when no library is mentioned and it exists *)
	let filename = "default.pvl" in
	if Sys.file_exists filename then
	  [filename]
	else
	  (* Look for the default library also in the ProVerif directory *)
	  let filename' = Filename.concat (Filename.dirname Sys.executable_name) filename in
	  if Sys.file_exists filename' then
	    [filename']
	  else
	    []
    | l -> List.rev l
  in
  parse_all_lib libs

(*******************************************
Get identifiers with global references, to
make sure that we keep them when they appear
as arguments of processes or letfun.
******************************************)

let add_id accu (s,ext) =
  if not (List.mem s (!accu)) then
    accu := s :: (!accu)

let get_ids_with_global_refs_query accu (q, _) =
  match q with
    PPutBegin _ -> ()
  | PRealQuery(_,pub_vars) -> List.iter (add_id accu) pub_vars
  | PQSecret(s,pub_vars,_) -> add_id accu s; List.iter (add_id accu) pub_vars

let get_ids_with_global_refs_decl accu = function
    TQuery(_, ql,_) ->
      List.iter (get_ids_with_global_refs_query accu) ql
  | _ -> ()


(********* Types ***********
This section is composed of two main functions :
- [get_type : Ptree.ident -> Types.typet]
        [get_type (s,_)] returns the type associated to [s] in [global_env] if [s] isn't the pre-defined type ["sid"] and ["any_type"]
- [check_type_decl : Ptree.ident -> unit]
        [check_type_decl (s,_)] first checks if [s] is not ["any_type"], ["sid"], or already defined.
If not, then the type is added into [global_env]
****************************)

let get_type_polym polym sid_allowed id =
  get_type_polym (!global_env) polym sid_allowed id

let get_type ty = get_type_polym false false ty

(** [check_type_decl (s,ext)] first checks if [s] is not ["any_type"], ["sid"], or already defined.
If not, then the type is added into [global_env] *)
let check_type_decl (s, ext) =
  if s = "any_type" then
    input_error "type any_type reserved for polymorphism" ext;
  if s = "sid" then
    input_error "type sid reserved for session identifiers" ext;
  check_no_def s ext;
  let r = { tname = s } in
  global_env := StringMap.add s (EType r) (!global_env)

(*********************************************
          Functions For Environment
**********************************************)

let initialize_env () =
  (* Initial functions and constant *)
  Display.record_id "true" dummy_ext;
  global_env := StringMap.add "true" (EFun Terms.true_cst) (!global_env);

  Display.record_id "false" dummy_ext;
  global_env := StringMap.add "false" (EFun Terms.false_cst) (!global_env);

  Display.record_id "not" dummy_ext;
  global_env := StringMap.add "not" (EFun (Terms.not_fun())) (!global_env);

  Display.record_id "&&" dummy_ext;
  global_env := StringMap.add "&&" (EFun (Terms.and_fun())) (!global_env);

  Display.record_id "||" dummy_ext;
  global_env := StringMap.add "||" (EFun (Terms.or_fun())) (!global_env);

  Display.record_id "0" dummy_ext;
  global_env := StringMap.add "0" (EFun Terms.zero_cst) (!global_env);

  Display.record_id "+" dummy_ext;
  global_env := StringMap.add "+" (EFun Terms.succ_fun) (!global_env);

  Display.record_id ">" dummy_ext;
  global_env := StringMap.add ">" (EFun (Terms.greater_fun ())) (!global_env);

  Display.record_id ">=" dummy_ext;
  global_env := StringMap.add ">=" (EFun (Terms.geq_fun ())) (!global_env);

  Display.record_id "<" dummy_ext;
  global_env := StringMap.add "<" (EFun (Terms.less_fun ())) (!global_env);

  Display.record_id "<=" dummy_ext;
  global_env := StringMap.add "<=" (EFun (Terms.leq_fun ())) (!global_env);

  Display.record_id "is_nat" dummy_ext;
  global_env := StringMap.add "is_nat" (EFun (Terms.is_nat_fun ())) (!global_env);

  List.iter (fun id ->
    Display.record_id id dummy_ext;
    global_env := StringMap.add id EReserved (!global_env)
	) ["mess";"table";"attacker";"subterm";"any_type";"time";"sid"];
    
  List.iter (fun t ->
    Display.record_id t.tname dummy_ext;
    global_env := StringMap.add t.tname (EType t) (!global_env)
         ) Param.types_initial

let get_var env (s,ext) =
  try
    match StringMap.find s env with
      EVar v -> v
    | _ -> input_error (s ^ " should be a variable") ext
  with Not_found ->
    input_error ("variable " ^ s ^ " not declared") ext

(* environment *)

let create_env l =
  add_env false (!global_env) l

(* May-fail environment *)

let add_env_may_fail sid_allowed env l =
  let env_ref = ref env in
  List.iter (fun ((s,ext),ty,can_fail) ->
    let t = get_type_polym false sid_allowed ty in
    begin
      try
        match StringMap.find s (!env_ref) with
            | EVar v when v.unfailing && can_fail -> input_error ("variable " ^ s ^ " already defined") ext
            | EVar _ when can_fail -> input_error ("variable "^s^" was already defined as a may fail variable") ext
            | EVar _ -> input_error ("variable "^s^" was already defined as a message variable") ext
            | _ -> input_warning ("identifier " ^ s ^ " rebound") ext
      with Not_found -> ()
    end;

    let var = Terms.new_var ~may_fail:can_fail s t in
    env_ref := StringMap.add s (EVar var) (!env_ref)
  ) l;
  !env_ref

let create_may_fail_env l =
  add_env_may_fail false (!global_env) l

(*********************************************
        Check constructor declaration
**********************************************)

let check_fun_decl (name, ext) argtypes restype options =
  let tyarg = List.map get_type argtypes in
  let tyres = get_type restype in
  check_no_def name ext;
  if tyres == Param.nat_type || tyres == Param.bool_type
  then
    begin
      if argtypes = [] then
        input_error ("The constant " ^ name ^ " cannot be declared with type '"^tyres.tname^"'") ext
      else
        input_error ("The function " ^ name ^ " cannot be declared with '"^tyres.tname^"' as a return type") ext
    end;
  let is_tuple = ref false in
  let is_private = ref false in
  let opt = ref 0 in
  List.iter (function
        ("data",_) -> is_tuple := true
      | ("projection" | "uniform"),_ -> () (* ignored, for compatibility with CryptoVerif *)
      |       ("private",_) -> is_private := true
      | ("typeConverter",_) ->
          if List.length tyarg != 1 then
            input_error "only unary functions can be declared \"typeConverter\"" ext;
          is_tuple := true;
          opt := (!opt) lor Param.fun_TYPECONVERTER
      | (_,ext) ->
        input_error "for functions, the only allowed options are data, private, typeConverter, and projection and uniform, which are ignored, for compatibility with CryptoVerif" ext) options;
  if (!is_tuple) && (!is_private) then
    input_error "a function cannot be declared both data or typeConverter and private" ext;
  let cat = if !is_tuple (* || ((arity == 0) && (not is_private)) *) then Tuple else Eq [] in
  let r = { f_name = Fixed name;
            f_type = tyarg, tyres;
            f_cat = cat;
            f_initial_cat = cat;
            f_private = !is_private;
            f_options = !opt;
            f_record = Param.fresh_record () }
  in
  if r.f_options land Param.fun_TYPECONVERTER == 0
  then Database.record_fun r;
  global_env := StringMap.add name (EFun r) (!global_env)

(*********************************************
         Check destructor declaration
**********************************************)

(* Destructor to check *)

let f_eq_tuple f s ext =
  match f.f_cat with
    Eq _ | Tuple -> ()
  | Name _ -> input_error (s ^ " is a name; it should not appear in equations or rewrite rules") ext
  | Red _ -> input_error (s ^ " is a function defined by rewrite rules; it should not appear in equations or rewrite rules") ext
  | _ -> input_error (s ^ " should not appear in equations or rewrite rules") ext

let f_any f s ext =
  match f.f_cat with
    Choice -> input_error "function choice should not appear in clauses or elimtrue" ext
  | Name _ -> input_error "names should not appear in clauses or elimtrue" ext
  | _ -> ()

let f_eq_tuple_name f s ext =
  match f.f_cat with
    Eq _ | Tuple | Name _ -> ()
  | Red _ -> input_error (s ^ " is a function defined by rewrite rules. It should not appear in non-interference queries") ext
  | _ -> input_error (s ^ " should not appear in non-interference queries") ext


(* Check messages *)

let rec check_eq_term f_allowed fail_allowed_top fail_allowed_all env (term,ext) =
  match term with
    | PFail -> input_error "The constant fail should not appear in this term" ext
    | (PIdent (s,ext)) ->
        begin try
          match StringMap.find s env with
            | EVar v when (not (fail_allowed_top || fail_allowed_all)) && v.unfailing ->
                input_error ("The may-fail variable " ^ s ^ " cannot be used in this term.") ext
            | EVar v -> Var v, v.btype
            | EFun f ->
                if fst f.f_type <> [] then
                input_error ("function " ^ s ^ " expects " ^
                  (string_of_int (List.length (fst f.f_type))) ^
                  " arguments but is used without arguments") ext;

                f_allowed f s ext;
                FunApp(f, []), snd f.f_type
            | EName r ->
                f_allowed r s ext;
                FunApp (r, []), snd r.f_type
            | ELetEq (t,ty) -> t,ty
            | _ -> input_error ("identifier " ^ s ^ " should be a function, a variable, or a name") ext
        with Not_found ->
          input_error ("identifier " ^ s ^ " not defined") ext
        end
    | (PFunApp ((f,ext), tlist)) ->
      (* FunApp: the allowed functions depend on f_allowed
         Three values of f_allowed are used:
         - f_eq_tuple: allow constructors only (for equations and definitions of destructors)
         - f_any: allow all functions except choice and names (for clauses and elimtrue)
         - f_eq_tuple_name: allow constructors and names (for non-interference queries)
         Predicates are never allowed. *)
      let (tl', tyl) = List.split (List.map (check_eq_term f_allowed false fail_allowed_all env) tlist) in
      let (f', result_type) = get_fun env (f,ext) tyl in
      f_allowed f' f ext;
      (Terms.app f' tl', result_type)

  | (PTuple tlist) ->
      let (tl', tyl) = List.split (List.map (check_eq_term f_allowed false fail_allowed_all env) tlist) in
      (FunApp (Terms.get_tuple_fun tyl, tl'), Param.bitstring_type)

  | PProj _ ->
      input_error "projections not allowed here" ext

let rec check_extended_equation may_fail var_env = function
  | EETerm t -> (var_env,t)
  | EELet ((x,ext),t,eq) ->
      try
        begin match StringMap.find x var_env with
          | EVar _ -> input_error ("variable " ^ x ^ " already defined") ext
          | _ -> input_error ("identifier " ^ x ^ " already defined") ext
        end
      with Not_found ->
        let (t',ty') = check_eq_term f_eq_tuple may_fail false var_env t in
        let var_env' = StringMap.add x (ELetEq (t',ty')) var_env in
        check_extended_equation may_fail var_env' eq

(* Check may-fail message *)

let check_may_fail_term env type_term (mterm,ext) = match mterm with
  | PFail ->
      Terms.get_fail_term type_term
  | _ ->
      let t, type_t = check_eq_term f_eq_tuple true false env (mterm,ext) in
      if type_t != type_term then
        input_error ("the term is of type "^type_t.tname^" but the type "^type_term.tname^" was expected") ext;
      t

(* Equations *)

let check_equation (var_env, t1, t2) =
  let (t1', ty1) = check_eq_term f_eq_tuple false false var_env t1 in
  let (t2', ty2) = check_eq_term f_eq_tuple false false var_env t2 in
  if ty1 != ty2 then
    begin
      let ext = merge_ext (snd t1) (snd t2) in
      input_error "the two members of an equation should have the same type" ext
    end;
  (t1', t2')

let check_equation_one_term (var_env, t1) =
  let (t1', ty1) = check_eq_term f_eq_tuple false false var_env t1 in
  if ty1 != Param.bool_type then
    input_error "when an equation declaration is just a term, it should have type bool" (snd t1);
  (t1', Terms.true_term)

let check_equations l eqinfo =
  let eqinfo = List.filter (fun (s,ext) -> s <> "manual") eqinfo in
  let eqinfo' = match eqinfo with
    [] -> EqNoInfo
  | ["convergent",ext] -> EqConvergent
  | ["linear",ext] -> EqLinear
  | (_,ext)::_ -> Parsing_helper.input_error "for equations, the only allowed options are either \"convergent\" or \"linear\" (\"manual\" is ignored for compatibility with CryptoVerif)" ext
  in
  let l' = map_opt (fun (env, t) ->
    let var_env = create_env env in
    let (var_env',t') = check_extended_equation false var_env t in
    match t' with
      PFunApp(("=",_), [t1;t2]),_ ->
        Some (check_equation (var_env', t1, t2))
    | PFunApp(("<>",_), [t1;t2]), ext ->
        if eqinfo' != EqNoInfo then
          Parsing_helper.input_error "disequations should not have options [convergent] or [linear]" ext;
        disequations := (check_equation (var_env', t1, t2)) :: (!disequations);
        None
    | t1 ->
        Some (check_equation_one_term (var_env', t1))
          ) l
  in
  if l' <> [] then
    equations := (l', eqinfo') :: (!equations)

(* Definition of destructors using Otherwise. *)

let check_red_may_fail (f,ext) type_arg type_res tlist options =
  let ty_arg = List.map get_type type_arg in
  let ty_res = get_type type_res in

  check_no_def f ext;

  if List.mem f special_functions then
    input_error (f ^ " not allowed here") ext;

  let rec generate_rules prev_args red_list = match red_list with
     | [] -> [],prev_args
     | (var_def,t)::q ->
          let env = create_may_fail_env var_def in
          let (env',t') = check_extended_equation true env t in

          match t' with
            | PFunApp(("=",_), [(PFunApp((f',ext'),l1),_);t2]),_ ->

                if f <> f' then
                  input_error ("In \"reduc\", all rewrite rules should begin with the same function " ^ f) ext';

                if List.length ty_arg != List.length l1 then
                  input_error ("Function " ^ f ^ " expects " ^
                              (string_of_int (List.length ty_arg)) ^
                              " argument(s) but is here given " ^
                              (string_of_int (List.length l1)) ^ " argument(s)") ext';

                let lhs = List.map2 (check_may_fail_term env') ty_arg l1
                and rhs = check_may_fail_term env' ty_res t2 in

                (* Generate the destructors from side condition *)

                if lhs = []
                then ([[],rhs,Terms.true_constraints], [])
                else
                  begin try
                    let destructors = Terms.generate_destructor_with_side_cond prev_args lhs rhs ext' in
                    let next_destructors,all_args = generate_rules (lhs::prev_args) q in

                    (destructors @ next_destructors), all_args
                  with Terms.False_inequality ->
                    (* This otherwise and all the next ones are not satisfiable anymore (we should raise a warning probably) *)
                    ([],prev_args)
                  end
            | PFunApp(("=",_), [(_, ext1);_]),_ -> input_error ("In \"reduc\", all rewrite rules should begin with function application") ext1
            | _,ext1 -> input_error ("In \"reduc\", all rewrite rules should be an equality between two terms") ext1

  in

  let red_list,all_args = generate_rules [] tlist in

  (* Generate the failing case *)
  let may_fail_vars = List.map (Terms.new_var_def_term ~may_fail:true) ty_arg
  and fail_term = Terms.get_fail_term ty_res in

  let complete_red_list =
    if may_fail_vars = []
    then red_list
    else
      begin try
        red_list @ (Terms.generate_destructor_with_side_cond all_args may_fail_vars fail_term Parsing_helper.dummy_ext)
      with
        Terms.False_inequality -> red_list
      end
  in

  assert (complete_red_list != []);

  let cat = Red complete_red_list in
  let is_private = ref false in

  List.iter (function
    | ("private",_) -> is_private := true
    | (_,ext) -> input_error "for functions defined by rewrite rules, the only allowed option is private" ext
  ) options;

  let fsymb =
    {
      f_name = Fixed f;
      f_type = ty_arg, ty_res;
      f_private = !is_private;
      f_options = 0;
      f_cat = cat;
      f_initial_cat = cat;
      f_record = Param.fresh_record ()
    } in

  (* Adding the destructor for checking; even destructors with "otherwise"
     can be non-deterministic in the presence of equations *)
  destructors_check_deterministic := fsymb::(!destructors_check_deterministic);

  (* Adding the destructor in environment *)

  (*Display.Text.display_red fsymb complete_red_list;*)
  global_env := StringMap.add f (EFun fsymb) (!global_env)

(* Old definition of destructors, without otherwise *)

let rec get_top_symbol_reduc = function
  | EETerm (PFunApp(("=",_), [(PFunApp((f,ext),_),_);_]),_) -> (f,ext)
  | EETerm (PFunApp(("=",_), [(_, ext1);_]),_) ->
      input_error ("In \"reduc\", all rewrite rules should begin with function application") ext1
  | EETerm (_,ext1) ->
      input_error ("In \"reduc\", all rewrite rules should be an equality between two terms") ext1
  | EELet (_,_,eq) -> get_top_symbol_reduc eq

let check_red tlist options =

  match tlist with
    | (_,t1)::_ ->
      begin
        let (f,ext) = get_top_symbol_reduc t1 in

        if List.mem f special_functions then
          input_error (f ^ " not allowed here") ext;

        check_no_def f ext;

        let red_list, ty_red_list = List.split (
          List.map (fun (var_def,t) ->
            let env = create_env var_def in
            let (env',t') = check_extended_equation false env t in

            match t' with
              | PFunApp(("=",_), [(PFunApp((f',ext'),l1),_);t2]),_ ->
                  if f <> f' then
                    input_error ("In \"reduc\", all rewrite rules should begin with the same function " ^ f) ext';

                  let (lhs, tylhs), (rhs, tyrhs) = (List.split (List.map (check_eq_term f_eq_tuple false false env') l1), check_eq_term f_eq_tuple false false env' t2) in
                  let var_list_rhs = ref [] in
                  Terms.get_vars var_list_rhs rhs;

                  if not (List.for_all (fun v -> List.exists (Terms.occurs_var v) lhs) (!var_list_rhs)) then
                    Parsing_helper.input_error "All variables of the right-hand side of a \"reduc\" definition\nshould also occur in the left-hand side." ext';

                  (lhs, rhs, Terms.true_constraints), (tylhs, tyrhs)
              | PFunApp(("=",_), [(_, ext1);_]),_ -> input_error ("In \"reduc\", all rewrite rules should begin with function application") ext1
              | _,ext1 -> input_error ("In \"reduc\", all rewrite rules should be an equality between two terms") ext1
          ) tlist
        ) in

        match ty_red_list with
          | [] -> internal_error "reduction with empty list"
          | (tylhs,tyrhs)::r ->
              List.iter (fun (tylhs',tyrhs') ->
                if not (Terms.eq_lists tylhs tylhs') then
                  input_error ("the arguments of function " ^ f ^ " do not have the same type in all rewrite rules") ext;

                if not (tyrhs == tyrhs') then
                  input_error ("the result of function " ^ f ^ " does not have the same type in all rewrite rules") ext
              ) r;

              let red_list' =
                begin
                  let var_list = List.map (fun ty -> Terms.new_var_def_term ty) tylhs
                  and fail = Terms.get_fail_term tyrhs
                  and tuple_symb = Terms.get_tuple_fun tylhs in

                  let tuple = FunApp(tuple_symb, var_list) in

                  assert (!Terms.current_bound_vars == []);

                  let side_cond_neq =
                    List.map (fun (arg_list,_,_) ->
                      [tuple,FunApp(tuple_symb, List.map (Terms.generalize_vars_not_in []) arg_list)]
                    ) red_list in
                  let side_cond = { neq = side_cond_neq; geq = []; is_nat = []; is_not_nat = []} in

                  Terms.cleanup ();
                  try
                    let side_cond' = TermsEq.simple_simplify_constraints side_cond in
                    red_list @ ((var_list,fail,side_cond')::(Terms.complete_semantics_constructors tylhs tyrhs))
                  with TermsEq.FalseConstraint ->
                    red_list @ (Terms.complete_semantics_constructors tylhs tyrhs)
                end in

              let cat = Red red_list' in
              let is_private = ref false in

              List.iter (function
                | ("private",_) -> is_private := true
                | (_,ext) ->
                  input_error "for functions defined by rewrite rules, the only allowed option is private" ext
              ) options;

              let fsymb = {
                  f_name = Fixed f;
                  f_type = tylhs, tyrhs;
                  f_private = !is_private;
                  f_options = 0;
                  f_cat = cat;
                  f_initial_cat = cat;
                  f_record = Param.fresh_record ()
                } in

              (* Adding the destructor for checking *)

              destructors_check_deterministic := fsymb::(!destructors_check_deterministic);

              (*Display.Text.display_red fsymb red_list';*)

              global_env := StringMap.add f (EFun fsymb) (!global_env)
      end
    | [] -> internal_error "reduction with empty list"

(* Check clauses *)

let rec interpret_info tyl prop = function
    ("memberOptim", ext) ->
      if List.length tyl != 2 then
        input_error "memberOptim makes sense only for predicates of arity 2" ext;
      prop lor Param.pred_ELEM
  | ("block",_) -> prop lor Param.pred_BLOCKING
          (* add other qualifiers here *)
  | (s,ext) -> input_error ("unknown predicate qualifier " ^ s) ext

let check_pred (c,ext) tl info =
  if c = "attacker" || c = "mess" || c = "event" || c = "inj-event" then
    input_error ("predicate name " ^ c ^ " is reserved. You cannot declare it") ext;
  check_no_def c ext;
  let tyl = List.map (get_type_polym true false) tl in
  let prop = List.fold_left (interpret_info tyl) 0 info in
  let r = { p_name = c; p_type = tyl; p_prop = prop;
            p_info = UserPred(
            if List.exists (fun t -> t == Param.any_type) tyl then
              Polym(c, prop, tyl)
            else
              Monom);
            p_record = 0 }
  in
  global_env := StringMap.add c (EPred r) (!global_env)


let add_rule hyp concl constra tag =
  input_clauses := (hyp, concl, constra, tag) :: (!input_clauses)

let equal_pred ty = Param.get_pred (Equal(ty))

let equal_fact t1 t2 =
  Pred(equal_pred (Terms.get_term_type t1), [t1;t2])

let check_cterm env (p,t) =
  let (tl, tyl) = List.split (List.map (check_eq_term f_any false true env) t) in
  (get_pred env p tyl, tl)

let rec check_hyp is_simple (hyp_accu,constra_accu) env (fact, ext) =
  match fact with
  | PFail -> input_error "The constant fail should not appear in this fact" ext
  | PIdent p ->
      let (p',l') = check_cterm env (p,[]) in
      (Pred(p',l')::hyp_accu, constra_accu)
  | PTuple _ -> input_error "tuples not allowed here" ext
  | PProj _ -> input_error "projections not allowed here" ext
  | PFunApp((f,fext) as p, l) ->
      (* FunApp: two cases:
         If is_simple, allow && and predicates
         If not is_simple, allow &&, <>, =, and predicates
         NOTE: in the latter case, I could allow all functions and predicates (except choice),
         for functions other than &&, they should return type boolean, and
         the term t would be encoded as equal:t, true.
         In that case, I should also modify the case PIdent to allow boolean constants. *)
      match f,l with
        "<>", [t1;t2] ->
          if is_simple then
            input_error (f ^ " not allowed here") ext;
          let (t1', ty1) = check_eq_term f_any false true env t1 in
          let (t2', ty2) = check_eq_term f_any false true env t2 in
          if ty1 != ty2 then
            input_error "the two arguments of an inequality test should have the same type" ext;
          (hyp_accu, { constra_accu with neq = [(t1', t2')] :: constra_accu.neq})
      | "=", [t1;t2] ->
          if is_simple then
            input_error (f ^ " not allowed here") ext;
          let (t1', ty1) = check_eq_term f_any false true env t1 in
          let (t2', ty2) = check_eq_term f_any false true env t2 in
          if ty1 != ty2 then
            input_error "the two arguments of an equality test should have the same type" ext;
          ((equal_fact t1' t2')::hyp_accu, constra_accu)
      | "&&", [h1;h2] ->
          check_hyp is_simple (check_hyp is_simple (hyp_accu,constra_accu) env h1) env h2
      | ("<>" | "=" | "&&"), _ -> internal_error ("Bad arity for special function " ^ f)
      | _ ->
          let (p',l') = check_cterm env (p,l) in
          (Pred(p',l')::hyp_accu, constra_accu)

let check_simple_fact env (fact, ext) =
  match fact with
  | PFail -> input_error "The constant fail should not appear in this fact" ext
  | PIdent p ->
      let (p',l') = check_cterm env (p,[]) in
      Pred(p',l')
  | PTuple _ -> input_error "tuples not allowed here" ext
  | PProj _ -> input_error "projections not allowed here" ext
  | PFunApp((f,fext) as p,l) ->
      (* FunApp: only predicates allowed *)
      let (p',l') = check_cterm env (p,l) in
      Pred(p',l')

let check_clause = function
  | (env, PFact(c)) ->
     let env = create_may_fail_env env in
     let concl = check_simple_fact env c in
     add_rule [] concl Terms.true_constraints LblClause
  | (env, PClause(i,c)) ->
     let env = create_may_fail_env env in
     let (hyp, constra) = check_hyp false ([],Terms.true_constraints) env i in
     let concl = check_simple_fact env c in
     add_rule hyp concl constra LblClause
  | (env, PEquiv(i,c,select)) ->
      (* The "select" flag was used to prevent selecting facts that unify with c. It is now ignored. *)
      let env = create_may_fail_env env in
      let (hyp, constra) = check_hyp true ([],Terms.true_constraints) env i in
      if not (Terms.is_true_constraints constra) then
        Parsing_helper.internal_error "Inequality constraints not allowed in equivalences, should be eliminated by check_hyp true\n";
      let concl = check_simple_fact env c in
      add_rule hyp concl Terms.true_constraints LblEquiv;
      List.iter (fun h -> add_rule [concl] h Terms.true_constraints LblEquiv) hyp;
      equiv_list := (hyp, concl, -1)::(!equiv_list) (* TO DO should give a real rule number, but that's not easy... *)


(* List of the free names of the process *)

let add_free_name (s,ext) t options =
  let is_private = ref false in
  List.iter (function
    | ("private",_) -> is_private := true
    | (_,ext) ->
        input_error "for free names, the only allowed option is private" ext) options;
  let ty = get_type t in
  check_no_def s ext;
  if  ty == Param.nat_type || ty == Param.bool_type
  then input_error (Printf.sprintf "The name %s cannot be declared with the type '%s'" s ty.tname) ext;
  let r = Terms.create_name ~allow_rename:false s ([],ty) (!is_private) in
  Database.record_name r;
  global_env := StringMap.add s (EName r) (!global_env)


(* Check non-interference terms *)

let get_non_interf_name env (s,ext) =
   try
     match StringMap.find s env  with
       EName r ->
         if not r.f_private then
           input_error ("Non-interference is certainly false on public values, such as " ^ s) ext
         else
           r
     | _ ->
         input_error ("Non-interference can only be tested on private free names") ext
   with Not_found ->
     input_error ("Name " ^ s ^ " is not declared") ext

let get_non_interf env (id, lopt) =
  let n = get_non_interf_name (create_env env) id in
  (n,
   match lopt with
     None -> None
   | Some l ->
       Some (List.map (fun t ->
         let (t', ty) = check_eq_term f_eq_tuple_name false false (create_env env) t in
         if ty != snd n.f_type then
           input_error ("this term has type " ^ ty.tname ^ " but should have type " ^ (snd n.f_type).tname) (snd t);
         t'
             ) l))

(*********************************************
              Checking Event
**********************************************)

let check_event (name, ext) argtypes =
  let tyarg = List.map get_type argtypes in
  let tyarg = if !Param.key_compromise = 0 then tyarg else Param.sid_type :: tyarg in
  check_no_def name ext;
  let r = { f_name = Fixed name;
            f_type = tyarg, Param.event_type;
            f_cat = Eq[];
            f_initial_cat = Eq[];
            f_private = true;
            f_options = 0;
            f_record = Param.fresh_record () }
  in
  global_env := StringMap.add name (EEvent r) (!global_env)

(*********************************************
              Checking Table
**********************************************)

let check_table (name, ext) argtypes =
  let tyarg = List.map get_type argtypes in
  check_no_def name ext;
  let r = { f_name = Fixed name;
            f_type = tyarg, Param.table_type;
            f_cat = Tuple;
            f_initial_cat = Tuple;
            f_private = true;
            f_options = 0;
            f_record = Param.fresh_record () }
  in
  global_env := StringMap.add name (ETable r) (!global_env)

(*********************************************
               Checking Term
To understand a term coming from the parser, it is first converted
into an [enriched_term] by [check_et], then expanded into
a term and process by [expand_term].
**********************************************)

(*** First, basic functions on enriched terms *)

let is_simple = function
  | ET_Var _ -> true
  | ET_FunApp(_,l) -> List.for_all (fun t -> t.et_simple) l
  | ET_Restr (_,_,t) -> t.et_simple
  | ET_Test(t1,t2,t3) -> t1.et_simple && t2.et_simple && t3.et_simple
  | ET_Let(pat,t1,t2,t3) -> pat.ep_simple && t1.et_simple && t2.et_simple && t3.et_simple
  | ET_Event _ | ET_LetFilter _ | ET_Insert _ | ET_Get _ ->
      false

let is_simple_no_let = function
  | ET_Var _ -> true
  | ET_FunApp(_,l) -> List.for_all (fun t -> t.et_simple_no_let) l
  | ET_Restr (_,_,t) -> t.et_simple_no_let
  | ET_Test(t1,t2,t3) -> t1.et_simple_no_let && t2.et_simple_no_let && t3.et_simple_no_let
  | ET_Let _ | ET_Event _ | ET_LetFilter _ | ET_Insert _ | ET_Get _ ->
      false

let is_simple_no_restr = function
  | ET_Var _ -> true
  | ET_FunApp(_,l) -> List.for_all (fun t -> t.et_simple_no_restr) l
  | ET_Test(t1,t2,t3) -> t1.et_simple_no_restr && t2.et_simple_no_restr && t3.et_simple_no_restr
  | ET_Let(pat,t1,t2,t3) -> pat.ep_simple_no_restr && t1.et_simple_no_restr && t2.et_simple_no_restr && t3.et_simple_no_restr
  | ET_Restr _ | ET_Event _ | ET_LetFilter _ | ET_Insert _ | ET_Get _ ->
      false

let get_et_type = function
  | ET_Var b -> b.btype
  | ET_FunApp(f,_) -> snd f.f_type
  | ET_Restr(_,_,t) | ET_Event(_,_,t) | ET_Insert(_,t) -> t.et_type
  | ET_Test(_,t2,t3) | ET_Let(_,_,t2,t3) | ET_LetFilter(_,_,_,t2,t3) | ET_Get(_,_,t2,t3,_) ->
      assert (Terms.equal_types t2.et_type t3.et_type);
      t2.et_type

let make_et_ty ext ty desc =
  { et_desc = desc;
    et_simple = is_simple desc;
    et_simple_no_let = is_simple_no_let desc;
    et_simple_no_restr = is_simple_no_restr desc;
    et_type = ty;
    et_ext = ext }

let make_et ext desc =
  make_et_ty ext (get_et_type desc) desc

let is_simple_pat = function
  | EP_PatVar _ -> true
  | EP_PatTuple(_,l) -> List.for_all (fun p -> p.ep_simple) l
  | EP_PatEqual t -> t.et_simple

let is_simple_pat_no_restr = function
  | EP_PatVar _ -> true
  | EP_PatTuple(_,l) -> List.for_all (fun p -> p.ep_simple_no_restr) l
  | EP_PatEqual t -> t.et_simple_no_restr

let get_ep_type = function
  | EP_PatVar b -> b.btype
  | EP_PatTuple(f,_) -> snd f.f_type
  | EP_PatEqual t -> t.et_type

let make_ep_ty ty desc =
  { ep_desc = desc;
    ep_simple = is_simple_pat desc;
    ep_simple_no_restr = is_simple_pat_no_restr desc;
    ep_type = ty }

let make_ep desc =
  make_ep_ty (get_ep_type desc) desc

let et_true = make_et dummy_ext (ET_FunApp(Terms.true_cst, []))
let et_false = make_et dummy_ext (ET_FunApp(Terms.false_cst, []))
let et_fail ty = make_et_ty dummy_ext ty (ET_FunApp(Terms.get_fail_symb ty, []))

let et_is_var t =
  match t.et_desc with
  | ET_Var _ -> true
  | _ -> false

let rec var_fun_test et =
  match et.et_desc with
  | ET_Var _ -> true
  | ET_FunApp(_,l) -> List.for_all var_fun_test l
  | ET_Test(t1,t2,t3) -> var_fun_test t1 && var_fun_test t2 && var_fun_test t3
  | ET_Restr _ | ET_Let _ | ET_Event _ | ET_LetFilter _
  | ET_Insert _ | ET_Get _ ->
      false

let rec var_fun_test_pat ep =
  match ep.ep_desc with
  | EP_PatVar _ -> true
  | EP_PatTuple(_,l) -> List.for_all var_fun_test_pat l
  | EP_PatEqual t -> var_fun_test t

(*** [et_term_never_fail t] is true when the enriched term [t]
     never fails *)

let rec et_term_never_fail t =
  match t.et_desc with
  | ET_Var v -> not v.unfailing
  | ET_FunApp(f,args) ->
      begin match f.f_initial_cat with
        | Failure -> false
        | Name _ -> true
        | Choice | ChoiceFst | ChoiceSnd | Tuple | Eq _ -> List.for_all et_term_never_fail args
        | Red rw_rules -> Terms.red_never_fails (List.map et_term_never_fail args) rw_rules
        | SpecVar _ | Syntactic _ | General_var | General_mayfail_var -> Parsing_helper.internal_error "[term.ml >> can_never_fail] Unexpected symbol in processes."
      end
  | ET_Restr(_,_,t) -> et_term_never_fail t
  | ET_Test(t1,t2,t3) -> et_term_never_fail t1 && et_term_never_fail t2 && et_term_never_fail t3
  | ET_Let(pat,t1,t2,t3) ->
      if (match pat.ep_desc with EP_PatVar _ -> true | _ -> false) && et_term_never_fail t1 then
        et_term_never_fail t2
      else
        et_term_never_fail t2 && et_term_never_fail t3
  | ET_Event(t1,_,t2) | ET_LetFilter(_,_,_,t1,t2) | ET_Insert(t1,t2) | ET_Get(_,_,t1,t2,_) ->
      et_term_never_fail t1 && et_term_never_fail t2

(*** [copy_et t] returns a copy of the enriched term [t],
     following links [ETLink] in variables. That implements
     substitutions.

     We must rename bound variables, because [Simplify.copy_process]
     requires variables not to be reused inside their scope,
     and if we did not rename bound variables, that would happen
     when we have several calls to the same function defined by
     letfun one under the other. *)

let get_lets_args_opt = function
    None -> ([], None)
  | Some l ->
      let rec get_lets_args = function
          [] -> ([],[])
        | b::l ->
            let (lets,l') = get_lets_args l in
            match b.link with
              NoLink -> (lets, b::l')
            | VLink v' -> (lets, v'::l')
            | ETLink { et_desc = ET_Var b' } ->
                (lets, b'::l')
            | ETLink t ->
                let b' = Terms.copy_var b in
                let t' =
                  if et_term_never_fail t
                  then t
                  else
                    let glet_symb =  Terms.glet_fun b.btype in
                    make_et t.et_ext (ET_FunApp(glet_symb,[t]))
                in
                ((b', t')::lets, b'::l')
            | _ -> Parsing_helper.internal_error "unexpected link in Pitsyntax.check_term"
      in
      let lets, l' = get_lets_args l in
      (lets, Some l')

let rec put_et_lets p = function
    [] -> p
  | (v,t)::l ->
      let pat = make_ep (EP_PatVar v) in
      let else_t = et_fail p.et_type in
      put_et_lets (make_et t.et_ext (ET_Let(pat,t,p,else_t))) l

let rec copy_et t =
  match t.et_desc with
  | ET_Var v ->
      begin
        match v.link with
        | NoLink -> t
        | ETLink t' -> t'
        | VLink v' -> make_et t.et_ext (ET_Var v')
        | _ -> Parsing_helper.internal_error "unexpected link in copy_et"
      end
  | ET_FunApp(f,args) -> make_et t.et_ext (ET_FunApp(f, List.map copy_et args))
  | ET_Restr(b, (args_opt, env), t') ->
      let (lets, args_opt') = get_lets_args_opt args_opt in
      put_et_lets
        (make_et t.et_ext (ET_Restr(b, (args_opt', env), copy_et t'))) lets
  | ET_Test(t1,t2,t3) ->
      make_et t.et_ext (ET_Test(copy_et t1, copy_et t2, copy_et t3))
  | ET_Let(pat, t1, t2, t3) ->
      let t1' = copy_et t1 in
      let (pat', t2') =
        Terms.auto_cleanup (fun () ->
          let pat' = copy_ep pat in
          let t2' = copy_et t2 in
          (pat', t2')
            )
      in
      let t3' = copy_et t3 in
      make_et t.et_ext (ET_Let(pat', t1', t2', t3'))
  | ET_Event(t1,(args_opt,env),t2) ->
      let (lets, args_opt') = get_lets_args_opt args_opt in
      put_et_lets
        (make_et t.et_ext (ET_Event(copy_et t1, (args_opt', env), copy_et t2))) lets
  | ET_LetFilter(vl, p, tl, t2,t3) ->
      let (vl', tl', t2') =
        Terms.auto_cleanup (fun () ->
          let vl' = List.map (fun v ->
            let v' = Terms.copy_var v in
            Terms.link v (VLink v');
            v'
              ) vl
          in
          let tl' = List.map copy_et tl in
          let t2' = copy_et t2 in
          (vl', tl', t2')
            )
      in
      make_et t.et_ext (ET_LetFilter(vl', p, tl', t2', copy_et t3))
  | ET_Insert(t1,t2) ->
      make_et t.et_ext (ET_Insert(copy_et t1, copy_et t2))
  | ET_Get(pat, t1, t2, t3, precise) ->
      let (pat', t1', t2') =
        Terms.auto_cleanup (fun () ->
          let pat' = copy_ep pat in
          let t1' = copy_et t1 in
          let t2' = copy_et t2 in
          (pat', t1', t2')
            )
      in
      make_et t.et_ext (ET_Get(pat', t1', t2', copy_et t3, precise))

and copy_ep pat =
  match pat.ep_desc with
  | EP_PatVar b ->
      let b' = Terms.copy_var b in
      Terms.link b (VLink b');
      make_ep (EP_PatVar b')
  | EP_PatTuple(f,l) -> make_ep (EP_PatTuple(f, List.map copy_ep l))
  | EP_PatEqual t -> make_ep (EP_PatEqual (copy_et t))



(*** [check_et : Types.envElement Stringmap.StringMap.t -> Pitptree.pterm_e -> Types.enriched_term].
In [check_et env pterm],
-- [env] is the environment that stores the meaning of the elements currently in scope
-- [pterm] is the term that will be checked
The function returns the translated enriched term. *)


let rec get_restr_arg env = function
    [] -> []
  | (s,ext)::l ->
      if List.exists (fun (s',_) -> s' = s) l then
        get_restr_arg env l
      else
        try
          match StringMap.find s env with
            EVar b -> b::(get_restr_arg env l)
          | _ ->
              Parsing_helper.input_error (s ^ " should be a variable") ext
        with Not_found ->
          Parsing_helper.input_error ("variable " ^ s ^ " not defined") ext

let get_restr_arg_opt env = function
    None -> None
  | Some l -> Some (get_restr_arg env l)

let check_no_global_ref (s,ext) =
  if List.mem s (!ids_with_global_refs) then
    input_error ("Variable or name "^s^" defined in a term and referenced in a query. This is not allowed because in general the expansion of terms may not allow "^s^" to be defined exactly when it is in the initial process") ext

let rec check_no_global_ref_pat = function
    PPatVar (id,_) -> check_no_global_ref id
  | PPatTuple(l) | PPatFunApp(_,l) | PPatChoice(_,l,_) ->
      List.iter check_no_global_ref_pat l
  | PPatEqual _ | PPatAny _ -> ()

(* Term from identifier *)

let get_term_from_ident env (s, ext) =
   try
     match StringMap.find s env with
       EVar b ->
         make_et ext (ET_Var b)
     | EName r ->
         make_et ext (ET_FunApp (r,[]))
     | EFun f ->
         if fst f.f_type = [] then
           make_et ext (ET_FunApp(f,[]))
         else
           input_error ("function " ^ s ^ " expects " ^
                        (string_of_int (List.length (fst f.f_type))) ^
                        " arguments but is used without arguments") ext
     | ELetFun(func_proc_layer, arg_type_list, result_type) ->
         if arg_type_list != [] then
             input_error ("letfun function " ^ s ^ " expects " ^
                        (args_to_string arg_type_list) ^
                        " but is used without arguments") ext;
         func_proc_layer []
     | EPred p ->
         if p.p_type != [] then
           input_error ("predicate " ^ s ^ " expects " ^
                        (args_to_string p.p_type) ^
                        " but is used without arguments") ext;
         make_et ext (ET_LetFilter([], p, [], et_true, et_false))
     | _ -> input_error ("identifier " ^ s ^ " should be a variable, a function, a name, or a predicate") ext
   with Not_found ->
     input_error ("Variable, function, name, or predicate " ^ s ^ " not declared") ext


(* [ok_get_cond t] returns true when [t] is acceptable as a condition
   of [get]. event, insert, new, and let ... suchthat that binds variables
   are forbidden because the condition of a get should be a deterministic
   computation. It should not have an effect on the trace (no insert, no event),
   otherwise, is this effect executed for each element of the table? It
   should not introduce a probabilistic computation (new) nor
   a non-deterministic one (let ... suchthat that binds variables). *)
let rec ok_get_cond t =
  match t.et_desc with
  | ET_Insert _ | ET_Event _ | ET_Restr _ | ET_LetFilter(_::_,_,_,_,_) -> false
  | ET_Var _ -> true
  | ET_FunApp(_,l) -> List.for_all ok_get_cond l
  | ET_Test(t1,t2,t3) ->
      (ok_get_cond t1) && (ok_get_cond t2) && (ok_get_cond t3)
  | ET_Let(pat,t1,t2,t3) ->
      (ok_get_cond_pat pat) && (ok_get_cond t1) && (ok_get_cond t2) && (ok_get_cond t3)
  | ET_LetFilter([],_,tl,t2,t3) ->
      (List.for_all ok_get_cond tl) && (ok_get_cond t2) && (ok_get_cond t3)
  | ET_Get(pat,cond,t2,t3,_) ->
      (ok_get_cond_pat pat) && (ok_get_cond t2) && (ok_get_cond t3)

and ok_get_cond_pat pat =
  match pat.ep_desc with
  | EP_PatVar _ -> true
  | EP_PatEqual t -> ok_get_cond t
  | EP_PatTuple(_,l) -> List.for_all ok_get_cond_pat l

let rec has_diff_pat pat =
  match pat.ep_desc with
  | EP_PatVar _ | EP_PatEqual _ -> false
  | EP_PatTuple(f,l) -> f.f_cat == Choice || List.exists has_diff_pat l

let get_precise_option = function
  | [] -> false
  | [("precise",_),None] -> true
  | ((_,ext),_)::q -> Parsing_helper.input_error "Process input, get, let suchthat can only have \"precise\" as option." ext

(* [check_et] itself *)
let rec check_et env (term, ext0) =
  match term with
  | PPIdent(id) ->
      get_term_from_ident env id

  | PPTuple(term_list) ->
      let l = check_et_list env term_list in
      let type_list = List.map (fun t -> t.et_type) l in
      let tuple_symb = Terms.get_tuple_fun type_list in
      make_et ext0 (ET_FunApp(tuple_symb,l))

  | PPRestr((s,ext),args,tyid,t) ->
      check_no_global_ref (s,ext);
      let ty = get_type tyid in
      if (StringMap.mem s env) then
        input_warning ("identifier " ^ s ^ " rebound") ext;
      if  ty == Param.nat_type || ty == Param.bool_type
      then input_error (Printf.sprintf "The name %s cannot be declared with the type '%s'" s ty.tname) ext;
      let r = Terms.create_name s (Param.tmp_type, ty) true in
      Database.record_name r;
      let env' = StringMap.add s (EName r) env in
      let t' = check_et env' t in
      let args_opt = get_restr_arg_opt env args in
      make_et ext0 (ET_Restr(r, (args_opt, env), t'))

  | PPFunApp((s,ext),list_arg) ->
        (* FunApp: all functions (including choice), predicates, and letfun allowed. *)
      begin
        let l = check_et_list env list_arg in
        let type_list = List.map (fun t -> t.et_type) l in
        match get_apply_symb env (s,ext) type_list with
          (EFun f, result_type) ->
            if (f.f_options land Param.fun_TYPECONVERTER != 0) && (Param.get_ignore_types()) then
              (* For a type converter function, the result is directly given : no FunApp.
                 Furthermore, the number of argument should be 1 *)
              match l with
              | [t] -> { t with et_type = result_type }
              | _ -> internal_error "Type converter functions should always be unary"
            else
              make_et_ty ext0 result_type (ET_FunApp(f,l))

        | (ELetFun(func_proc_layer, arg_type_list, result_type), _) ->
            func_proc_layer l

        | (EPred p, result_type) ->
            (* allow predicates, encoded by LetFilter([], p(M1...Mn), true, false *)
            make_et ext0 (ET_LetFilter([], p, l, et_true, et_false))

        | _ -> input_error (s ^ " should be a function or a predicate") ext
      end

  | PPTest(cond,term_then,term_else_opt) ->
      let t_cond = check_et env cond in
      let type_cond = t_cond.et_type in
      let t_then = check_et env term_then in
      let type_then = t_then.et_type in
      let t_else =
        match term_else_opt with
          Some term_else -> check_et env term_else
        | None -> et_fail type_then
      in
      let type_else = t_else.et_type in
      if type_cond != Param.bool_type then
        input_error ("The type of the condition in the test is " ^
                     type_cond.tname ^ " but a boolean is expected.") ext0;
      if type_then != type_else then
        input_error
          (Printf.sprintf "The then and else branches of the test should have the same type, but the then branch is of type %s and the else branch is of type %s."
             type_then.tname type_else.tname)
          ext0;

      make_et ext0 (ET_Test(t_cond, t_then, t_else))

  | PPLet(pat,term,term_then, term_else_opt) ->
      check_no_global_ref_pat pat;
        (* This case will be transformed into a process Let which will never fail,
           and then use the destructor gletresult to get the correct message.*)

      let term' = check_et env term in
      let type_term = term'.et_type in
      let (pat', env') = check_ep ext0 env (Some type_term) pat env in

      let term_then' = check_et env' term_then in
      let type_then = term_then'.et_type in
      let term_else' =
        match term_else_opt with
          Some term_else -> check_et env term_else
        | None -> et_fail type_then
      in

      if type_then != term_else'.et_type
      then input_error "the in and else branches should have the same type" ext0;

      begin
	match term_else_opt, pat'.ep_desc with
	| Some _, EP_PatVar _ when et_term_never_fail term' ->
	    input_error "the else branch of let should be omitted when it cannot be executed (the pattern is a variable and the assigned term cannot fail)" ext0
	| _ -> ()
      end;

      make_et ext0 (ET_Let(pat', term', term_then', term_else'))

  | PPLetFilter(identlist,(fact,ext),term_then,term_else_opt) ->
      List.iter (fun (id,_) -> check_no_global_ref id) identlist;
      let (env', vlist) =
        List.fold_left (fun (env, vlist) ((s,e),t) ->
          if (StringMap.mem s env) then
            input_warning ("identifier " ^ s ^ " rebound") e;

          let ty = get_type t in
          let v = Terms.new_var s ty in
          (StringMap.add s (EVar v) env, v:: vlist)
            ) (env,[]) identlist in

      let vlist = List.rev vlist in

      let (pred, tl) = check_fact env' (fact,ext) in

      let term_then' = check_et env' term_then in
      let type_then = term_then'.et_type in
      let term_else' =
        match term_else_opt with
          Some term_else -> check_et env term_else
        | None -> et_fail type_then
      in

      if type_then != term_else'.et_type then
        input_error "the in and else branches should have the same type" ext;

      make_et ext0 (ET_LetFilter(vlist,pred, tl, term_then', term_else'))

  | PPEvent(id,l, env_args, term_cont) ->
      let l' = check_et_list env l in
      let type_list = List.map (fun t -> t.et_type) l' in
      let env_args' = (get_restr_arg_opt env env_args, env) in
      let term_cont' = check_et env term_cont in
      let type_list, args =
        if !Param.key_compromise == 0 then
          type_list, l'
        else
          Param.sid_type :: type_list,
          (make_et dummy_ext (ET_Var (Terms.new_var_def Param.sid_type))) :: l'
      in
      let f = get_event_fun env id type_list in
      make_et ext0 (ET_Event(make_et ext0 (ET_FunApp(f, args)), env_args',
                             term_cont'))

  | PPInsert(id,l,term_cont) ->
      let l' = check_et_list env l in
      let type_list = List.map (fun t -> t.et_type) l' in
      let f = get_table_fun env id type_list in
      let term_cont' = check_et env term_cont in
      make_et ext0 (ET_Insert(make_et ext0 (ET_FunApp(f,l')), term_cont'))

  | PPGet((i,ext),pat_list,cond_opt,term_then,term_else_opt, opts) ->
      let precise = get_precise_option opts in
      List.iter check_no_global_ref_pat pat_list;
      try
        match StringMap.find i env with
        | ETable f ->
              (* By checking the terms in the patterns in the initial environment env,
                 we make sure that layer_pat cannot reference variables bound in the
                 patterns *)
            if List.length (fst f.f_type) != List.length pat_list then
              input_error ("Table " ^ i ^ " expects " ^
                           (string_of_int (List.length (fst f.f_type))) ^
                           " argument(s) but is here given " ^
                           (string_of_int (List.length pat_list)) ^ " argument(s)") ext;
            let (pat_list', env') = check_ep_list ext env (List.map (fun t -> Some t) (fst f.f_type)) pat_list env in

            let cond' =
              match cond_opt with
              | Some t ->
                  let t' = check_et env' t in
                  let type_cond = t'.et_type in
                  if not (ok_get_cond t') then
                    input_error "new, insert, event, and let x1..xn suchthat with n>0 are not allowed in conditions of get" (snd t);
                  if type_cond != Param.bool_type then
                    input_error ("this term has type " ^ type_cond.tname ^ " but should have type bool") (snd t);
                  t'
              | None ->
                  et_true
            in
            let term_then' = check_et env' term_then in
            let type_then = term_then'.et_type in
            let term_else' =
              match term_else_opt with
                Some term_else -> check_et env term_else
              | None -> et_fail type_then
            in
            let type_else = term_else'.et_type in
            if type_then != type_else then
              input_error
                (Printf.sprintf "The then and else branches of get should have the same type, but the then branch is of type %s and the else branch is of type %s."
                   type_then.tname type_else.tname)
                ext;

            make_et ext0 (ET_Get(make_ep (EP_PatTuple(f,pat_list')), cond',
                         term_then', term_else', precise))
          | _ -> input_error (i ^ " should be a table") ext
        with Not_found ->
          input_error ("table " ^ i ^ " not defined") ext

and check_et_list env = function
  | [] -> []
  | term::q ->
      let tl = check_et_list env q
      and t = check_et env term in
      t::tl


(* Checking Pattern

   [check_ep :
   Parsing_helper.extent ->
   Types.envElement Stringmap.StringMap.t ->
   Types.typet option ->
   Pitptree.tpattern ->
   Types.envElement Stringmap.StringMap.t ->
   Types.enriched_pattern * Types.envElement Stringmap.StringMap.t]

   [check_ep ext environment type_pat_opt pat new_env] converts
   the parsed pattern [pat] into an enriched pattern.
   It returns that enriched pattern as well as an updated environment
   in which the variables bound by the pattern have been added.
   [ext] is the extent of the pattern (used for error messages).
   [environment] is the initial environment in which the pattern
   is checked.
   [new_env] is an environment in which variables bound by other
   parts of the same pattern have been added.
   [type_pat_opt] is the type of the pattern, which it is known.
*)
and check_ep ext environment type_pat_opt pat new_env =
  match pat with
  | PPatVar ((s,e), ty_opt) ->
      let ty =
        match ty_opt, type_pat_opt with
          | None, None -> input_error ("variable " ^ s ^ " should be declared with a type") e
          | Some (t,e), None -> get_type (t,e)
          | None, Some ty -> ty
          | Some (t,e), Some ty ->
              let ty' = get_type (t,e) in
              if ty != ty' then
                input_error ("variable " ^ s ^ " is declared of type " ^ t ^ " but should be of type " ^ ty.tname) e;
              ty
      in

      if (StringMap.mem s new_env) then
        input_warning ("identifier " ^ s ^ " rebound") e;

      let v = Terms.new_var s ty in

      (make_ep (EP_PatVar v), StringMap.add s (EVar v) new_env)
  
  | PPatAny (e,ty_opt) ->
      let ty =
        match ty_opt, type_pat_opt with
          | None, None -> input_error ("the any term pattern '_' should be declared with a type") e
          | Some (t,e), None -> get_type (t,e)
          | None, Some ty -> ty
          | Some (t,e), Some ty ->
              let ty' = get_type (t,e) in
              if ty != ty' then
                input_error ("the any term pattern '_' is declared of type " ^ t ^ " but should be of type " ^ ty.tname) e;
              ty
      in  

      let v = Terms.new_var ~orig:false Param.ignored_var_name ty in

      (make_ep (EP_PatVar v), new_env)

  | PPatTuple list_pat ->
      begin
        match type_pat_opt with
        | None -> ()
        | Some(ty) when ty != Param.bitstring_type ->
            input_error ("pattern is of type " ^ Param.bitstring_type.tname ^
                         " but should be of type " ^ ty.tname) ext
        | _ -> ()
      end;

     let (l_pat, env') = check_ep_list ext environment (List.map (fun _ -> None) list_pat) list_pat new_env in

     let ty_list = List.map (fun pat -> pat.ep_type) l_pat in
     let tuple_symb = Terms.get_tuple_fun ty_list in

     (make_ep (EP_PatTuple(tuple_symb, l_pat)), env')

  | PPatEqual term ->
      (* By checking the term in the initial environment before
         adding variables bound by the pattern, we make sure that
         layer_proc_t does not reference variables bound in the pattern *)
      let t = check_et environment term in
      let type_t = t.et_type in
      begin
        match type_pat_opt with
        | None -> ()
        | Some(ty) ->
            if ty != type_t then
              input_error ("pattern is of type " ^ type_t.tname ^ " but should be of type " ^ ty.tname) (snd term);
      end;
      (make_ep (EP_PatEqual t), new_env)

  | PPatChoice((s,ext),l,tyopt) ->
      (* choice pattern, only if !Param.allow_diff_patterns is true *)
      if not (!Param.allow_diff_patterns) then
        input_error "diff or choice is allowed in patterns only when the setting allowDiffPatterns is true" ext;
      let type_pat_opt' =
        match tyopt, type_pat_opt with
        | None, _ -> type_pat_opt
        | Some (t,e), None -> Some (get_type (t,e))
        | Some (t,e), Some ty ->
            let ty' = get_type (t,e) in
            if ty != ty' then
              input_error ("choice patterns is declared of type " ^ t ^ " but should be of type " ^ ty.tname) e;
            Some ty
      in

      let (pat_l, env') = check_ep_list ext environment [type_pat_opt'; type_pat_opt'] l new_env in
      let (pat1,pat2) =
        match pat_l with
        | [pat1; pat2] -> (pat1,pat2)
        | _ -> assert false
      in
      if has_diff_pat pat1 || has_diff_pat pat2 then
        input_error "nested diff or choice patterns are forbidden" ext;
      if pat1.ep_type != pat2.ep_type then
        input_error "the two terms of a diff or choice pattern should have the same type" ext;

      let choice_fun = Param.choice_fun pat1.ep_type in
      (make_ep_ty pat1.ep_type (EP_PatTuple(choice_fun, pat_l)), env')
  | PPatFunApp((s,ext),l) ->
      (* PatFunApp: only data constructors allowed *)
      try
        begin match StringMap.find s environment with
          | EFun f ->
              begin match type_pat_opt with
                | None -> ()
                | Some ty ->
                    if ty != snd f.f_type then
                      input_error ("pattern is of type " ^ (snd f.f_type).tname ^ " but should be of type " ^ ty.tname) ext;
              end;

              if List.length (fst f.f_type) != List.length l then
                input_error ("Function " ^ s ^ " expects " ^
                             (string_of_int (List.length (fst f.f_type))) ^
                             " argument(s) but is here given " ^
                             (string_of_int (List.length l)) ^ " argument(s)") ext;

              let (pat_l, env') = check_ep_list ext environment (List.map (fun t -> Some t) (fst f.f_type)) l new_env in

              if f.f_cat <> Tuple then
                input_error ("only data functions are allowed in patterns, not " ^ s) ext;

              if (f.f_options land Param.fun_TYPECONVERTER != 0) && (Param.get_ignore_types())
              then
                match pat_l with
                | [t] -> ({ t with ep_type = snd f.f_type }, env')
                | _ -> internal_error "type converter functions should always be unary"
              else
                (make_ep (EP_PatTuple(f, pat_l)), env')
          | _ -> input_error ("only functions can be applied, not " ^ s) ext
        end
      with Not_found ->
        input_error ("function " ^ s ^ " not defined") ext


and check_ep_list ext environment type_pat_list_opt pat_list env = match pat_list,type_pat_list_opt with
  | [],[] -> ([],env)
  | pat::pat_l, ty_pat::ty_pat_l ->
      let (pat, env') = check_ep ext environment ty_pat pat env in
      let (pat_l, env'') = check_ep_list ext environment ty_pat_l pat_l env' in
      (pat::pat_l, env'')
  |_,_ -> internal_error "[check_ep_list] Size of pattern list and type list should be the same"

(* Checking Fact
   [check_fact: Types.envElement Stringmap.StringMap.t ->
   Pitptree.pterm * Parsing_helper.extent ->
   Types.predicate * Types.enriched_term list]

   [check_fact env fact] converts the parsed fact [fact]
   into an enriched fact, represented by a predicate and
   a list of enriched terms (used for let ... suchthat).
*)

and check_fact env (fact, ext) = match fact with
  | PPIdent p ->
      (get_pred env p [],[])

  | PPTuple _ -> input_error "tuples not allowed here" ext
  | PPRestr _ | PPTest _ | PPLet _ | PPLetFilter _
  | PPEvent _ | PPInsert _ | PPGet _ ->
      input_error "new, if, let allowed in terms, but not at this position in conditions" ext
  | PPFunApp((f,fext) as p,l) ->
      (* FunApp: = and predicates allowed
         NOTE: in fact, t = true allows to encode any boolean term,
         should I rather allow any boolean term? *)

      match f, l with
        "=", [t1;t2] ->
          let t1' = check_et env t1
          and t2' = check_et env t2 in

          if t1'.et_type != t2'.et_type then
            input_error "the two arguments of an equality test should have the same type" ext;

          (equal_pred t1'.et_type, [t1'; t2'])

      | "=", _ -> internal_error ("Bad arity for special function " ^ f)
      | _ ->
          let tl = check_et_list env l in
          let type_l = List.map (fun t -> t.et_type) tl in
          let pred = get_pred env p type_l in
          (pred,tl)

(*** The second step is the expansion of enriched terms into terms/processes.
     This is implemented mainly by the function [expand_term]. *)

let add_cond_eval cond_eval t =
  match cond_eval with
  | FunApp(f,[]) when f == Terms.true_cst -> t
  | _ ->
      let ty = Terms.get_term_type t in
      let test_fun = Terms.gtest_fun ty in
      let caught_fail_cst = Terms.glet_constant_fun ty in
      FunApp(test_fun, [cond_eval; t; FunApp(caught_fail_cst,[])])

let rec put_lets cond_eval bound p =
  match bound with
  | [] -> p
  | (v,t) :: l ->
      put_lets cond_eval l
        (Terms.make_basic_let v (add_cond_eval cond_eval t) p)

let make_let_opt cond v t p =
  if cond then
    Terms.make_basic_let v t p
  else
    p

let check_no_ref ext vlist proc_layer =
  let proc_layer_Nil = proc_layer (fun _ -> Nil) in
  if List.exists (fun v -> Reduction_helper.occurs_var_proc v proc_layer_Nil) vlist then
    input_error "Cannot expand term because a variable in the expanded part would be referenced before being defined" ext

(* When the term is simple (contains only Var, FunApp, Restr, Test, Let)
   and Param.precise_let_expand is true,
   we make an optimized expansion that avoids introducing
   cases in which the adversary can distinguish the result of
   intermediate tests inside the term. That improves the precision
   for equivalence proofs. Test is expanded into a term,
   all Let inside the branches of Test actually done before the Test.

   In this case, [cond_eval] is a term of type bool, such that the value of [t]
   is useful only when [cond_eval] is true. When [cond_eval] is not true,
   we replace the subcomputations needed to compute [t] with
   [catch-fail]. That speeds up the subsequent translation into
   Horn clauses.

   Otherwise, [cond_eval] is not used.

   When the term contains only Var, FunApp, Restr, Test,
   the expansion is even simpler and expands Test into a term,
   without really using [cond_eval]. *)
let rec expand_term t =
  match t.et_desc with
  | ET_Var b ->
      (fun cond_eval proc_context -> proc_context (Var b))

  | ET_Restr(n,new_args,t) ->
      let proc_layer = expand_term t in
      let proc_layer_restr cond_eval proc_context =
        Restr(n, new_args, proc_layer cond_eval proc_context, Terms.new_occurrence())
      in
      proc_layer_restr

  | ET_FunApp(f,list_arg) ->
      let proc_layer_list = expand_term_list list_arg in
      let proc_layer cond_eval proc_context =
        proc_layer_list cond_eval (fun l ->
          match f.f_cat with
          | Tuple | Eq _ when List.exists Terms.is_failure l ->
              proc_context (Terms.get_fail_term (snd f.f_type))
          | _ -> proc_context (FunApp(f,l)))
      in
      proc_layer

  | ET_Test(cond,term_then,term_else) ->
      let proc_layer_cond = expand_term cond in
      let proc_layer_then = expand_term term_then in
      let proc_layer_else = expand_term term_else in

      let fail = Terms.get_fail_term term_then.et_type in
      if term_then.et_simple_no_let && term_else.et_simple_no_let then
        (* Case of terms containing only Var, FunApp, Restr, Test.
           Restr become processes and are moved before,
           all the rest is expanded as a term, using the if-then-else
           destructor for Test.
           [cond_eval] is not really used. *)
        let proc_layer cond_eval proc_context =
          proc_layer_cond cond_eval (fun c ->
            if Terms.is_failure c then
              proc_context fail
            else
              if !Param.expand_simplify_if_cst then
                begin
                  if Terms.equal_terms c Terms.true_term then
                    proc_layer_then cond_eval proc_context
                  else if Terms.equal_terms c Terms.false_term then
                    proc_layer_else cond_eval proc_context
                  else
                    proc_layer_then cond_eval (fun tthen ->
                      proc_layer_else cond_eval (fun telse ->
                        let gtest_symb = Terms.gtest_fun term_then.et_type in
                        proc_context (FunApp(gtest_symb, [c; tthen; telse]))
                          ))
                end
              else
                proc_layer_then cond_eval (fun tthen ->
                  proc_layer_else cond_eval (fun telse ->
                    let gtest_symb = Terms.gtest_fun term_then.et_type in
                    proc_context (FunApp(gtest_symb, [c; tthen; telse]))
                      ))
                  )
        in
        proc_layer
      else if (!Param.precise_let_expand) && term_then.et_simple && term_else.et_simple then
        (* Case of simple terms (containing only Var, FunApp, Restr, Test, Let).
           Restr and Let are moved ahead, as processes, but the lets are transformed
           so that they never fail. Test is expanded into a term.
           [cond_eval] is used to evaluate terms only when needed. *)
        let undo_catch_fail = Terms.undo_catch_fail_fun Param.bool_type in
        let proc_layer cond_eval proc_context =
          proc_layer_cond cond_eval (fun c ->
            if Terms.is_failure c then
              proc_context fail
            else
              (* [b] can take the values
                 - true: the condition [cond] is true, the then branch is executed
                 - catch-fail: the condition fails or
                   the term [if cond then ... else ...] is not evaluated,
                   nothing is executed
                 - other values: the condition [cond] is false, the else branch
                 is executed. *)
              let general_case () =
                let b = Terms.new_var_def Param.bool_type in
                let (not_f,b',c') =
                  if (Terms.term_never_fail c) && (match cond_eval with
                  | FunApp(f,[]) -> f == Terms.true_cst
                  | _ -> false) then
                    (* we are sure that c never fails, so c' = c
                       and that b = (add_cond_eval cond_eval c') is never caught_fail *)
                    Terms.not_fun(),Var b, c
                  else
                    (* we apply [catch_fail] to [c] even when [c] never fails,
                       so that [undo_catch_fail] does not generate comparisons between
                       [c] and [caught_fail] *)
                    let catch_fail = Terms.glet_fun (Terms.get_term_type c) in
                    Terms.is_false(),FunApp(undo_catch_fail, [Var b]), FunApp(catch_fail, [c])
                in
                Terms.make_basic_let b (add_cond_eval cond_eval c')
                  (proc_layer_then (Var b) (fun tthen ->
                    proc_layer_else (FunApp(not_f, [Var b])) (fun telse ->
                      let gtest_symb = Terms.gtest_fun term_then.et_type in
                      proc_context (FunApp(gtest_symb, [b'; tthen; telse])))))
              in

              if !Param.expand_simplify_if_cst
              then
                if Terms.equal_terms c Terms.true_term
                then proc_layer_then cond_eval proc_context
                else if Terms.equal_terms c Terms.false_term
                then proc_layer_else cond_eval proc_context
                else general_case ()
              else general_case ()
          )
        in
        proc_layer
      else
        (* General case, Test is expanded into a process *)
        let proc_layer cond_eval proc_context =
        proc_layer_cond Terms.true_term (fun c ->
          if Terms.term_never_fail c then
            if !Param.expand_simplify_if_cst then
              begin
                if Terms.equal_terms c Terms.true_term then
                  proc_layer_then Terms.true_term proc_context
                else if Terms.equal_terms c Terms.false_term then
                  proc_layer_else Terms.true_term proc_context
                else
                  Test(c, proc_layer_then Terms.true_term proc_context,
                       proc_layer_else Terms.true_term proc_context,
                       Terms.new_occurrence())
              end
            else
              Test(c, proc_layer_then Terms.true_term proc_context,
                   proc_layer_else Terms.true_term proc_context,
                   Terms.new_occurrence())
          else if Terms.is_failure c then
            (* When the condition fails, the whole test returns "fail" *)
            proc_context fail
          else
            match term_else.et_desc with
            | ET_FunApp(f,[]) when f.f_cat = Failure ->
                Let(PatEqual (Terms.true_term), c,
                    proc_layer_then Terms.true_term proc_context,
                    proc_context fail,
                    Terms.new_occurrence())
            | _ ->
                let b = Terms.new_var_def Param.bool_type in
                Let(PatVar b, c,
                    Test(Var b, proc_layer_then Terms.true_term proc_context,
                         proc_layer_else Terms.true_term proc_context,
                         Terms.new_occurrence()),
                    proc_context fail,
                    Terms.new_occurrence())
                  )
        in
        proc_layer

  | ET_Let(pat, term, term_then, term_else) ->
      let proc_layer_term = expand_term term in
      let proc_layer_then = expand_term term_then in

      if (!Param.precise_let_expand) && pat.ep_simple && term_then.et_simple && term_else.et_simple then
        (* Case of simple terms (containing only Var, FunApp, Restr, Test, Let).
           Restr and Let are moved ahead, as processes, but the lets are transformed
           so that they never fail. Test is expanded into a term.
           [cond_eval] is used to evaluate terms only when needed. *)
        begin
          match pat.ep_desc with
          | EP_PatVar v when et_term_never_fail term ->
           (* The "in" branch is always executed *)
             let proc_layer cond_eval proc_context  =
               proc_layer_term cond_eval (fun term_eval ->
                 Terms.make_basic_let v (add_cond_eval cond_eval term_eval)
                   (proc_layer_then cond_eval proc_context))
             in
             proc_layer

          | _ ->
              let proc_layer_pattern, v = expand_simple_pat pat in
              let proc_layer_else = expand_term term_else in

              let test_fun = Terms.gtest_fun term_then.et_type in

              let proc_layer cond_eval proc_context  =
                proc_layer_term cond_eval (fun term_eval ->
                  if Terms.is_failure term_eval then
                    (* The pattern is still evaluated when the term fails.
                       The pattern-matching always fails. *)
                    proc_layer_pattern (fun _ _ ->
                      proc_layer_else cond_eval proc_context)
                  else
                    let (make_test,term_eval') =
                      if (Terms.term_never_fail term_eval) && (match cond_eval with
                      | FunApp(f,[]) -> f == Terms.true_cst
                      | _ -> false) then
                        (* we are sure that term_eval never fails, so term_eval' = term_eval
                           and that v = (add_cond_eval cond_eval term_eval') is never caught_fail *)
                        (fun t->t), term_eval
                      else
                        (* we apply [catch_fail] to [term_eval] even when [term_eval] never fails,
                           so that [not_caught_fail_fun] does not generate comparisons between
                           [term_eval] and [caught_fail] *)
                        let v' = FunApp(Terms.not_caught_fail_fun term.et_type, [Var v]) in
                        let catch_fail = Terms.glet_fun term.et_type in
                        (fun t -> Terms.make_and v' t),FunApp(catch_fail, [term_eval])
                    in
                    Terms.make_basic_let v (add_cond_eval cond_eval term_eval')
                      (proc_layer_pattern (fun bound test ->
                        let test_v = Terms.new_var_def Param.bool_type in
                        Terms.make_basic_let test_v (make_test test)
                          (put_lets (Var test_v) bound
                             (proc_layer_then (Var test_v) (fun tthen ->
                            (* In the absence of let, [cond_eval] is not used, so
                               no need to bind [neg_test_v] when [term_else] contains
                               no let *)
                               let neg_test_v = Terms.new_var_def Param.bool_type in
                               make_let_opt (not term_else.et_simple_no_let) neg_test_v (Terms.make_and cond_eval (Terms.make_not (Var test_v)))
                                 (proc_layer_else (Var neg_test_v) (fun telse ->
                                   proc_context (FunApp(test_fun, [Var test_v; tthen; telse]))
                                     ))))))))
              in
              proc_layer
        end
      else
        (* General case. Let is expanded into a process that determines
           which branch is taken *)
        let proc_layer_pattern = expand_pattern pat in
        let proc_layer_else = expand_term term_else in
        let proc_layer cond_eval proc_context  =
          proc_layer_term Terms.true_term (fun term_eval ->
            if Terms.is_failure term_eval then
              (* The pattern is still evaluated when the term fails.
                 The pattern-matching always fails. *)
              proc_layer_pattern (fun _ ->
                proc_layer_else Terms.true_term proc_context)
            else
              proc_layer_pattern (fun pattern ->
                if (match pattern with PatVar _ -> true | _ -> false) &&
                  (Terms.term_never_fail term_eval) then
                  Let(pattern, term_eval,
                    proc_layer_then Terms.true_term proc_context,
                      Nil, Terms.new_occurrence())
                else
                  Let(pattern, term_eval,
                      proc_layer_then Terms.true_term proc_context,
                      proc_layer_else Terms.true_term proc_context,
                      Terms.new_occurrence())
                    ))
        in
        proc_layer

  | ET_LetFilter(vlist,p,tl,term_then,term_else) ->
      let layer_tl = expand_term_list tl in
      (* Verify that the expanded part of layer_tl does not reference
         the variables of vlist *)
      check_no_ref t.et_ext vlist (layer_tl Terms.true_term);

      let layer_then = expand_term term_then in
      let layer_else = expand_term term_else in

      (* LetFilter fails when a destructor in tl' fails *)
      let proc_layer cond_eval context =
        layer_tl Terms.true_term (fun tl' ->
          let rec collect_tests accu_tests = function
            | (Var v) as t1 -> t1
            | FunApp({ f_cat = Tuple | Eq _ | Name _ | Failure } as f,l) ->
                FunApp(f, List.map (collect_tests accu_tests) l)
            | t1 ->
                if List.exists (fun v -> Terms.occurs_var v t1) vlist then
                  input_error "Variables <vars> bound by \"let <vars> suchthat <fact>\" should only occur under constructors in <fact>" t.et_ext;
                if Terms.term_never_fail t1 then
                  t1
                else
                  let v = Terms.new_var_def (Terms.get_term_type t1) in
                  accu_tests := (v,t1) :: (!accu_tests);
                  Var v
          in
          let fail = Terms.get_fail_term term_then.et_type in
          if List.exists Terms.is_failure tl' then
            context fail
          else
            let accu_tests = ref [] in
            let tl'' = List.map (collect_tests accu_tests) tl' in
            let tfinal =
              LetFilter(vlist,Pred(p, tl''),
                        layer_then Terms.true_term context,
                        layer_else Terms.true_term context,
                        Terms.new_occurrence ())
            in
            match !accu_tests with
            | [] -> tfinal
            | [v,t] ->
                Let(PatVar v, t, tfinal,
                    context fail,
                    Terms.new_occurrence ())
            | l ->
                let tyl = List.map (fun (v,t) -> v.btype) l in
                let tuple_fun = Terms.get_tuple_fun tyl in
                let pat = PatTuple(tuple_fun, List.map (fun (v,t) -> PatVar v) l) in
                let term = FunApp(tuple_fun, List.map (fun (v,t) -> t) l) in
                Let(pat, term, tfinal,
                    context fail,
                    Terms.new_occurrence ())
                  )
      in
      proc_layer

  | ET_Event(t, env_args, term_cont) ->
      let layer_t = expand_event_insert_arg t in
      let proc_layer_cont = expand_term term_cont in
      let proc_layer cond_eval proc_context =
        layer_t (fun t' ->
          Event(t', env_args,
                proc_layer_cont Terms.true_term proc_context,
                Terms.new_occurrence()))
          (fun () -> proc_context (Terms.get_fail_term term_cont.et_type))
      in
      proc_layer

  | ET_Insert(t,term_cont) ->
     let layer_t = expand_event_insert_arg t in
     let proc_layer_cont = expand_term term_cont in
     let proc_layer cond_eval proc_context =
       layer_t (fun t' ->
         Insert(t', proc_layer_cont Terms.true_term proc_context,
                Terms.new_occurrence()))
         (fun () -> proc_context (Terms.get_fail_term term_cont.et_type))
     in
     proc_layer

  | ET_Get(pat,cond,term_then,term_else,precise) ->
      let layer_pat = expand_pattern pat in
      let layer_cond = expand_term cond in
      (* Verify that the expanded part of layer_cond does not reference
         the variables of bound in the patterns *)
      let vlist = ref [] in
      let _ = layer_pat (fun pat ->
        (* The goal of this function is to get all variables bound by the pattern
           by storing them in vlist *)
        vlist := Reduction_helper.get_pat_vars (!vlist) pat;
        Nil)
      in
      check_no_ref t.et_ext (!vlist) (layer_cond Terms.true_term);
      let proc_layer_then = expand_term term_then in
      let proc_layer_else = expand_term term_else in

      let proc_layer cond_eval proc_context =
        layer_pat (fun pat ->
          layer_cond Terms.true_term (fun cond ->
            Get(pat, cond,
                proc_layer_then Terms.true_term proc_context,
                proc_layer_else Terms.true_term proc_context, Terms.new_occurrence ~precise:precise ())
              )
            )
      in
      proc_layer

and expand_event_insert_arg t =
  (* When an argument of event or insert fails, the whole term fails.
     This function looks for arguments that may fail and handles them
     appropriately. *)
  match t.et_desc with
  | ET_FunApp(f,l) ->
      let proc_layer = expand_term_list l in
      let proc_layer' proc_context proc_fail =
        proc_layer Terms.true_term (fun l' ->
          let rec collect_tests accu_tests accu_l = function
              [] -> accu_tests, List.rev accu_l
            | (t::l) ->
                if Terms.term_never_fail t then
                  collect_tests accu_tests (t::accu_l) l
                else if Terms.is_failure t then
                  raise Not_found
                else
                  let v = Terms.new_var_def (Terms.get_term_type t) in
                  collect_tests ((v,t)::accu_tests) ((Var v)::accu_l) l
          in
          try
            let tests, l'' = collect_tests [] [] l' in
            let tfinal = proc_context (FunApp(f, l'')) in
            match tests with
            | [] -> tfinal
            | [v,t] ->
                Let(PatVar v, t, tfinal, proc_fail(), Terms.new_occurrence())
            | l ->
                let tyl = List.map (fun (v,t) -> v.btype) l in
                let tuple_fun = Terms.get_tuple_fun tyl in
                let pat = PatTuple(tuple_fun, List.map (fun (v,t) -> PatVar v) l) in
                let term = FunApp(tuple_fun, List.map (fun (v,t) -> t) l) in
                Let(pat, term, tfinal, proc_fail(), Terms.new_occurrence())
          with Not_found ->
            proc_fail())

      in
      proc_layer'
  | _ ->
      internal_error "argument of event or insert should be a function application"

and expand_term_list = function
  | [] ->
      (* It corresponds to when no term needs to be checked hence the context is in fact a process *)
      (fun cond_eval proc_context -> proc_context [])
  | term::q ->
      let proc_layer_q = expand_term_list q
      and proc_layer_t = expand_term term in

      let proc_layer_list cond_eval proc_context =
        proc_layer_t cond_eval (fun t ->
          proc_layer_q cond_eval (fun l -> proc_context (t::l))) in

      proc_layer_list

and expand_pattern pat =
  match pat.ep_desc with
  | EP_PatVar v ->
      let layer_proc context = context (PatVar v) in
      layer_proc

  | EP_PatEqual term ->
      let layer_proc_t = expand_term term in
      let layer_proc context =
        layer_proc_t Terms.true_term (fun t -> context (PatEqual t)) in
      layer_proc

  | EP_PatTuple(f,l) ->
      (* PatFunApp: only data constructors allowed,
         plus choice if !Param.allow_diff_patterns is true *)
      let layer_list = expand_pattern_list l in
      let layer_proc context =
        layer_list (fun l -> context (PatTuple(f,l))) in
      layer_proc

and expand_pattern_list = function
  | [] -> (fun context -> context [])
  | pat::pat_l ->
      let layer_proc_pat = expand_pattern pat in
      let layer_proc_pat_l = expand_pattern_list pat_l in
      let layer_proc context =
        layer_proc_pat (fun pattern ->
          layer_proc_pat_l (fun pattern_list ->
            context (pattern::pattern_list)
          )
        ) in
      layer_proc

and expand_simple_pat pat =

  match pat.ep_desc with
  | EP_PatVar v ->
      let layer_proc context =
        context [] Terms.true_term
      in
      (layer_proc, v)
  | _ ->

  let x = Terms.new_var_def pat.ep_type in
  let cond_eval = FunApp(Terms.not_caught_fail_fun pat.ep_type, [Var x]) in

  let rec sub_expand_pattern pattern =
    match pattern.ep_desc with
    | EP_PatVar v ->
        let layer_proc cor_term context =
          context [v, cor_term] Terms.true_term
        in
        layer_proc

    | EP_PatEqual term ->
        let layer_proc_t = expand_term term in
        let equal_symb = Terms.equal_no_fail_fun term.et_type in
        let layer_proc cor_term context =
          layer_proc_t cond_eval (fun t -> context [] (FunApp(equal_symb,[t;cor_term]))) in
        layer_proc

    | EP_PatTuple(f,l) ->
        (* PatTuple: only data constructors allowed,
           plus choice if !Param.allow_diff_patterns is true *)
        if l == [] then
          let equal_symb = Terms.equal_no_fail_fun (snd f.f_type) in
          let layer_proc cor_term context =
            context [] (FunApp(equal_symb,[FunApp(f,[]);cor_term]))
          in
          layer_proc
        else
          let layer_list = sub_expand_pattern_list l in
          let layer_proc cor_term context =
            let cor_term_list = List.map (fun f -> FunApp(f,[cor_term])) (Terms.get_all_projection_fun f) in
            layer_list cor_term_list
              (fun accu_bound -> fun test ->
                let fst_elt = List.hd cor_term_list
                and success_symb = Terms.success_fun ((List.hd l).ep_type) in
                let test_proper_tuple = FunApp(success_symb,[fst_elt]) in
                context accu_bound (Terms.make_and test test_proper_tuple)
                  )
          in
          layer_proc

  and sub_expand_pattern_list = function
    | [] -> (fun _ context -> context [] Terms.true_term)
    | pat::pat_l ->
       let layer_proc_pat = sub_expand_pattern pat in
       let layer_proc_pat_l = sub_expand_pattern_list pat_l in

       let layer_proc cor_term_list context =
          layer_proc_pat (List.hd cor_term_list)
            (fun accu_bound -> fun test ->
              layer_proc_pat_l (List.tl cor_term_list)
                (fun accu_bound' -> fun test' ->
                  context (accu_bound @ accu_bound') (Terms.make_and test test')
                    )
                )
       in
       layer_proc

  in

  let layer_proc = sub_expand_pattern pat in
  (layer_proc (Var x), x)

(*** Combine conversion of parsed term into enriched
     term and expansion into term and process *)

let check_term env t =
  let t' = check_et env t in
  (expand_term t' Terms.true_term, t'.et_type)

let check_term_list env tl =
  let tl' = check_et_list env tl in
  (expand_term_list tl' Terms.true_term, List.map (fun t -> t.et_type) tl')

let check_fact env f =
  let (p,tl) = check_fact env f in
  let proc_layer = expand_term_list tl in
  (fun proc_context ->
    proc_layer Terms.true_term (fun tl' -> proc_context (Pred(p, tl'))))

let check_get_cond env t =
  let t' = check_et env t in
  if not (ok_get_cond t') then
    input_error "new, insert, event, and let x1..xn suchthat with n>0 are not allowed in conditions of get" (snd t);
  (expand_term t' Terms.true_term, t'.et_type)


(*********************************************
              Checking Process
**********************************************)

let check_process env p =

  let barrier_tags = ref [] in

  let rec check_process cur_phase env (process, ext0) = match process with
  | PNil -> Nil
  | PPar(p1,p2) -> Par(check_process cur_phase env p1, check_process cur_phase env p2)
  | PRepl p -> Repl(check_process cur_phase env p, Terms.new_occurrence ())
  | PTest(cond,p1,p2) ->
      let layer_proc_cond, type_cond = check_term env cond in
      let p1' = check_process cur_phase env p1 in
      let p2' = check_process cur_phase env p2 in

      if type_cond != Param.bool_type then
        input_error "The condition on the test should be of type boolean" (snd cond);

      layer_proc_cond (fun t ->
        if Terms.is_failure t
        then Nil
        else if !Param.expand_simplify_if_cst then
          begin
            if Terms.equal_terms t Terms.true_term then
              p1'
            else if Terms.equal_terms t Terms.false_term then
              p2'
            else
              Test(t,p1', p2', Terms.new_occurrence ())
          end
        else
          Test(t,p1', p2', Terms.new_occurrence ())
      )

  | PLetDef((s,ext), args, explicit_barrier_prefix) ->
      let proc_layer_list, type_list = check_term_list env args in
      begin
        try
          match StringMap.find s env with
            EProcess(param, p', barrier_tags_callee) ->
              let p' = NamedProcess(s, (List.map (fun b -> Var b) param), p') in
              let ptype = List.map (fun b -> b.btype) param in
              if not (Terms.eq_lists ptype type_list) then
                input_error ("process " ^ s ^ " expects " ^
                             (args_to_string ptype) ^
                             " but is here given " ^
                             (args_to_string type_list)) ext;

              assert (!Terms.current_bound_vars == []);

              proc_layer_list (fun l ->
                if List.exists2 (fun t v ->
                  (not v.unfailing) && (Terms.is_failure t)
                    ) l param
                then Nil
                else
                  let lets = ref [] in
                  List.iter2 (fun t v ->
                  (* [keep_v] is true when a [let] must be introduced
                     because the variable [v] is used in queries *)
                    let keep_v = List.mem v.vname.orig_name (!ids_with_global_refs) in
                    if keep_v && v.unfailing then
                      input_error ("This process has a parameter " ^ v.vname.orig_name ^ " of type ... or fail; this argument cannot be used in query secret or in public_vars") ext;


                    if (Terms.is_var t) && (not keep_v) then
                      (* When [t] is a variable, avoid introducing a let, except when
                         we must keep the variable [v] *)
                      Terms.link v (TLink t)
                    else if (not v.unfailing) || (Terms.term_never_fail t) then
                      (* We can introduce a let without catch_fail.
                         [keep_v] is false, hence we can rename v. *)
                      let v' =
                        (* When [v] is not a may-fail variable, we just use [Terms.copy_var]
                           which keeps the original name of the variable [orig_name]
                           (important when [keep_v] is true).
                           When [v] is a may-fail variable, we cannot use [Terms.copy_var]
                           since [v'] should not be a may-fail variable; we use
                           [Terms.new_var]. The original name of the variable [orig_name]
                           is not preserved. That's ok because we know that [keep_v] is false
                           in this case. *)
                        if not v.unfailing
                        then Terms.copy_var v
                        else Terms.new_var v.vname.name v.btype
                      in
                      Terms.link v (TLink (Var v'));
                      lets := (v', t) ::(!lets)
                    else
                      (* The term may fail and we must evaluate the process with "fail" in this case,
                         we use catch-fail to be able to introduce a let *)
                      let catch_fail = Terms.glet_fun v.btype in
                      let undo_catch_fail = Terms.undo_catch_fail_fun v.btype in
                      let v' = Terms.new_var v.vname.name v.btype in
                      Terms.link v (TLink (FunApp(undo_catch_fail, [Var v'])));
                      lets := (v', FunApp(catch_fail, [t])) :: (!lets)
                                                                 ) l param;

                  let barrier_add_prefix =
                    match explicit_barrier_prefix with
                    | None -> (Terms.fresh_id "@")^"_"
                    | Some ("",_) -> ""
                    | Some (s,_) -> s^"_"
                  in
                  let p'' = Terms.put_lets (fun () -> Simplify.copy_process barrier_add_prefix p') (!lets) in
                  Terms.cleanup ();
                  barrier_tags :=
                     (List.map (fun (n,(s,ext)) -> (n,(barrier_add_prefix^s,ext))) barrier_tags_callee)
                     @ (!barrier_tags);
                  let min_phase = Reduction_helper.get_min_used_phase p'' in
                  if min_phase <= cur_phase then
                    input_error ("process " ^ s ^ " called in phase " ^
                                 (string_of_int cur_phase) ^ " and uses phase " ^
                                 (string_of_int min_phase) ^ ": phases should be in increasing order") ext;
                  p''
                    )
          | _ ->
              input_error (s ^ " should be a process") ext
        with Not_found ->
          input_error ("process " ^ s ^ " not defined") ext
      end

  | PRestr((s,ext),args,t,p) ->
      let ty = get_type t in
      if (StringMap.mem s env) then
        input_warning ("identifier " ^ s ^ " rebound") ext;
      if  ty == Param.nat_type || ty == Param.bool_type
      then input_error (Printf.sprintf "The name %s cannot be declared with the type '%s'" s ty.tname) ext;
      let r = Terms.create_name s (Param.tmp_type, ty) true in
      Database.record_name r;
      Restr(r, (get_restr_arg_opt env args, env), check_process cur_phase (StringMap.add s (EName r) env) p, Terms.new_occurrence())

  | PInput(ch_term,pat,p,opts) ->
      let precise = get_precise_option opts in
      let layer_channel, type_ch = check_term env ch_term in
      if type_ch != Param.channel_type then
        input_error ("this term has type " ^ type_ch.tname ^ " but should have type channel") (snd ch_term);
      let (pat', env') = check_ep dummy_ext env None pat env in
      let layer_pattern = expand_pattern pat' in
      let no_proc_layer_pat = var_fun_test_pat pat' in
      let p' = check_process cur_phase env' p in
      layer_channel (fun ch ->
        if Terms.is_failure ch then
          Nil
        else
          if no_proc_layer_pat then
            layer_pattern (fun pattern ->
              Input(ch, pattern, p', Terms.new_occurrence ~precise:precise ()))
          else
            let x = Terms.new_var_def pat'.ep_type in
            Input(ch, PatVar x,
                  layer_pattern (fun pattern ->
                    Let(pattern, Var x, p', Nil, Terms.new_occurrence ())),
                  Terms.new_occurrence ~precise:precise ())
      )

   | POutput(ch_term,term, p) ->
       let layer_channel, type_ch = check_term env ch_term in
       if type_ch != Param.channel_type then
        input_error ("this term has type " ^ type_ch.tname ^ " but should have type channel") (snd ch_term);
       let layer_term, ty_term = check_term env term in
       let p' = check_process cur_phase env p in
       layer_channel (fun ch ->
         layer_term (fun t ->
           (* The message is still evaluated when the channel fails *)
           if (Terms.is_failure ch) || (Terms.is_failure t) then
             Nil
           else
             Output(ch, t, p', Terms.new_occurrence ())
               )
           )

   | PLet(pat, t, pin, pelse) ->
       (* copy the code of [check_term] to get access to the extended
	  term [t'] *)
       let t' = check_et env t in
       let layer_term = expand_term t' Terms.true_term in
       let type_t = t'.et_type in

       let (pat', env') = check_ep dummy_ext env (Some type_t) pat env in
       let layer_pattern = expand_pattern pat' in
       begin
	 match pat'.ep_desc with
	 | EP_PatVar _ when fst pelse <> PNil && et_term_never_fail t' ->
	     input_error "the else branch of let should be omitted when it cannot be executed (the pattern is a variable and the assigned term cannot fail)" ext0
	 | _ -> ()
       end;
       let pin' = check_process cur_phase env' pin in
       let pelse' = check_process cur_phase env pelse in

       layer_term (fun term ->
         layer_pattern (fun pattern ->
           (* The pattern is still evaluated when the term fails *)
           if Terms.is_failure term
           then pelse'
           else
             if Terms.term_never_fail term && match pattern with PatVar _ -> true | _ -> false
             then Let(pattern, term, pin', Nil, Terms.new_occurrence ())
             else Let(pattern, term, pin', pelse', Terms.new_occurrence ())
                 )
           )

   | PLetFilter(identlist,(fact,ext),p,q,opts) ->
       let precise = get_precise_option opts in
       let (env', vlist) = List.fold_left (fun (env, vlist) ((s,e),t) ->
         if (StringMap.mem s env) then
           input_warning ("identifier " ^ s ^ " rebound") e;
         let ty = get_type t in
         let v = Terms.new_var s ty in
         (StringMap.add s (EVar v) env, v:: vlist)) (env,[]) identlist
       in

       let vlist = List.rev vlist in
       let layer_fact = check_fact env' (fact,ext) in
       (* Verify that the expanded part of layer_fact does not reference
          the variables of vlist *)
       check_no_ref ext vlist layer_fact;

       let p' = check_process cur_phase env' p in
       let q' = check_process cur_phase env' q in

       let rec check_term_vlist_only_under_constr vlist = function
         | Var _ -> ()
         | FunApp({ f_cat = Tuple | Eq _ | Name _ | Failure },l) ->
             List.iter (check_term_vlist_only_under_constr vlist) l
         | t ->
             if List.exists (fun v -> Terms.occurs_var v t) vlist then
               input_error "Variables <vars> bound by \"let <vars> suchthat <fact>\" should only occur under constructors in <fact>" ext
       in

       let check_fact_vlist_only_under_constr vlist (Pred(_,l)) =
         List.iter (check_term_vlist_only_under_constr vlist) l
       in

       layer_fact (fun fact' ->
         check_fact_vlist_only_under_constr vlist fact';
         LetFilter(vlist,fact', p', q', Terms.new_occurrence ~precise:precise ())
       )

   | PEvent(id,l,env_args,p) ->
       let layer_list,type_list = check_term_list env l in
       let env_args' = (get_restr_arg_opt env env_args, env) in
       let p' = check_process cur_phase env p in

       if !Param.key_compromise == 0 then
         let f = get_event_fun env id type_list in

         layer_list (fun l' ->
           if List.exists Terms.is_failure l' then
             Nil
           else
             Event(FunApp(f, l'), env_args', p', Terms.new_occurrence()))
       else
         let f = get_event_fun env id (Param.sid_type :: type_list) in

         layer_list (fun l' ->
           if List.exists Terms.is_failure l' then
             Nil
           else
             Event(FunApp(f, (Terms.new_var_def_term Param.sid_type) :: l'), env_args',
                   p',
                   Terms.new_occurrence()
                     )
         )

   | PInsert(id,l,p) ->
       let layer_list, type_list = check_term_list env l in

       let f = get_table_fun env id type_list in
       let p' = check_process cur_phase env p in

       layer_list (fun l' ->
         if List.exists Terms.is_failure l' then
           Nil
         else
           Insert(FunApp(f, l'), p', Terms.new_occurrence()))

   | PGet((i,ext),pat_list,cond_opt,p,elsep,opts) ->
       let precise = get_precise_option opts in
       begin try
         begin match StringMap.find i env with
           | ETable f ->
               (* By checking the terms in the patterns in the initial environment env,
                  we make sure that layer_pat cannot reference variables bound in the
                  patterns *)
               if List.length (fst f.f_type) != List.length pat_list then
                 input_error ("Table " ^ i ^ " expects " ^
                              (string_of_int (List.length (fst f.f_type))) ^
                              " argument(s) but is here given " ^
                              (string_of_int (List.length pat_list)) ^ " argument(s)") ext;

               let (pat_list', env') = check_ep_list ext env (List.map (fun t -> Some t) (fst f.f_type)) pat_list env in
               let layer_pat = expand_pattern_list pat_list' in

               let p' = check_process cur_phase env' p in
               let elsep' = check_process cur_phase env elsep in
               begin
                 match cond_opt with
                 | Some t ->
                     let (layer_cond,type_cond) = check_get_cond env' t in
                     if type_cond != Param.bool_type then
                       input_error ("this term has type " ^ type_cond.tname ^ " but should have type bool") (snd t);

                     (* Verify that the expanded part of layer_cond does not reference
                        the variables of bound in the patterns *)
                     let vlist = ref [] in
                     let _ = layer_pat (fun pat_list ->
                       (* The goal of this function is to get all variables bound by the pattern
                          by storing them in vlist *)
                       vlist := List.fold_left Reduction_helper.get_pat_vars (!vlist) pat_list;
                       Nil)
                     in
                     check_no_ref (snd t) (!vlist) layer_cond;

                     layer_pat (fun pat_list ->
                       layer_cond (fun cond ->
                         Get(PatTuple(f,pat_list), cond, p', elsep', Terms.new_occurrence ~precise:precise ())
                       )
                     )
                  | None ->
                      layer_pat (fun pat_list ->
                        Get(PatTuple(f, pat_list), Terms.true_term, p', elsep', Terms.new_occurrence ~precise:precise ())
                      )
               end
           | _ -> input_error (i ^ " should be a table") ext
         end
       with Not_found ->
         input_error ("table " ^ i ^ " not defined") ext
       end

   | PPhase(n,p) ->
       if cur_phase >= n then
         input_error "phases should be in increasing order" ext0;
       Phase(n, check_process n env p, Terms.new_occurrence())

   | PBarrier(n,tag, p) ->
       let tag' =
         match tag with
           None -> (Terms.fresh_id "@", Parsing_helper.dummy_ext)
         | Some orig_tag -> orig_tag
       in
       barrier_tags := (n, tag') :: (!barrier_tags);
       Barrier(n, tag', check_process cur_phase env p, Terms.new_occurrence())

  in
  let p' = check_process 0 env p in
  (p', !barrier_tags)

(*********************************************
               Other Checking
**********************************************)

(* Macro expansion *)

let macrotable = ref StringMap.empty

let rename_table = ref StringMap.empty

let expansion_number = ref 0

let rename_ident i =
  match i with
    "=" | "<>" | "not" | "&&" | "||" | "event" | "inj-event" | "==>" | "choice" | ">" | ">=" | "<=" | "<" -> i
  | _ -> if i.[0] = '!' || i.[0] = '-' then i else
  try
    StringMap.find i (!rename_table)
  with Not_found ->
    let r = "@" ^ (string_of_int (!expansion_number)) ^ "_" ^ i in
    rename_table := StringMap.add i r (!rename_table);
    r

let rename_ie (i,ext) = (rename_ident i, ext)

let rename_ie_opt = function
  | None -> None
  | Some id -> Some (rename_ie id)

let rec rename_term (t,ext) =
  let t' = match t with
  | PFail -> PFail
  | PIdent i -> PIdent (rename_ie i)
  | PFunApp(f,l) -> PFunApp(rename_ie f, List.map rename_term l)
  | PTuple l -> PTuple(List.map rename_term l)
  | PProj _ -> input_error "projections not allowed here" ext
  in
  (t',ext)

let rec rename_format = function
    PFIdent i -> PFIdent (rename_ie i)
  | PFFunApp(f,l) -> PFFunApp(rename_ie f, List.map rename_format l)
  | PFTuple l -> PFTuple(List.map rename_format l)
  | PFName _ -> internal_error "Names not allowed in formats with -in pi"
  | PFAny i -> PFAny (rename_ie i)

let rename_format_fact (i,l) = (rename_ie i, List.map rename_format l)

let rec rename_gformat (t,ext) =
  let t' = match t with
    PFGIdent i -> PFGIdent (rename_ie i)
  | PFGFunApp(f,l) -> PFGFunApp(rename_ie f, List.map rename_gformat l)
  | PFGTuple l -> PFGTuple(List.map rename_gformat l)
  | PFGName(i,l) ->  PFGName(rename_ie i, List.map (fun (i,t) -> (rename_ie i, rename_gformat t)) l)
  | PFGAny i -> PFGAny (rename_ie i)
  | PFGLet(i,t,t') -> PFGLet(rename_ie i, rename_gformat t, rename_gformat t')
  in
  (t',ext)

let rec rename_nounif = function
    BFLet(i,f,t) -> BFLet(rename_ie i, rename_gformat f, rename_nounif t)
  | BFNoUnif((i,l,n')) -> BFNoUnif((rename_ie i, List.map rename_gformat l, n'))

let rec rename_gterm (t,ext) =
  let t' = match t with
    PGIdent i -> PGIdent (rename_ie i)
  | PGFunApp(f,l,at_op) -> PGFunApp(rename_ie f, List.map rename_gterm l,rename_ie_opt at_op)
  | PGPhase(i,l,n,at_op) -> PGPhase(rename_ie i, List.map rename_gterm l, n, rename_ie_opt at_op)
  | PGTuple l -> PGTuple(List.map rename_gterm l)
  | PGName(i,l) -> PGName(rename_ie i, List.map (fun (i,t) -> (rename_ie i, rename_gterm t)) l)
  | PGLet(i,t,t') -> PGLet(rename_ie i, rename_gterm t, rename_gterm t')
  in
  (t',ext)

let rename_query = function
    PPutBegin(b,l), ext -> PPutBegin(b, List.map rename_ie l), ext
  | PRealQuery (t,l), ext -> PRealQuery(rename_gterm t, List.map rename_ie l), ext
  | PQSecret(v,l,opt), ext -> PQSecret(rename_ie v, List.map rename_ie l, opt), ext

let rename_lemma (t,opt_ror,pubvars) =
  let opt_ror' = match opt_ror with
    | None -> None
    | Some (x,opt) -> Some (rename_ie x, opt)
  in
  (rename_gterm t, opt_ror', List.map rename_ie pubvars)

let rename_clause = function
    PClause(t,t') -> PClause(rename_term t, rename_term t')
  | PFact t -> PFact(rename_term t)
  | PEquiv(t,t',b) -> PEquiv(rename_term t, rename_term t', b)

let rec rename_pterm (t,ext) =
  let t' = match t with
    PPIdent i -> PPIdent (rename_ie i)
  | PPFunApp(f,l) -> PPFunApp(rename_ie f, List.map rename_pterm l)
  | PPTuple(l) -> PPTuple(List.map rename_pterm l)
  | PPRestr(i,args,ty,t) ->
      let args' =
        match args with
          None -> None
        | Some l-> Some (List.map rename_ie l)
      in
      PPRestr(rename_ie i, args', rename_ie ty, rename_pterm t)
  | PPTest(t1,t2,t3opt) -> PPTest(rename_pterm t1, rename_pterm t2, rename_pterm_opt t3opt)
  | PPLet(pat, t1, t2, t3opt) -> PPLet(rename_pat pat, rename_pterm t1, rename_pterm t2, rename_pterm_opt t3opt)
  | PPLetFilter(l, t1, t2, t3opt) -> PPLetFilter(List.map(fun (i,ty) -> (rename_ie i, rename_ie ty)) l, rename_pterm t1, rename_pterm t2, rename_pterm_opt t3opt)
  | PPEvent(i,l,lidopt,t) ->
      PPEvent(rename_ie i, List.map rename_pterm l,
              (match lidopt with
                None -> None
              | Some lid -> Some (List.map rename_ie lid)),
              rename_pterm t)
  | PPInsert(i,l,t) ->
      PPInsert(rename_ie i, List.map rename_pterm l, rename_pterm t)
  | PPGet(i,lpat,topt,t1,t2opt,opts) ->
      PPGet(rename_ie i, List.map rename_pat lpat, rename_pterm_opt topt,
            rename_pterm t1, rename_pterm_opt t2opt, opts)
  in
  (t',ext)

and rename_pterm_opt = function
    None -> None
  | Some t3 -> Some (rename_pterm t3)

and rename_pat = function
    PPatVar(i,tyopt) -> PPatVar(rename_ie i, rename_ie_opt tyopt)
  | PPatAny(e,tyopt) -> PPatAny(e,rename_ie_opt tyopt)
  | PPatTuple l -> PPatTuple(List.map rename_pat l)
  | PPatFunApp(f,l) -> PPatFunApp(rename_ie f, List.map rename_pat l)
  | PPatChoice(f,l,tyopt) -> PPatChoice(f, List.map rename_pat l, rename_ie_opt tyopt)
  | PPatEqual t -> PPatEqual (rename_pterm t)

let rename_barrier_prefix barrier_prefix =
  match barrier_prefix with
  | None | Some("",_) -> barrier_prefix
  | Some id -> Some (rename_ie id)

let rec rename_process (process, ext0) =
  let process' = match process with
    PNil -> PNil
  | PPar(p1,p2) -> PPar(rename_process p1, rename_process p2)
  | PRepl(p) -> PRepl(rename_process p)
  | PRestr(i,args,ty,p) ->
      let args' =
        match args with
          None -> None
        | Some l -> Some (List.map rename_ie l)
      in
      PRestr(rename_ie i, args', rename_ie ty, rename_process p)
  | PLetDef(i,l,barrier_prefix) -> PLetDef(rename_ie i, List.map rename_pterm l, rename_barrier_prefix barrier_prefix)
  | PTest(t,p1,p2) -> PTest(rename_pterm t, rename_process p1, rename_process p2)
  | PInput(t,pat,p,opts) -> PInput(rename_pterm t, rename_pat pat, rename_process p,opts)
  | POutput(t1,t2,p) -> POutput(rename_pterm t1, rename_pterm t2, rename_process p)
  | PLet(pat, t, p1, p2) -> PLet(rename_pat pat, rename_pterm t, rename_process p1, rename_process p2)
  | PLetFilter(l, t, p1, p2,opts) -> PLetFilter(List.map (fun (i,ty) -> (rename_ie i, rename_ie ty)) l, rename_pterm t, rename_process p1, rename_process p2,opts)
  | PEvent(i,l,env_args,p) ->
      let env_args' =
        match env_args with
          None -> None
        | Some l -> Some (List.map rename_ie l)
      in
      PEvent(rename_ie i ,List.map rename_pterm l, env_args', rename_process p)
  | PInsert(i,l,p) -> PInsert(rename_ie i ,List.map rename_pterm l, rename_process p)
  | PGet(i,patl,topt,p,elsep,opts) -> PGet(rename_ie i ,List.map rename_pat patl, rename_pterm_opt topt, rename_process p, rename_process elsep,opts)
  | PPhase(n,p) -> PPhase(n, rename_process p)
  | PBarrier(n,tag,p) -> PBarrier(n, tag, rename_process p)
  in
  (process', ext0)

let rename_env env = List.map (fun (i,ty) -> (rename_ie i, rename_ie ty)) env

let rename_may_fail_env env = List.map (fun (i,ty,can_fail) -> (rename_ie i, rename_ie ty, can_fail)) env

let rec rename_side_condition side_c = match side_c with
        |[] -> []
        |(env,t1,t2)::q -> (rename_env env, rename_term t1, rename_term t2)::(rename_side_condition q)

let rec rename_extended_equation = function
  | EELet(i,t,eq) -> EELet(rename_ie i,rename_term t, rename_extended_equation eq)
  | EETerm t -> EETerm (rename_term t)

let rename_decl = function
    TTypeDecl i -> TTypeDecl (rename_ie i)
  | TFunDecl(i,l,ty,opt) -> TFunDecl(rename_ie i, List.map rename_ie l, rename_ie ty, opt)
  | TEventDecl(i,l) -> TEventDecl(rename_ie i, List.map rename_ie l)
  | TTableDecl(i,l) -> TTableDecl(rename_ie i, List.map rename_ie l)
  | TConstDecl(i,ty,opt) -> TConstDecl(rename_ie i, rename_ie ty, opt)
  | TReduc(l,opt) -> TReduc(List.map (fun (env,t) -> (rename_env env,rename_extended_equation t)) l, opt)
  | TReducFail(f, ty_arg,ty_res,l,opt) -> TReducFail(rename_ie f, List.map rename_ie ty_arg, rename_ie ty_res, List.map (fun (env,t) -> (rename_may_fail_env env,rename_extended_equation t)) l, opt)
  | TEquation(l, eqinfo) -> TEquation(List.map (fun (env, t1) -> (rename_env env, rename_extended_equation t1)) l, eqinfo)
  | TPredDecl(i,l,opt) -> TPredDecl(rename_ie i, List.map rename_ie l, opt)
  | TSet ((_,ext),_) ->
      input_error "set is not allowed inside macro definitions" ext
  | TPDef(i,env,p) -> TPDef(rename_ie i, rename_may_fail_env env, rename_process p)
  | TQuery(env, l,opt) -> TQuery(rename_env env, List.map rename_query l,opt)
  | TLemma(b,env,l,opt) -> TLemma(b,rename_env env, List.map rename_lemma l,opt)
  | TNoninterf(env, l) -> TNoninterf(rename_env env, List.map (fun (i,tlopt) ->
      (rename_ie i, match tlopt with
        None -> None
      | Some tl -> Some (List.map rename_term tl))) l)
  | TWeaksecret i -> TWeaksecret (rename_ie i)
  | TNoUnif(env, nounif,nounif_value,opt) -> TNoUnif(rename_env env, rename_nounif nounif,nounif_value,opt)
  | TNot(env, t) -> TNot(rename_env env, rename_gterm t)
  | TElimtrue(env, f) -> TElimtrue(rename_may_fail_env env, rename_term f)
  | TFree(i,ty, opt) -> TFree(rename_ie i, rename_ie ty, opt)
  | TClauses l -> TClauses (List.map (fun (env, cl) -> (rename_may_fail_env env, rename_clause cl)) l)
  | TDefine((s1,ext1),argl,def) ->
      input_error "macro definitions are not allowed inside macro definitions" ext1
  | TExpand(s1,argl) ->
      TExpand(s1, List.map rename_ie argl)
  | TLetFun(i,env,t) -> TLetFun(rename_ie i, rename_may_fail_env env, rename_pterm t)

let apply argl paraml already_def def =
  rename_table := StringMap.empty;
  incr expansion_number;
  List.iter (fun s ->
    rename_table := StringMap.add s s (!rename_table)) already_def;
  List.iter2 (fun (a,_) (p,_) ->
    rename_table := StringMap.add p a (!rename_table)) argl paraml;
  let def' = List.map rename_decl def in
  rename_table := StringMap.empty;
  def'


let declares = function
    TTypeDecl(i)
  | TFunDecl(i,_,_,_)
  | TConstDecl(i,_,_)
  | TReducFail(i,_,_,_,_)
  | TPredDecl (i,_,_)
  | TEventDecl (i,_)
  | TTableDecl (i,_)
  | TFree(i,_,_)
  | TPDef (i, _, _)
  | TLetFun(i,_,_) ->
      Some i
  | TReduc((_,t)::_,_) ->
      let i = get_top_symbol_reduc t in
      Some i
  | _ -> None

(* [add_already_def expanded_macro already_def] adds to [already_def]
   the identifiers defined in [expanded_macro].
   Since we use @ in identifiers in the expanded macro, we do not
   need to restrict ourselves to identifiers that appear in arguments. *)

let rec add_already_def expanded_macro already_def =
  List.fold_left (fun already_def a ->
    match declares a with
    | Some (s,_) -> s::already_def
    | None -> already_def
          ) already_def expanded_macro


let rec check_no_dup = function
    [] -> ()
  | (arg,ext)::l ->
      List.iter (fun (arg',ext') ->
        if arg = arg' then
          input_error ("Macro contains twice the argument " ^ arg) ext'
            ) l;
      check_no_dup l

type macro_elem =
    Macro of Pitptree.ident list * Pitptree.tdecl list * string list * macro_elem Stringmap.StringMap.t

let rec expand_macros macro_table already_def = function
    [] -> []
  | a::l ->
      match a with
      | TDefine((s1,ext1),argl,def) ->
          if StringMap.mem s1 macro_table then
            input_error ("Macro " ^ s1 ^ " already defined.") ext1
          else
            check_no_dup argl;
            let macro_table' = StringMap.add s1 (Macro(argl, def, already_def, macro_table)) macro_table in
            expand_macros macro_table' already_def l
      | TExpand((s1,ext1),argl) ->
          begin
            try
              let Macro(paraml, def, old_already_def, old_macro_table) = StringMap.find s1 macro_table in
              if List.length argl != List.length paraml then
                input_error ("Macro " ^ s1 ^ " expects " ^ (string_of_int (List.length paraml)) ^
                             " arguments, but is here given " ^ (string_of_int (List.length argl)) ^ " arguments.") ext1;
              let applied_macro = apply argl paraml old_already_def def in
              let expanded_macro = expand_macros old_macro_table old_already_def applied_macro in
              let already_def_after_macro = add_already_def expanded_macro already_def in
              expanded_macro @ (expand_macros macro_table already_def_after_macro l)
            with Not_found ->
              input_error ("Macro " ^ s1 ^ " not defined.") ext1
          end
      | _ ->
          let already_def' =
            match declares a with
              Some(s,_) -> s::already_def
            | None -> already_def
          in
          a::(expand_macros macro_table already_def' l)

(* Fix query options: there is a shift/reduce conflict in the parsing
of query options:
query ... secret x ... [options_secret] [options_query]
where both [options_secret] and [options_query] are optional.
As a consequence, when only one set of options is present,
the parser assumes that it is [options_secret].
This function fixes the parsing in case these options are actually
[options_query].
*)

let is_query_option ((id, ext), args) =
  (args = None) && List.mem id ["maxSubset"; "proveAll"; "noneSat"; "noneVerif"; "discardSat"; "discardVerif"; "fullSat"; "fullVerif"; "instantiateSat"; "instantiateVerif"; "induction"; "noInduction"; "keep" ]

let fix_query_options (env, q, opt) =
  if opt = [] then
    let rec aux = function
      | [PQSecret(sec_var, pub_vars, options), ext] as q ->
          if List.for_all is_query_option options then
            [PQSecret(sec_var, pub_vars, []), ext], options
          else
            q, []
      | q1::qrest ->
          let qrest', opt' = aux qrest in
          q1::qrest', opt'
      | [] -> [], []
    in
    let q', opt' = aux q in
    env, q', opt'
  else
    env, q, opt

(* Handle all declarations *)

let rec check_one = function
    TTypeDecl(i) -> check_type_decl i
  | TFunDecl(f,argt,rest,i) -> check_fun_decl f argt rest (no_param_option_list i)
  | TConstDecl(f,rest,i) -> check_fun_decl f [] rest (no_param_option_list i)
  | TEquation(l,eqinfo) -> check_equations l (no_param_option_list eqinfo)
  | TReduc (r,i) -> check_red r (no_param_option_list i)
  | TReducFail (f,ty_arg,ty_res,r,i) -> check_red_may_fail f ty_arg ty_res r (no_param_option_list i)
  | TPredDecl (p, argt, info) -> check_pred p argt (no_param_option_list info)
  | TEventDecl(i, args) -> check_event i args
  | TTableDecl(i, args) -> check_table i args
  | TPDef ((s,ext), args, p) ->
      check_no_def s ext;
      let env = ref (!global_env) in
      let arglist = List.map (fun ((s',ext'),ty,may_fail) ->
        let t = get_type ty in
        begin
          try
            match StringMap.find s' (!env) with
              EVar _ -> input_error ("variable " ^ s' ^ " already defined") ext'
            | _ -> ()
          with Not_found ->
            ()
        end;
        let v = Terms.new_var ~may_fail:may_fail s' t in
        env := StringMap.add s' (EVar v) (!env);
        v
               ) args
      in
      let (p', barrier_tags) = check_process (!env) p in
      global_env := StringMap.add s (EProcess(arglist, p', barrier_tags)) (!global_env)
  | TQuery (env,q,opt) ->
      let (env,q,opt) = fix_query_options (env,q,opt) in
      query_list := (QueryToTranslate(transl_query (env, q,(no_param_option_list opt)))) :: (!query_list);
      corresp_query_list := (env,q) :: (!corresp_query_list)
  | TLemma(b,env,q,opt) ->
      lemma_list := (LemmaToTranslate(transl_lemma b (env,q,(no_param_option_list opt)))):: !lemma_list;
      let q' = List.map (fun (t,_,pubvars) -> (PRealQuery(t,pubvars), snd t)) q in
      corresp_query_list := (env,q') :: (!corresp_query_list)
  | TNoninterf (env, lnoninterf) ->
      let non_interf_query = List.map (get_non_interf env) lnoninterf in
      query_list := (NonInterfQuery non_interf_query) :: (!query_list);
  | TWeaksecret i ->
      let w = get_non_interf_name (!global_env) i in
      query_list := (WeakSecret w) :: (!query_list)
  | TNoUnif (env, nounif,nounif_value,opt) -> nounif_list := (env,nounif,nounif_value,opt) :: !nounif_list
  | TElimtrue(env, fact) ->
      let env = create_may_fail_env env in
      elimtrue := (check_simple_fact env fact) :: (!elimtrue)
  | TNot (env, no) ->
      not_list := (env, no) :: (!not_list)
  | TFree (name,ty,i) ->
      add_free_name name ty (no_param_option_list i)
  | TClauses c ->
      List.iter check_clause c
  | TLetFun ((s,ext), args, p) ->
      check_no_def s ext;

      let env = ref (!global_env) in

      let arg_list = List.map (fun ((s',ext'),ty,may_fail) ->
        let t = get_type ty in
        begin
          try
            match StringMap.find s' (!env) with
              EVar _ -> input_error ("variable " ^ s' ^ " already defined") ext'
              | _ -> ()
          with Not_found ->
            ()
        end;

        let v = Terms.new_var ~may_fail:may_fail s' t in
        env := StringMap.add s' (EVar v) (!env);
        v
          ) args in

      let type_arg_list = List.map (fun v -> v.btype) arg_list in

      let result = check_et (!env) p in
      let type_result = result.et_type in

      let func_proc_layer list_term_arg =
        let lets = ref [] in
        List.iter2 (fun v term ->
          if (not v.unfailing) || (et_term_never_fail term) then
            if et_is_var term then
              v.link <- ETLink term
            else
              let v' = Terms.new_var v.vname.name v.btype in
              v.link <- ETLink (make_et dummy_ext (ET_Var v'));
              lets := (v', term) ::(!lets)
          else
              (* The term may fail and we must evaluate the letfun with "fail" in this case,
                 we use catch-fail to be able to introduce a let *)
            let catch_fail = Terms.glet_fun v.btype in
            let undo_catch_fail = Terms.undo_catch_fail_fun v.btype in
            let v' = Terms.new_var v.vname.name v.btype in
            v.link <- ETLink (make_et dummy_ext (ET_FunApp(undo_catch_fail, [make_et dummy_ext (ET_Var v')])));
            lets := (v', make_et dummy_ext (ET_FunApp(catch_fail, [term]))) :: (!lets)
                 ) arg_list list_term_arg;

        put_et_lets
          { (copy_et result) with et_type = type_result }
          (!lets)
           (* Changing the type is useful in case types are ignored and
              the last function of the letfun is a type converter *)
      in

      global_env := StringMap.add s (ELetFun(func_proc_layer, type_arg_list, type_result)) (!global_env)

  | TDefine _ | TExpand _ ->
      internal_error "macros should have been expanded"

  | TSet _ -> internal_error "set declaration should have been handled before"

(* Maximum phase for queries, not, nounif *)

let max_phase_event max_phase_process (f,e) =
  match f with
  | PGPhase((s, ext), tl, n,_) ->
      begin
        match s with
          "mess" | "attacker" | "table" ->
            if n > max_phase_process then
              input_warning "phase greater than the maximum phase used in the process.\nIs that really what you want?" e;
            n
        | _ -> input_error "phases can be used only with attacker, mess, or table" ext
      end
  | _ -> 0

let rec max_phase_query max_phase_process = function
  | PGFunApp((("==>" | "||" | "&&"), _), [he1;he2],_), _ ->
      max (max_phase_query max_phase_process he1)
        (max_phase_query max_phase_process he2)
  | PGLet(id,t,t'), _ ->
      max_phase_query max_phase_process t'
  | ev ->
      max_phase_event max_phase_process ev

let max_phase_corresp_secret_putbegin_query max_phase_process = function
  | PRealQuery (q, _) ->
      max_phase_query max_phase_process q
  | PQSecret _ | PPutBegin _ -> 0

let max_phase_format max_phase_process ((s, ext), _, n) =
  match s with
    "attacker" | "mess" | "table" ->
      if n > max_phase_process then
        input_warning "nounif declaration for a phase greater than used" ext;
      n
  | s ->
      if n <> -1 then
        input_error "declared predicates do not depend on phases, so no phase should be specified in such facts in queries" ext;
      0

let rec max_phase_nounif max_phase_process = function
    BFLet(_,_,nounif) -> max_phase_nounif max_phase_process nounif
  | BFNoUnif fact -> max_phase_format max_phase_process fact

(* Reset the local state of this module *)

let reset() =
  equations := [];
  destructors_check_deterministic := [];
  ids_with_global_refs := [];
  corresp_query_list := [];
  query_list := [];
  not_list := [];
  input_clauses := [];
  elimtrue := [];
  equiv_list := [];
  nounif_list := [];
  lemma_list := [];
  global_env := StringMap.empty;
  macrotable := StringMap.empty;
  rename_table := StringMap.empty;
  expansion_number := 0


let interpret_setting (p,ext) v =
  match (p,v) with
    "attacker", S ("passive",_) -> Param.active_attacker := false
  | "attacker", S ("active",_) -> Param.active_attacker := true
  | "preciseActions", (S ("no",_) | S ("false",_)) ->
      Param.precise_actions := NotPrecise
  | "preciseActions", (S ("yes",_) | S ("true",_)) ->
      Param.precise_actions := Precise
  | "preciseActions", (S ("yesWithoutArgsInNames",_) | S ("trueWithoutArgsInNames",_)) ->
      Param.precise_actions := PreciseWithoutArgsInNames
  | "allowDiffPatterns", _ -> Param.boolean_param Param.allow_diff_patterns p ext v
  | "privateCommOnPublicTerms", _ -> Param.boolean_param Param.allow_private_comm_on_public_terms p ext v
  | "keyCompromise", S ("strict",_) -> Param.key_compromise := 2
  | "keyCompromise", S ("approx",_) -> Param.key_compromise := 1
  | "keyCompromise", S ("none",_) -> Param.key_compromise := 0
  | "movenew", _ -> Param.boolean_param Param.move_new p ext v
  | "movelet", _ -> Param.boolean_param Param.move_let p ext v
  | "inductionLemmas", _ -> Param.boolean_param Param.induction_lemmas p ext v
  | "inductionQueries", _ -> Param.boolean_param Param.induction_queries p ext v
  | "verboseLemmas", _ -> Param.boolean_param Param.verbose_lemmas p ext v
  | "verboseDestructors", _ -> Param.boolean_param Param.verbose_destr p ext v
  | "nounifIgnoreAFewTimes", S ("none",_) -> Param.nounif_ignore_once:= Param.NIO_None
  | "nounifIgnoreAFewTimes", S ("all",_) -> Param.nounif_ignore_once:= Param.NIO_All
  | "nounifIgnoreAFewTimes", S ("auto",_) -> Param.nounif_ignore_once:= Param.NIO_Auto
  | "nounifIgnoreNtimes", I n ->
      if n < 1
      then Parsing_helper.input_error "The setting nounifIgnoreNtimes must be set with an integer greater or equal to 1." ext;
      Param.initial_nb_of_nounif_ignore := n
  | "removeEventsForLemma", _ -> Param.boolean_param Param.event_lemma_simplification p ext v
  | "saturationApplication", S ("none",_) -> Param.sat_application:= LANone
  | "saturationApplication", S ("full",_) -> Param.sat_application:= LAFull
  | "saturationApplication", S ("discard",_) -> Param.sat_application:= LAOnlyWhenRemove
  | "saturationApplication", S ("instantiate",_) -> Param.sat_application:= LAOnlyWhenInstantiate
  | "verificationApplication", S ("none",_) -> Param.verif_application:= LANone
  | "verificationApplication", S ("full",_) -> Param.verif_application:= LAFull
  | "verificationApplication", S ("discard",_) -> Param.verif_application:= LAOnlyWhenRemove
  | "verificationApplication", S ("instantiate",_) -> Param.verif_application:= LAOnlyWhenInstantiate
  | "verboseClauses", S ("explained",_) -> Param.verbose_explain_clauses := Param.ExplainedClauses
  | "verboseClauses", S ("short",_) -> Param.verbose_explain_clauses := Param.Clauses
  | "verboseClauses", S ("none",_) -> Param.verbose_explain_clauses := Param.NoClauses
  | "explainDerivation", _ -> Param.boolean_param Param.explain_derivation p ext v
  | "removeUselessClausesBeforeDisplay", _ -> Param.boolean_param Param.remove_subsumed_clauses_before_display p ext v
  | "predicatesImplementable", S("check",_) -> Param.check_pred_calls := true
  | "predicatesImplementable", S("nocheck",_) -> Param.check_pred_calls := false
  | "eqInNames", _ -> Param.boolean_param Param.eq_in_names p ext v
  | "reconstructTrace", I n ->
      if n < 0 then
        Parsing_helper.input_error "Value of reconstructTrace should be a positive integer or zero, yes, true, no, false" ext;
      Param.reconstruct_trace := n
  | "reconstructTrace", (S ("no",_) | S ("false",_)) ->
      Param.reconstruct_trace := 0
  | "reconstructTrace", (S ("yes",_) | S ("true",_)) ->
      Param.reconstruct_trace := -1
  | "traceBacktracking", _ -> Param.boolean_param Param.trace_backtracking p ext v
  | "unifyDerivation", _ -> Param.boolean_param Param.unify_derivation p ext v
  | "traceDisplay", S ("none",_) -> Param.trace_display := Param.NoDisplay
  | "traceDisplay", S ("short",_) -> Param.trace_display := Param.ShortDisplay
  | "traceDisplay", S ("long",_) -> Param.trace_display := Param.LongDisplay
  | "ignoreTypes", S (("all" | "true" | "yes"), _) -> Param.set_ignore_types true
  | "ignoreTypes", S (("none" | "attacker" | "false" | "no"), _) -> Param.set_ignore_types false
  | "simplifyProcess", S (("true" | "yes"), _) -> Param.simplify_process := 1
  | "simplifyProcess", S (("false" | "no"), _) -> Param.simplify_process := 0
  | "simplifyProcess", S ("interactive", _) -> Param.simplify_process := 2
  | "rejectChoiceTrueFalse", _ -> Param.boolean_param Param.reject_choice_true_false p ext v
  | "rejectNoSimplif", _ -> Param.boolean_param Param.reject_no_simplif p ext v
  | "expandIfTermsToTerms", _ -> input_warning "Setting expandIfTermsToTerms is deprecated" ext
  | "preciseLetExpand", _ -> Param.boolean_param Param.precise_let_expand p ext v
  | "expandSimplifyIfCst", _ -> Param.boolean_param Param.expand_simplify_if_cst p ext v
  | "interactiveSwapping", _ -> Param.boolean_param Param.interactive_swapping p ext v
  | "swapping", S sext -> Param.set_swapping := Some sext
  | "proveLemmaOnly", _ -> Param.boolean_param Param.prove_lemma_only p ext v
  | _,_ -> Param.common_parameters p ext v


(* Final parsing function *)

let parse_file s =
  (* Reinitialize the state *)
  Param.reset_param();
  Display.init_used_ids();
  reset();
  let (decl, proc, second_proc) = parse_with_lib s in
  (* ignoreTypes must be set before doing the rest of the work
     Setting all parameters beforehand does not hurt.
     Furthermore, we record identifiers that we want to keep unchanged *)
  List.iter (fun ((p,ext),v) -> interpret_setting (p,ext) v) (!Param.additional_settings);
  List.iter (function
    | TSet((p,ext),v) -> interpret_setting (p,ext) v
    | _ -> ()
              ) decl;
  Param.default_set_ignore_types();
  initialize_env();
  List.iter (function one_decl ->
    match declares one_decl with
    | Some (s,ext) -> Display.record_id s ext
    | None -> ()
            ) decl;

  (* Expand macros [def] / [expand] *)
  let already_def = StringMap.fold (fun s _ already_def -> s :: already_def) (!global_env) [] in
  let decl = expand_macros StringMap.empty already_def decl in

  (* Set [ids_with_global_refs] to make sure that
     we keep them when we expand processes and [letfun] *)
  List.iter (get_ids_with_global_refs_decl ids_with_global_refs) decl;

  (* *)

  List.iter (function
      TSet _ -> ()
    | x -> check_one x) decl;

  let (p, barrier_tags) = Terms.auto_cleanup (fun () ->
    check_process (!global_env) proc)
  in

  let second_p = match second_proc with
    | None -> None
    | Some(proc2) ->
        (* Barriers are not allowed when proving the equivalence of 2 processes,
           so we can ignore barrier_tags returned by check_process here *)
        let (p2,_) = Terms.auto_cleanup (fun () ->
          check_process (!global_env) proc2)
        in
        if (!Param.key_compromise != 0) then
          Parsing_helper.user_error "Key compromise is incompatible with equivalence";
        Some p2
  in

  (* Compute process_query *)
  let process_query = match second_p with
    | Some p2 ->
        if !Param.has_choice then
          Parsing_helper.user_error "Equivalence is incompatible with choice";
        if (!query_list) != [] then
          Parsing_helper.user_error "Queries are incompatible with equivalence";
        Equivalence({ proc = p; bi_pro = false; display_num = None; construction = Initial_process1 },
                    { proc = p2; bi_pro = false; display_num = None; construction = Initial_process2 })
    | None ->
        if !Param.has_choice then
          begin
            if (!query_list) != [] then
              Parsing_helper.user_error "Queries are incompatible with choice";
            SingleProcessSingleQuery({ proc = p; bi_pro = true; display_num = None; construction = Initial_process }, ChoiceQuery)
          end
        else
          SingleProcess({ proc = p; bi_pro = false; display_num = None; construction = Initial_process }, List.rev (!query_list))
  in

  (* Compute maximum phase *)
  let max_phase_process =
    if !Param.key_compromise = 2 then
      1
    else
      max (Reduction_helper.get_max_used_phase p)
        (match second_p with
          None -> 0
        | Some p2 -> Reduction_helper.get_max_used_phase p2)
  in
  let max_phase =
    List.fold_left (fun accu (env, ql) ->
      List.fold_left (fun accu (q,_) ->
        max accu (max_phase_corresp_secret_putbegin_query max_phase_process q)
          ) accu ql
        ) max_phase_process (!corresp_query_list)
  in
  let max_phase =
    List.fold_left (fun accu (env, no_decl) ->
      max accu (max_phase_event max_phase_process no_decl)
        ) max_phase (!not_list)
  in
  let max_phase =
    List.fold_left (fun accu (env, nounif,_,_) ->
      max accu (max_phase_nounif max_phase_process nounif)
        ) max_phase (!nounif_list)
  in

  let pi_state =
    { pi_process_query = process_query;
      pi_global_env = Set (!global_env);
      pi_glob_table = Unset;
      pi_glob_table_var_name = Unset;
      pi_types = StringMap.fold (fun _ v accu ->
               match v with
               | EType t -> t::accu
               | _ -> accu) (!global_env) [];
      pi_funs = StringMap.fold (fun _ v accu ->
               match v with
               | EFun f -> f::accu
               | _ -> accu) (!global_env) [];
      pi_freenames = StringMap.fold (fun _ v accu ->
               match v with
               | EName n -> n::accu
               | _ -> accu) (!global_env) [];
      pi_events = StringMap.fold (fun _ v accu ->
               match v with
               | EEvent e -> e::accu
               | _ -> accu) (!global_env) [];
      pi_equations = !equations;
      pi_max_used_phase = max_phase;
      pi_all_barrier_tags = barrier_tags;
      pi_input_clauses = !input_clauses;
      pi_elimtrue = !elimtrue;
      pi_equivalence_clauses = !equiv_list;
      pi_destructors_check_deterministic = !destructors_check_deterministic;
      pi_disequations = !disequations;
      pi_event_status_table = Unset;
      pi_get_not = get_not (!not_list);
      pi_get_nounif = get_nounif (!nounif_list);
      pi_terms_to_add_in_name_params = Unset;
      pi_min_choice_phase = Unset;
      pi_need_vars_in_names = Function (get_need_vars_in_names (!corresp_query_list) (!not_list) (!nounif_list));
      pi_name_args_exact = true;
      pi_lemma = List.rev !lemma_list;
      pi_original_axioms = [];
      pi_precise_actions = [];
      pi_originally_lemma = false
    }
  in
  reset();
  pi_state
