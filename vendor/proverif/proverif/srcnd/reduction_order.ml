(* Trace reconstruction 
   This version of the trace reconstruction algorithm takes into
   account the order of nodes in the derivation tree, in order
   to speed up the reconstruction. It may fail more often in
   the presence of synchronous outputs on private channels.
*)
(* TO DO Implement phases *)

open Types
open Pitypes
open Terms
open Reduction_helper

let double_check = ref false
let debug_find_io_rule = ref false
let debug_print s = ()
   (* print_string s; print_newline()  *)

type info = 
    ReplInfo of funsymb list (* List of already used session identifiers *)
  | Nothing

type sub_proc =
    process * (term list) * (hypspec list) * (fact list) * info
      (* process (always closed -- only bound variables can occur; no variable with link *)
      (* list of name_params (terms received as input + session ids), always closed -- no variables *)
      (* list of occurrences of inputs and replications already seen in the reduction *)
      (* list of facts corresponding to already seen inputs -- no variables *)
      (* cached info for inputs *)

type reduc_type =
  | RNil of int
  | RPar of int 
  | RRepl of int * int
  | RRestr of int * funsymb * funsymb
  | RLet1 of int * pattern * term 
  | RLet2 of int * pattern * term
  | RInput of int * term * pattern * term
  | ROutput1 of int * term * term 
  | RTest1 of int * term * term 
  | RTest2 of int * term * term
  | RBegin1 of int * term
  | REnd of int * term
  | RPhase of int
  | RLetFilter1 of int * binder list * fact 
  | RLetFilter3 of int * binder list * fact 
  | RIO of int * term * pattern * int * term * term
  | RIO2 of int * term * pattern * int * term * term
  | RInit

type action =
    OutputAction of (term list) * (hypspec list) * (fact list) * fact
  | IOAction of (term list) * (hypspec list) * (fact list) * fact

type reduc_state = 
    { 
      goal : fact; (* goal to reach *)
      subprocess : sub_proc list; (* process list *)
      public : term list; (* attacker knowledge *)

      current_node : fact_tree;
      father_node : fact_tree;
      expect_redIO : fact_tree;

      previous_state : reduc_state option; (* previous semantic state *)
   
      executed_actions : action list;

      hyp_not_matched : fact list;
      attacker_pred : predicate;
      mess_pred : predicate;
      current_phase : int;
      min_current_node : int; (* Minimum and maximum indexes of processes that may correspond
	                         to the current node of the derivation *)
      max_current_node : int;
      comment : reduc_type  (* type of the reduction *)
    }

let dummy_node = { desc = FRemoved; thefact = Pred(Param.bad_pred, []) }

exception No_result
(* We use the exception Unify for local failure *)

(* Display the trace *)

let order_of_int n = 
  (string_of_int (n+1)) ^ 
  (
  if (n>=10) && (n<14) then "th" else
  match (n+1) mod 10 with
  | 1 -> "st"
  | 2 -> "nd"
  | 3 -> "rd"
  | _ -> "th")

let rec itern f n = function
    [] -> ()
  | (a::l) -> 
      if n > 0 then 
	begin
	  f a;  
	  itern f (n-1) l
	end

let display_init_state = ref true

let rec display_reduc_state display_state state =
  if (not (!display_init_state)) && (state.previous_state = None) then
    (* Do not display the initial state; used when the 
       beginning of the trace has already been displayed *)
    List.length state.public
  else
  let display_next_state =
    match state.comment with
    | RInput _ | RIO _ | RIO2 _ | RPhase _ -> true
    | _ -> false
  in
  let display_cur_state = display_state ||
    match state.comment with
    | RIO _ | RIO2 _ | RPhase _ -> true
    | _ -> state.previous_state = None
  in
  let old_size_public = 
    match state.previous_state with
      Some s -> display_reduc_state display_next_state s
    | None -> 0
  in
  begin
    match state.comment with
    | RNil(n) -> print_string ((order_of_int n) ^" process: Reduction 0")
    | RPar(n) -> print_string ((order_of_int n) ^" process: Reduction |")
    | RRepl(n, cpn) -> print_string ((order_of_int n) ^" process: Reduction ! "^(string_of_int cpn)^" copy(ies)")
    | RRestr(n, na, n') -> print_string ((order_of_int n) ^" process: New " ^ na.f_name ^ " creating " ^ n'.f_name)
    | RLet1(n, pat, t) ->
	print_string ((order_of_int n) ^" process: Let ");
	Display.display_pattern pat;
	print_string " = ";
	Display.display_term2 t;
	print_string " succeeds"
    | RLet2(n, pat, t) -> 
	print_string ((order_of_int n) ^" process: Let ");
	Display.display_pattern pat;
	print_string " = ";
	Display.display_term2 t;
	print_string " fails"
    | RInput(n, tc, pat, mess_term) ->
	print_string ((order_of_int n) ^" process: In(");
	Display.display_term2 tc;
	print_string ", ";
	Display.display_pattern pat;
	print_string ") done with message ";
	Display.display_term2 mess_term
    | ROutput1(n, tc, t) ->
	print_string ((order_of_int n) ^" process: Out(");
	Display.display_term2 tc;
	print_string ", ";
	Display.display_term2 t;
	print_string ") done"
    | RTest1(n, t1, t2) ->
	print_string ((order_of_int n) ^" process: If ");
	Display.display_term2 t1;
	print_string " = ";
	Display.display_term2 t2;
	print_string " succeeds"
    | RTest2(n, t1, t2) ->
	print_string ((order_of_int n) ^" process: If ");
	Display.display_term2 t1;
	print_string " = ";
	Display.display_term2 t2;
	print_string " fails"
    | RBegin1(n, t) ->
	print_string ((order_of_int n) ^" process: Event(");
	Display.display_term2 t;
	print_string ") executed"
    | REnd(n, t) ->
	print_string ((order_of_int n) ^" process: Event(");
	Display.display_term2 t;
	print_string ") is the goal"
    | RPhase(n) ->
	print_string ("Switching to phase " ^ (string_of_int n))
    | RLetFilter1(n, bl, f)  ->
        print_string ((order_of_int n) ^" process: let ");
	let first = ref true in
	List.iter (fun b -> 
	  if !first then 
	    first := false
	  else
	    print_string ", ";
	  print_string (b.sname ^ "_" ^ (string_of_int b.vname))
	    ) bl;
	print_string " suchthat ";
	Display.display_fact2 f;
	print_string " executed"
    | RLetFilter3(n, bl, f)  ->
        print_string ((order_of_int n) ^" process: let ");
	let first = ref true in
	List.iter (fun b -> 
	  if !first then 
	    first := false
	  else
	    print_string ", ";
	  print_string (b.sname ^ "_" ^ (string_of_int b.vname))
	    ) bl;
	print_string " suchthat ";
	Display.display_fact2 f;
	print_string ": let...suchthat fails"
    | RIO(ninput, tc', pat, n, tc, t) ->
        print_string ((order_of_int ninput) ^" process: In(");
	Display.display_term2 tc';
	print_string ", ";
	Display.display_pattern pat;
	print_string ") reduces with ";
        print_string ((order_of_int n) ^" process: out(");
	Display.display_term2 tc;
	print_string ", ";
	Display.display_term2 t;
	print_string ")"
    | RIO2(ninput, tc', pat, n, tc, t) ->
        print_string ((order_of_int ninput) ^" process: In(");
	Display.display_term2 tc';
	print_string ", ";
	Display.display_pattern pat;
	print_string ") reduces with ";
        print_string ((order_of_int n) ^" process: out(");
	Display.display_term2 tc;
	print_string ", ";
	Display.display_term2 t;
	print_string ") but input fails"
    | RInit -> print_string "Initial state"
  end;
  print_newline ();
  print_newline ();
  let size_public = List.length state.public in
  if size_public > old_size_public then
    begin
	print_endline "Additional knowledge of the attacker:";
	itern (fun x -> 
	  print_string "      ";
	  Display.display_term2 x;
	  print_string "\n") (size_public - old_size_public) state.public;
	print_endline "";
	print_endline "--------------------------------------------------------------"
    end;
  if display_cur_state then
    begin
	print_endline "New processes:";
	let n = ref 0 in
	List.iter (fun (proc, _,_,_,_) -> 
	  if !n > 0 then print_endline "|";
	  Display.display_process "      " proc;
	  print_newline ();
	  incr n) state.subprocess;
	print_endline "--------------------------------------------------------------"
    end;
  size_public

let rec display_labeled_trace state =
  if (!display_init_state) || (state.previous_state != None) then
    (* Do not display the initial state when the 
       beginning of the trace has already been displayed *)
    begin
      begin
	match state.previous_state with
	  Some s -> display_labeled_trace s
	| None -> ()
      end;
      begin
	match state.comment with
	  RInput(n, tc, pat, mess_term) ->
	    print_string "in(";
	    Display.display_term2 tc;
	    print_string ", ";
	    Display.display_term2 mess_term;
	    print_string ")\n\n"
	| ROutput1(n, tc, t) ->
	    print_string "out(";
	    Display.display_term2 tc;
	    print_string ", ";
	    Display.display_term2 t;
	    print_string ")\n\n"
	| RBegin1(n, t) | REnd(n,t) ->
	    print_string "event(";
	    Display.display_term2 t;
	    print_string ")\n\n"
	| _ -> ()
      end
    end

let display_trace final_state =
  match !Param.trace_display with
    Param.NoDisplay -> ()
  | Param.ShortDisplay ->   
      if !display_init_state then
	begin
	  print_string "A more detailed output of the traces is available with\n";
	  print_string "  param traceDisplay = long.\n";
	  print_endline "Goal of the attack :";
	  Termslinks.display_fact_with_links final_state.goal;
	  print_endline "";
	  print_newline()
	end;
      display_labeled_trace final_state
  | Param.LongDisplay -> 
      if !display_init_state then
	begin
	  print_endline "Goal of the attack :";
	  Termslinks.display_fact_with_links final_state.goal;
	  print_endline ""
	end;
      ignore (display_reduc_state true final_state)

(* Find a clause *)

let rec skip n l = 
  if n = 0 then l else
  match l with
    [] -> Parsing_helper.internal_error "skip"
  | (_::l) -> skip (n-1) l

let rec truncate n l =
  if n = 0 then [] else
  match l with
    [] -> Parsing_helper.internal_error "skip"
  | (a::l) -> a::(truncate (n-1) l)

exception Found of term list (*local to find_io_rule *)

let find_io_rule hypspeclist hyplist name_params var_list current_node =
  let l = List.length hypspeclist in
  let lnp = List.length name_params in
  let lh = List.length hyplist in
  (* Useful for debugging *)
  (*  begin
      auto_cleanup (fun () ->
	print_string "Process ";
	display_tag hypspeclist name_params;
	print_string "  ";
	Display.display_list Termslinks.display_fact_with_links " & " hyplist;
	print_newline())
    end; *)
  match current_node.desc with
    FRule(_,ProcessRule(hypspeclist2, name_params2), _, sons2) ->
      let sons = List.map (fun t -> t.thefact) sons2 in
      (* auto_cleanup (fun () ->
	print_string "Looking for ";
	display_tag hypspeclist2 name_params2;
	print_string "  ";
	Display.display_list Termslinks.display_fact_with_links " & " sons;
	print_newline()); *)
      let l2 = List.length hypspeclist2 in
      let lnp2 = List.length name_params2 in
      let lh2 = List.length sons in
      if (l2 < l) || (lnp2 < lnp) || (lh2 < lh)
        || (not (hypspeclist = skip (l2-l) hypspeclist2)) then
	raise Unify
      else
        begin
	  let sons3 = skip (lh2-lh) sons in
	  try 
	    auto_cleanup (fun () ->
	      match_modulo_list (fun () ->
	        match_equiv_list (fun () -> 
                  raise (Found (List.map copy_closed_remove_syntactic var_list))
	            ) sons3 hyplist 
                  ) name_params (skip (lnp2-lnp) name_params2)
		)
          with Found tl -> tl
        end
  | _ -> Parsing_helper.internal_error "Current node should have a process rule in find_io_rule" 

(* let find_io_rule = Profile.f5 "find_io_rule" find_io_rule *)

(* Evaluate a term possibly containing destructors
   Raises Unify when the term evaluation fails.
   The function next_f may raise No_result when it finds no result.
   In this case, term_evaluation also raises No_result *)

let rec term_evaluation next_f = function
    Var v -> 
      begin
        match v.link with
          TLink t -> term_evaluation next_f t
        | _ -> Parsing_helper.internal_error "Error: term should be closed in attack reconstruction";
      end
  | FunApp(f,l) ->
      (* for speed, use the initial definition of destructors, not the one enriched with the equational theory *)
      match f.f_initial_cat with
	Eq _ | Tuple -> term_evaluation_list (fun l' -> next_f (FunApp(f,l'))) l
      | Name _ -> next_f (FunApp(f,[]))
      | Red redl -> term_evaluation_list (fun l' ->
	  let evaluation_succeeds = ref false in
	  let rec try_red_list = function
	      [] -> 
		if !evaluation_succeeds then
		  raise No_result
		else
		  raise Unify
	    | (red1::redl) ->
		let (left, right) = auto_cleanup (fun () -> Terms.copy_red red1) in
		try 
		  auto_cleanup (fun () ->
		  match_modulo_list (fun () -> 
		    try
		      (* TO DO (for speed) should I remove_syntactic, or keep it,
			 but take it into account elsewhere (when doing
			 function symbol comparisons, accept functions that
			 differ by their syntactic status) *)
 		      next_f (let t = TermsEq.remove_syntactic_term right in
		              close_term t; 
		              t)
		    with No_result ->
			evaluation_succeeds := true;
			raise Unify
				    ) left l')
		with Unify -> try_red_list redl
	  in
	  try_red_list redl
	  ) l
      | _ -> Parsing_helper.internal_error "unexpected function symbol in term_evaluation"

and term_evaluation_list next_f = function
    [] -> next_f []
  | (a::l) -> 
      term_evaluation_list (fun l' -> 
	term_evaluation (fun a' ->
	  next_f (a'::l')
	) a
      ) l

(*
Note: it is important that nothing is added in name_params for constructors 
with an equational theory. Indeed, these constructors are substituted during the
evaluation of the process, so the result of check_several_types would not be
the same in pitransl and in reduction, leading to different values of name_params,
so errors
*)

let rec check_several_types = function
    Var { link = TLink t } -> check_several_types t
  | Var _ -> false
  | FunApp(f,l) ->
      (List.exists check_several_types l) || 
      (match f.f_initial_cat with
       	 Red rules -> List.length rules > 1
       | Eq rules -> 
	   if !Param.eq_in_names then
	     Parsing_helper.internal_error "Setting eqInNames should have disabled trace reconstruction";
	   false
       | _ -> false)

let term_evaluation_name_params next_f t hypspeclist hyplist name_params current_node =
  let may_have_several_types = check_several_types t in
  term_evaluation (fun t' ->
    if may_have_several_types then
      (* We check that a clause in io_rule justifies our choice when adding 
         elements to name_params -> This makes it possible to detect wrong 
         choices very quickly and avoid losing too much time in backtracking. *)
      let _ = find_io_rule hypspeclist hyplist (t'::name_params) [] current_node in
      next_f t' (t' :: name_params)
    else
      next_f t' name_params
    ) t

let rec term_evaluation_letfilter next_f = function
    Var { link = TLink t } -> term_evaluation_letfilter next_f t
  | Var v ->  next_f (Var v)
  | FunApp(f,l) ->
      match f.f_cat with
	Eq _ | Tuple -> term_evaluation_list_letfilter (fun l' -> next_f (FunApp(f,l'))) l
      | Name _ -> next_f (FunApp(f,[]))
      | Red redl -> term_evaluation next_f (FunApp(f,l))
      | _ -> Parsing_helper.internal_error "unexpected function symbol in term_evaluation_letfilter"

and term_evaluation_list_letfilter next_f = function
    [] -> next_f []
  | (a::l) -> 
      term_evaluation_list_letfilter (fun l' -> 
	term_evaluation_letfilter (fun a' -> next_f (a'::l')) a
      ) l

let term_evaluation_letfilter next_f l name_params =
  let may_have_several_types = List.exists check_several_types l in
  term_evaluation_list_letfilter (fun l' ->
    if may_have_several_types then
      (* The fact that the newly added name_params are justified by a clause
	 in the derivation tree will be checked in next_f, when looking
         for the result of letfilter *)
      next_f l' (l' @ name_params)
    else
      next_f l' name_params
    ) l

(* Match a pattern
   Raises Unify when the matching fails *)

let rec match_pattern next_f p t = match p with
  PatVar b -> Terms.link b (TLink t); next_f ()
| PatTuple(f,l) ->
    let vl = Terms.var_gen (List.length l) in
    match_modulo (fun () ->
	 let tl = List.map copy_closed_remove_syntactic vl in
         match_pattern_list next_f l tl
      ) (FunApp(f, vl)) t
| PatEqual t' ->
      term_evaluation (fun t'' ->
	match_modulo (fun () -> ()) t'' t
	) t';
      next_f ()

and match_pattern_list next_f pl tl = match (pl, tl) with
  [],[] -> next_f ()
| (p1::pl,t1::tl) ->
     match_pattern (fun () ->
        match_pattern_list next_f pl tl) p1 t1
| _ -> Parsing_helper.internal_error "Different length in match_pattern_list"

let rec update_name_params name_params = function
  PatVar b -> (copy_closed_remove_syntactic (Var b))::name_params
| PatTuple(f,l) -> update_name_params_list name_params l
| PatEqual _ -> name_params

and update_name_params_list name_params = function
  [] -> name_params
| (a::l) -> update_name_params (update_name_params_list name_params l) a


(* Test if a term is public *)

let rec is_in_public public = function
    FunApp({ f_cat = Tuple }, l) -> List.for_all (is_in_public public) l
  | t -> List.exists (equal_terms_modulo t) public

let channel_public public t =
  (List.mem t (!public_free)) || (is_in_public public t)

let rec add_in_public public = function
    FunApp({ f_cat = Tuple }, l) -> add_in_public_list public l
  | t ->  t::public

and add_in_public_list public = function
    [] -> public
  | (a::l) -> add_in_public_list (add_in_public public a) l

let rec add_public state t = 
  { state with public = add_in_public state.public t }

(* Apply an attacker rule *)
(* next_f takes as input the new state *)

let do_attacker_rule next_f prev_state =
  match prev_state.current_node with
    { desc = FRule(_, Apply(symb,_), _, sons); thefact = Pred(p,[t]) } ->
      begin
      match symb with
	Func(f) when f.f_cat != Tuple ->
	if p == prev_state.attacker_pred then
	  begin
	    (* Optionally check that the hypotheses are public *)
	    if !double_check then
	      begin
		List.iter (fun son ->
		  match son.thefact with
		    Pred(_,[t]) ->
		      if not (is_in_public prev_state.public t) then
			begin
			  print_string "Hypothesis = ";
			  Display.display_term t;
			  Parsing_helper.internal_error "Hypothesis should be public"
			end
		  | _ -> Parsing_helper.internal_error "Hypothesis should be attacker fact") sons
	      end;
            next_f (add_public prev_state t)
	  end
        else
	  begin
	    debug_print "Bad phase";
	    raise No_result (* Bad phase; cannot apply the rule *)
	  end
      |	_ -> (* Tuple function or projection *)
        next_f prev_state (* No change in public although the node has been executed correctly *)
      end
  | { desc = FRule(_, Rn, _, sons); thefact = Pred(p,[t]) } ->
      if p == prev_state.attacker_pred then
        next_f (add_public prev_state t)
      else
	begin
	  debug_print "Bad phase";
          raise No_result (* Bad phase; cannot apply the rule *)
	end
  | _ -> 
      Parsing_helper.internal_error "Expecting attacker rule at this node"

(* Do reductions that do not involve interactions *)
(* When the goal is reached, returns the final state.
   Otherwise, raises an exception No_result. *)

let rec replace_at n a' = function
  [] -> Parsing_helper.internal_error "replace_at"
| (a::l) -> if n = 0 then a'::l else a::(replace_at (n-1) a' l)

let rec remove_at n = function
   [] -> Parsing_helper.internal_error "remove_at"
| (a::l) -> if n = 0 then l else a::(remove_at (n-1) l)
 
let rec add_at n a' l = 
  if n = 0 then a' :: l else 
  match l with
    [] -> Parsing_helper.internal_error "add_at"
  | (a::l) -> a::(add_at (n-1) a' l)

let rec do_nil_par_restr prev_state n =
  let (proc, name_params, occs, facts, cache_info) =
	 List.nth prev_state.subprocess n in
  match proc with
    Nil -> debug_print "Doing Nil";
       { prev_state with 
         subprocess = remove_at n prev_state.subprocess;
         comment = RNil(n);
         max_current_node = prev_state.max_current_node - 1;
         previous_state = Some prev_state }
  | Par(p,q) -> 
      debug_print "Doing Par";
      do_nil_par_restr
        (do_nil_par_restr
          { prev_state with
	    subprocess = add_at n (p, name_params, occs, facts, Nothing)
	                (replace_at n (q, name_params, occs, facts, Nothing) 
                         prev_state.subprocess);
            comment = RPar(n);
            max_current_node = prev_state.max_current_node + 1;
            previous_state = Some prev_state } (n+1)) n
  | Restr(na,p) ->
      debug_print "Doing Restr";
      let nt = FunApp(na, name_params) in
      let n' = add_name_for_pat nt in
      let p' = process_subst p na n' in
      begin
	do_nil_par_restr { prev_state with
	    subprocess = replace_at n (p', name_params, occs, facts, Nothing) prev_state.subprocess;
            comment = RRestr(n, na, n');
            previous_state = Some prev_state } n
      end
  | _ -> prev_state

let rec find_occ (proc, name_params, occs, facts, cache_info) = 
  (match proc with
    Nil | Par _ | Restr _ -> Parsing_helper.internal_error "Nil, Par, Restr should have been reduced"
  | Let(pat,t,p,q,occ) -> LetTag occ
  | Test(t1,t2,p,q,occ) -> TestTag occ
  | Output(tc,t,p,occ) -> OutputTag occ
  | Event(FunApp(fs,l),p,occ) -> BeginEvent (occ)
  | LetFilter(bl, pr, p, q, occ) -> LetFilterTag occ
  | Repl(p,occ) -> ReplTag (occ, List.length name_params)
  | Input(tc,pat,p,occ) -> InputTag occ
  | Phase(n,p) -> LetTag (-1) (* return a non-existent tag *)) :: occs

let rec find_proc_for_current_node n current_node = function
    [] -> raise Not_found
  | ((proc, name_params, occs, facts, cache_info) as sub_proc)::l -> 
      let new_occs = find_occ sub_proc in
      match cache_info with
	Nothing ->
	  begin
	    try
              let _ = find_io_rule new_occs facts name_params [] current_node in
	      (n,sub_proc)
	    with Unify ->
              find_proc_for_current_node (n+1) current_node l
	  end
      | ReplInfo l_sid ->
	  begin
	    (* TO DO this assumes no non-interference and no key compromise
	       (which is coherent with the current usage of this module)
	       With key compromise, we may need two session ids.
               With non-interference, we need to add the session ids in inputs and input_facts *)
	    let sid = Terms.new_var "sid" in
	    try
	      match find_io_rule new_occs facts ((Var sid)::name_params) [Var sid] current_node with
		[FunApp(f,[])] ->
		  if List.memq f l_sid then
		    raise Unify (* Must not reuse the same session id *)
		  else
		    (n,sub_proc)
	      |	_ -> Parsing_helper.internal_error "find_proc_for_current_node, Repl case, reduction.ml"
		
	    with Unify ->
	      find_proc_for_current_node (n+1) current_node l
	  end

(* let find_proc_for_current_node = Profile.f3 "find_proc_for_current_node" find_proc_for_current_node *)

let match_action father node action = (* In action, all facts should be mess facts (no attacker facts) *)
  match action with
    OutputAction(name_params', hypspec', facts', fact') ->
      begin
	match node.desc with
	  FRule(_, ProcessRule(hypspec, name_params), _, sons) ->
	    (hypspec = hypspec') && 
	    (try
      	      auto_cleanup (fun () ->
		match_modulo_list (fun () ->
		  match_equiv_list (fun () -> ()) (node.thefact::(List.map (fun son -> son.thefact) sons)) (fact'::facts')
		    ) name_params name_params'
		  );
		true
	    with Unify -> false)
        | _ -> false
      end    
  | IOAction(name_params', hypspec', facts', fact') ->
      begin
	match father.desc with
	  FRule(_, ProcessRule(hypspec, name_params), _, sons) ->
	    (* hypspec', name_params', fact'::facts' should be suffixes of 
	       hypspec, name_params, List.map (fun son -> son.thefact) sons *)
	    let facts = List.map (fun t -> t.thefact) sons in
	    let l = List.length hypspec in
	    let lnp = List.length name_params in
	    let lh = List.length facts in
	    let l' = List.length hypspec' in
	    let lnp' = List.length name_params' in
	    let lh' = 1 + List.length facts' in
	    if (l' > l) || (lnp' > lnp) || (lh' > lh) ||
	      (List.nth sons (lh-lh') != node) ||
              (not (hypspec' = skip (l-l') hypspec)) then
	      false
	    else
              begin
		let facts3 = skip (lh-lh') facts in
		try
		  auto_cleanup (fun () ->
		    match_modulo_list (fun () ->
	              match_equiv_list (fun () -> ()
			  ) facts3 (fact'::facts') 
			) (skip (lnp-lnp') name_params) name_params' 
		      );
		  true
		with Unify -> false
              end
	| _ -> false
      end

(* let match_action = Profile.f3 "match_action" match_action *)

(* TO DO for passive attackers, this will almost always fail! *)

let do_red_io f public_channel son_node (tc, t, p, name_params, occs, facts, cache_info) prev_state =
  debug_print "Doing Red I/O";
  let n, _ = find_proc_for_current_node 0 son_node prev_state.subprocess in
  let proc_list = remove_at n prev_state.subprocess in
  let n', (proc', name_params', occs', facts', cache_info') =
    find_proc_for_current_node 0 prev_state.current_node proc_list in
  let n'' = if n' >= n then n'+1 else n' in
  match proc' with
    Input(tc',pat',p',occ') ->     
      begin
      try
        auto_cleanup (fun () ->
	  term_evaluation_name_params (fun tc' name_params' ->
	    if not (equal_terms_modulo tc' tc) then raise No_result;
	    let fact = Pred(prev_state.mess_pred, [tc'; t]) in
	    let new_occs' = (InputTag occ')::occs' in
	    match_pattern (fun () -> 
	      let name_params'' = update_name_params name_params' pat' in
	      let p'' = auto_cleanup (fun () -> copy_process p') in
	      let action = IOAction(name_params', new_occs', facts', fact) in
	      let cur_state' = 
		{ prev_state with
	          subprocess = replace_at n (p, name_params, occs, facts, Nothing) 
			    (replace_at n'' (p'', name_params'', new_occs', fact :: facts', Nothing)
			    prev_state.subprocess);
	          executed_actions = action :: prev_state.executed_actions;
	          expect_redIO = dummy_node;
	          public = if public_channel then add_in_public prev_state.public t else prev_state.public;
		  comment = RIO(n'', tc', pat', n, tc, t);
		  previous_state = Some prev_state }
	      in
	      match prev_state.goal with
		Pred(p,[tcg;tg]) when (p == prev_state.mess_pred) &&
		(equal_terms_modulo tg t) && (equal_terms_modulo tcg tc) ->
		  (* SUCCESS! *)
		  cur_state'
	      | _ -> 
		  f (if n < n'' then
		    do_nil_par_restr (do_nil_par_restr cur_state' n'') n
		  else
		    do_nil_par_restr (do_nil_par_restr cur_state' n) n'')
		    ) pat' t
	 ) tc' occs' facts' name_params' prev_state.current_node
		      )
        with Unify -> (* A destructor evaluation fails or the pattern does not match *)
	  debug_print "Red I/O: destructor evaluation fails or pattern does not match";
	  raise No_result
      end
  | _ ->
      debug_print "Red I/O: Input expected";
      raise No_result

let rec do_red_nointeract f prev_state =
  let proc_list = truncate (prev_state.max_current_node - prev_state.min_current_node) (skip prev_state.min_current_node prev_state.subprocess) in
  try
  let n, (proc, name_params, occs, facts, cache_info) =
    find_proc_for_current_node prev_state.min_current_node prev_state.current_node proc_list in
  match proc with
  | Let(pat,t,p,q,occ) ->
      debug_print "Doing Let";
      let new_occs = (LetTag occ) :: occs in
      begin
      try 
        auto_cleanup (fun () -> 
        term_evaluation_name_params (fun t' name_params' ->
          match_pattern (fun () -> 
            let p' = copy_process p in
            let name_params'' = 
              if !Param.all_vars_in_names then
                update_name_params name_params' pat
              else
                name_params'
            in 
          do_red_nointeract f 
	      (do_nil_par_restr { prev_state with
	    subprocess = replace_at n (p', name_params'', new_occs, facts, Nothing) prev_state.subprocess;
            comment = RLet1(n, pat, t);
	    min_current_node = n;
	    max_current_node = n+1;
            previous_state = Some prev_state } n)
	      ) pat t'
           ) t new_occs facts name_params prev_state.current_node)
      with Unify ->
        do_red_nointeract f 
	  (do_nil_par_restr { prev_state with
	  subprocess = replace_at n (q, name_params, new_occs, facts, Nothing) prev_state.subprocess;
          comment = RLet2(n, pat, t);
          min_current_node = n;
	  max_current_node = n+1;
          previous_state = Some prev_state } n)
      end
  | Test(t1,t2,p,q,occ) ->
      debug_print "Doing Test";
      begin
	try
          auto_cleanup (fun () ->
	    let new_occs = (TestTag occ) :: occs in
            term_evaluation_name_params (fun t1' name_params' ->
	      term_evaluation_name_params (fun t2' name_params'' ->
                if equal_terms_modulo t1' t2' then
	          do_red_nointeract f 
		    (do_nil_par_restr { prev_state with
	              subprocess = replace_at n (p, name_params'', new_occs, facts, Nothing) prev_state.subprocess;
                      comment = RTest1(n, t1, t2);
	              min_current_node = n;
	              max_current_node = n+1;
                      previous_state = Some prev_state } n)
                else
                  do_red_nointeract f 
		    (do_nil_par_restr { prev_state with
	              subprocess = replace_at n (q, name_params'', new_occs, facts, Nothing) prev_state.subprocess;
                      comment = RTest2(n, t1, t2);
	              min_current_node = n;
	              max_current_node = n+1;
                      previous_state = Some prev_state } n)
	      ) t2 new_occs facts name_params' prev_state.current_node
            ) t1 new_occs facts name_params prev_state.current_node
	  )
        with Unify ->
	  debug_print "Test: destructor fails";
	  raise No_result
      end
  | Output(tc,t,p,occ) ->
      debug_print "Doing Output";
      begin
	let new_occs = (OutputTag occ) :: occs in
	try
	  auto_cleanup (fun () ->
            term_evaluation (fun tc' ->
	      term_evaluation (fun t' ->
		if is_channel tc' then
		  begin
		    let public_channel = channel_public prev_state.public tc' in
                    (* For active attackers, one can output on public channels *)
		    if (!Param.active_attacker) && public_channel then
		      begin
			let action = OutputAction(name_params, new_occs, facts, Pred(prev_state.mess_pred, [tc'; t'])) in
			let state' =
			    (do_nil_par_restr { prev_state with
                              subprocess = replace_at n (p, name_params, new_occs, facts, Nothing) prev_state.subprocess;
			      comment = ROutput1(n, tc, t);
	                      executed_actions = action :: prev_state.executed_actions;
	                      public = add_in_public prev_state.public t';
	                      min_current_node = n;
	                      max_current_node = n+1;
			      previous_state = Some prev_state } n)
			in
			if match_action dummy_node prev_state.current_node action then
			  f state'
			else
			  do_red_nointeract f state'
		      end
		    else
		      (* first reduce the process corresponding to the father node,
			 then apply Red I/O with the father node in the derivation tree *)
		      begin
			if prev_state.expect_redIO != dummy_node then
			  begin
			    debug_print "Unexpected Red I/O";
			    raise No_result
			  end;
	                (* print_string "Father node ";
	                Display.display_fact prev_state.father_node.thefact;
	                print_newline(); *)
	                match prev_state.father_node.desc with
	                  FRule(_,ProcessRule(_, _), _, _) ->
	                    let action = OutputAction(name_params, new_occs, facts, Pred(prev_state.mess_pred, [tc'; t'])) in
	                    if match_action dummy_node prev_state.current_node action then
	                      begin
	                        debug_print "Reducing father node in view of Red I/O";
			        do_red_nointeract (fun state -> do_red_io f public_channel prev_state.current_node (tc', t', p, name_params, new_occs, facts, cache_info) state) { prev_state with 
                                    current_node = prev_state.father_node;
                                    father_node = dummy_node;
                                    expect_redIO = prev_state.current_node;
                                    min_current_node = 0;
                                    max_current_node = List.length (prev_state.subprocess) }
                              end
                            else
                              begin
                                debug_print "I block on an output on a private channel before reaching\nthe action corresponding to the current node.";
	                        raise No_result
                              end
	               | _ -> debug_print "Cannot reduce father node";
	                      raise No_result
		      end
		  end
		else
		  begin
		    debug_print "Output not on a channel";
		    raise No_result
		  end
			      ) t
			    ) tc
		       )
	with Unify ->
	  debug_print "Output: destructor fails";
	  raise No_result
      end
  | Event(FunApp(fs,l) as t,p,occ) ->
      debug_print "Doing Event";
      let fstatus = Pievent.get_event_status fs in
      let do_begin() =
	match fstatus.begin_status with
	  No -> 
	    let new_occs = (BeginEvent (occ)) :: occs in
	    do_red_nointeract f 
	          (do_nil_par_restr { prev_state with
	                              subprocess = replace_at n (p, name_params, new_occs, facts, Nothing) prev_state.subprocess;
				      comment = RBegin1(n, t);
     	                              min_current_node = n;
	                              max_current_node = n+1;
				      previous_state = Some prev_state } n)
	| NonInj | Inj ->
	    try
	    auto_cleanup (fun () ->
	      term_evaluation_name_params (fun t' name_params' ->
		  let new_occs = BeginFact :: (BeginEvent (occ)) :: occs in
		  let new_facts = (Out(t', [])) :: facts in
		  auto_cleanup (fun () ->
		    let _ = find_io_rule new_occs new_facts name_params' [] prev_state.current_node in
		    do_red_nointeract f 
		      (do_nil_par_restr { prev_state with
	                                      subprocess = replace_at n (p, name_params', new_occs, new_facts, Nothing) prev_state.subprocess;
                                              comment = RBegin1(n, t);
	                                      min_current_node = n;
	                                      max_current_node = n+1;
				              previous_state = Some prev_state } n)
			       )
					  ) t occs facts name_params prev_state.current_node)
            with Unify ->
	      debug_print "Event: destructor fails";
	      raise No_result
      in
      begin
	try
	auto_cleanup( fun () ->
	  term_evaluation (fun t'' ->
	    match (fstatus.end_status, prev_state.goal) with
	    | (NonInj, Pred(pr,[t'])) when pr == Param.end_pred ->
		if equal_terms_modulo t'' t' then
		  begin
		    debug_print "Success";
		  (* SUCCESS! *)
		  { prev_state with
	            subprocess = replace_at n (p, name_params, occs, facts, Nothing) prev_state.subprocess;
		    comment = REnd(n,t);
		    previous_state = Some prev_state }
		  end
		else
		  do_begin()
	    | (Inj, Pred(pr,[_;t'])) when pr == Param.end_pred_inj ->
		if equal_terms_modulo t'' t' then
		  begin
		    debug_print "Success";
		  (* SUCCESS! *)
		  { prev_state with
	            subprocess = replace_at n (p, name_params, occs, facts, Nothing) prev_state.subprocess;
		    comment = REnd(n,t);
		    previous_state = Some prev_state }
		  end
		else
		  do_begin()
	    | _ -> do_begin()
			  ) t)
        with Unify ->
	  debug_print "Event: destructor fails";
	  raise No_result
      end
  | LetFilter(bl, Pred(pr,l), p, q, occ) ->
      debug_print "Doing LetFilter";
      begin
	try
	  let new_occs = (LetFilterTag occ) :: occs in
	  let vars_bl = List.map (fun b -> Var b) bl in
	  auto_cleanup (fun () ->
	    term_evaluation_letfilter (fun l' name_params' ->
	      let fact' = Pred(pr,l') in
	      try
 	        let terms_bl = find_io_rule new_occs (fact' :: facts) name_params' vars_bl prev_state.current_node in
		let new_facts' = (TermsEq.copy_remove_syntactic_fact fact') :: facts in
		List.iter2 (fun b term_b ->
		      Terms.link b (TLink term_b)) bl terms_bl;
	        let name_params'' = List.map copy_closed_remove_syntactic name_params' in
                let p' = auto_cleanup (fun () -> copy_process p) in
                do_red_nointeract f 
		  (do_nil_par_restr { prev_state with
	                              subprocess = replace_at n (p', name_params'', LetFilterFact :: new_occs, new_facts', Nothing) prev_state.subprocess;
                                      comment = RLetFilter1(n, bl, Pred(pr,l));
	                              min_current_node = n;
	                              max_current_node = n+1;
				          previous_state = Some prev_state } n)
              with Unify ->
		(* it should be ok to query the fact with names instead of patterns? *)
	        let letfilterclauses = auto_cleanup (fun () -> Rules.query_goal_std fact') in
                if letfilterclauses != [] (* fact' may be derivable from the clauses => 
                     LetFilter may succeed but not allowed by the derivation tree =>
                     consider that LetFilter blocks *) then
                  raise Unify
	        else
	          do_red_nointeract f 
		    (do_nil_par_restr { prev_state with 
	                    subprocess = replace_at n (q, name_params, new_occs, facts, Nothing) prev_state.subprocess;
		            comment = RLetFilter3(n, bl, Pred(pr,l));
    	                    min_current_node = n;
	                    max_current_node = n+1;
		            previous_state = Some prev_state } n)
	                                     ) l (vars_bl @ name_params)
	               )
	with Unify ->
	  debug_print "LetFilter: destructor fails";
	  raise No_result
      end
  | Repl(p,occ) ->
      debug_print "Doing Repl";
      let sid = Terms.new_var "sid" in
      let new_occs = (ReplTag (occ,List.length name_params))::occs in
      begin
	try
          match find_io_rule new_occs facts ((Var sid)::name_params) [Var sid] prev_state.current_node with
            [(FunApp(sid,[])) as sid_pat] ->
	       (* TO DO this assumes no non-interference and no key compromise
	          (which is coherent with the current usage of this module)
	          With key compromise, we may need two session ids.
                  With non-interference, we need to add the session ids in inputs and input_facts *)
	      let cache_info' = 
		 begin
		   match cache_info with
		     ReplInfo l_sid -> ReplInfo (sid :: l_sid)
		   | Nothing -> ReplInfo [sid]
		 end
	      in
              let p' = auto_cleanup (fun () -> copy_process p) in
              do_red_nointeract f 
		(do_nil_par_restr { prev_state with
                                    subprocess = add_at n (p', sid_pat::name_params, new_occs, facts, Nothing) 
	                               (replace_at n (proc, name_params, occs, facts, cache_info') prev_state.subprocess);
	                            min_current_node = n;
	                            max_current_node = n+1;
	                            comment = RRepl(n,1);
	                            previous_state = Some prev_state
                                  } n)
           | _ -> Parsing_helper.internal_error "Repl case, reduction.ml"
        with Unify ->
	  Parsing_helper.internal_error "Repl case 2, reduction.ml"
      end
  | Input(tc,pat,p,occ) -> 
      debug_print "Doing Input";
      let do_redIO = 
	(prev_state.expect_redIO != dummy_node) &&
	(let FRule(_, _,_,sons) = prev_state.current_node.desc in
	 prev_state.expect_redIO == List.nth (List.rev sons) (List.length facts))
      in
      if do_redIO then f prev_state else
      let new_occs = (InputTag occ) :: occs in
      begin
      try
        auto_cleanup (fun () ->
	  term_evaluation_name_params (fun tc' name_params' ->
	    if not (is_channel tc') then 
	      begin
                debug_print "Input: non-channel";
	        raise No_result
	      end;
	    let m = Terms.new_var "m" in
	    let fact = Pred(prev_state.mess_pred, [tc'; Var m]) in
	    let public_channel = channel_public prev_state.public tc' in
            if (!Param.active_attacker) && public_channel then
	      begin
		(* Input on a public channel, and the attacker is active: apply (Res In)  *)
		  match find_io_rule new_occs (fact :: facts) name_params' [Var m] prev_state.current_node with
		    [mess_term] ->
		      (* Optionally check that the message is public *)
			if !double_check then
			  begin
			    if not (is_in_public prev_state.public mess_term) then
			      Parsing_helper.internal_error "Input message is not public; the invariant should guarantee that it is!";
	                  end;
		      auto_cleanup (fun () ->
			match_pattern (fun () -> 
			  let name_params'' = update_name_params name_params' pat in
			  let p' = auto_cleanup (fun () -> copy_process p) in
			  let fact' = Pred(prev_state.mess_pred, [tc'; mess_term]) in
			  do_red_nointeract f 
			    (do_nil_par_restr { prev_state with
                                                subprocess = replace_at n (p', name_params'', new_occs, fact' :: facts, Nothing) 
                                                  prev_state.subprocess;
                                                comment = RInput(n, tc, pat, mess_term);
                                                previous_state = Some prev_state } n)
       			       ) pat mess_term
			    )
		  | _ -> Parsing_helper.internal_error "input case; reduction.ml"
	      end
	    else
	      begin
	      (* Red I/O should have been applied by a previous output *)
		debug_print "Input: Red I/O should have been applied";
		raise No_result
	      end
                ) tc new_occs facts name_params prev_state.current_node
            )
      with Unify ->
	debug_print "Input: destructor fails";
	raise No_result
      end
  | Phase(n,p) -> (* TO DO Phases still to implement *)
      Parsing_helper.internal_error "Phases not yet implemented"
  | Nil | Par _ | Restr _ -> 
      Parsing_helper.internal_error "Nil, Par, Restr should have been reduced"
with Not_found ->
  debug_print "Process not found";
  raise No_result (* Cannot continue executing on the same current node *)


(* Test success *)

let test_success cur_state =
  match cur_state.goal with
    Pred(p,[t]) when p == cur_state.attacker_pred ->
      is_in_public cur_state.public t
  | Pred(p,[tc;t]) when p == cur_state.mess_pred ->
      (is_channel tc &&
       is_in_public cur_state.public t &&
       is_in_public cur_state.public tc)
  | _ -> false

(* Initial attacker knowledge *)

let rec public_build l =
  match l with
  | [] -> []
  | h::t ->
      if not h.f_private then
	(FunApp(h,[]))::(public_build t)
      else
	public_build t

(* Initialize the rule lists *)

let rev_name_subst_tags = function
    ProcessRule (hsl,nl) -> ProcessRule (hsl,List.map rev_name_subst nl)
  | t -> t

let rec rev_name_subst_tree t =
  { thefact = rev_name_subst_fact t.thefact;
    desc = match t.desc with
      FRemovedWithProof t -> FRemovedWithProof (rev_name_subst_tree t)
    | FEquation son -> FEquation (rev_name_subst_tree son)
    | FRule(n, tags, constra, sons) ->
	FRule(n, rev_name_subst_tags tags, constra, List.map rev_name_subst_tree sons)
    | d -> d
  } 
  

let rec init_rule state tree =
  match tree.desc with
  | FHAny -> 
      begin
	match tree.thefact with
	  Pred(_,[t]) ->
	    begin
	      match follow_link t with
		FunApp({ f_cat = Name _; f_private = false },[]) as valname ->
		  
		  { state with public = valname :: state.public }
                  (* we add the FHAny directly to the attacker knowledge *)
	      |	 _ -> Parsing_helper.internal_error "Bad FHAny"
	    end
	| _ -> Parsing_helper.internal_error "Bad FHAny"
      end
  | FEmpty -> 
      begin
	match tree.thefact with
	  Out(_,_) -> state
	| Pred(p, [t]) when p.p_prop land Param.pred_ATTACKER != 0 ->
	    begin
	      match follow_link t with
		FunApp({ f_cat = Name _; f_private = false },[]) as valname ->
		  { state with public = valname :: state.public }
	      |	_ -> 
		  if is_in_public state.public t then 
		    state
		  else
                    { state with 
                      public = t :: state.public;
	              hyp_not_matched = (Pred(p,[t]))::state.hyp_not_matched }
            end
        | _ -> 
	     { state with
	       hyp_not_matched = tree.thefact::state.hyp_not_matched }
      end
  | FRemoved | FRemovedWithProof _ -> state
  | FRule (n, tags, constra, sons) ->
      let rec init_sons_rule state1 = function
	| [] -> state1
	| h::t ->
	    let state1' = init_rule state1 h in
	    init_sons_rule state1' t
      in 
      init_sons_rule state sons
  | FEquation son -> init_rule state son

(* The main search function *)

(* The order of scanning of sons is important for the following reasons:
   - we must scan them so that "FRemoved" nodes appear before their
   corresponding non-removed duplicate
   - we must scan hypotheses of process rules in the order of the process,
   so that, when we execute (Res I/O), the actions that precede the
   input have already been executed.
   (this is coherent with the previous order)
   - in rule (Rl), the channel must be scanned first, then the
   message, so that when we execute the output, we have already
   proved that the channel is public.
   (to have that, the att(channel) hypothesis of (Rl) must be before
   its mess(channel,message) hypothesis)

*)


let rec search_derivation_tree next_f cur_state father node =
  match node.desc with
    FRemoved -> next_f cur_state (* Only attacker facts that have been visited before may be "FRemoved" *)
  | FEquation son -> search_derivation_tree next_f cur_state node son
  | FRemovedWithProof p -> search_derivation_tree next_f cur_state father p
  | FHAny | FEmpty -> next_f cur_state
  | FRule(n, tags, constra, sons) ->
      let already_done = match tags with
	ProcessRule _ ->
	  List.exists (match_action father node) cur_state.executed_actions 
      |	Rn | Apply _ ->
	  if (!Param.simplify_derivation) then
	    false (* When the derivation is simplified, duplicate attacker facts are removed *)
	  else
	    begin
	      match node.thefact with
		Pred(p,[t]) -> is_in_public cur_state.public t
		    (* TO DO Phases not implemented *)
	      |	_ -> Parsing_helper.internal_error "Attacker fact expected"
	    end
      |	_ -> false
      in 
      if already_done then
	next_f cur_state (* Action already executed *)
      else
      search_derivation_tree_list (fun new_state -> 
	(* print_string "Visiting node ";
	Display.display_fact node.thefact;
	print_newline(); *)
	match tags with
	  Rn | Apply _ -> 
	    do_attacker_rule next_f { new_state with 
                  current_node = node; 
	          father_node = father;
                  min_current_node = 0; 
                  max_current_node = List.length new_state.subprocess }
	| ProcessRule _ ->
	    do_red_nointeract next_f { new_state with 
                  current_node = node; 
	          father_node = father;
                  min_current_node = 0; 
                  max_current_node = List.length new_state.subprocess }
	| LblEquiv | Rl _ | Rs _ | Init | PhaseChange | LblNone | Isname _ | Elem _ | TestUnif ->
	    next_f new_state
	  ) cur_state node sons

and search_derivation_tree_list next_f cur_state father = function
    [] -> next_f cur_state
  | (a::l) -> search_derivation_tree_list (fun state -> search_derivation_tree next_f state father a) cur_state father l
	(* Visit the node a after l, so that the Removed nodes are seen after their non-removed duplicate
	   has been visited *)

let do_reduction tree =
(*  Profile.start();  *)
  let public_init = public_build !freenames in
  public_free := public_init;
  display_init_state := true;
  init_name_mapping (!freenames);
  close_tree tree;
  let tree = rev_name_subst_tree tree in
  let init_state = { goal = tree.thefact;
		     subprocess = [(!(main_process), [],[],[],Nothing)];
		     public = public_init;
		     executed_actions = [];
		     previous_state = None;
		     hyp_not_matched = [];
		     attacker_pred = Param.attacker_pred;
		     mess_pred = Param.mess_pred;
		     current_phase = 0;
		     current_node = dummy_node;
	             father_node = dummy_node;
		     expect_redIO = dummy_node;
		     min_current_node = 0;
		     max_current_node = 1;
		     comment = RInit } in
  let res = 
  begin
  try
    let state = do_nil_par_restr (init_rule init_state tree) 0 in
    let final_state = search_derivation_tree (fun cur_state ->
      if test_success cur_state then cur_state else raise No_result) state dummy_node tree
    in
    if final_state.hyp_not_matched = [] then 
      begin
	display_trace final_state; 
	print_endline "An attack has been found.";
	true
      end
    else
      begin
	display_trace final_state; 
	print_endline "An attack has been found, assuming the following hypothesis :";
	List.iter (fun x ->
	  print_string "    * ";
	  Termslinks.display_fact_with_links x;
	  print_newline ()) final_state.hyp_not_matched;
	print_newline ();
	false
      end
  with No_result ->
    if not (!Param.trace_backtracking) then
      print_endline "Blocked!";
    print_endline "Could not find an attack corresponding to this derivation.";
    false
  end
  in
  Terms.cleanup ();
(*  Profile.stop(); *)
  res

