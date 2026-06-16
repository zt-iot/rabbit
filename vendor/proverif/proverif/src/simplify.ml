open Parsing_helper
open Types
open Pitypes

(* [reject_choice_true_false] is [true] when a process that still
   contains a test "if choice[true,false] then ... else ..."
   should be discarded.
   Indeed, ProVerif is very unlikely to prove observational equivalence
   for such processes. *)

let reject_choice_true_false = ref false

(* [simplif_done] is set to [true] when a real simplification
   has been done during the simplification of a process.
   A real simplification can be merging two branches of if
   or decomposing a "let f(...) = f(...) in".
   By default, simplified processes in which no real simplification
   has been done are discarded. *)

let simplif_done = ref false

let new_occurrence = Terms.new_occurrence

(*********************************************
          Types of normalised process
**********************************************)

type normalised_process_P =
  {
    seq_names : (funsymb * new_args) list;
    seq_lets : (binder * term) list;
    seq_cond : normalized_process_D
  }

and normalized_process_D =
    IfNorm of term * normalized_process_D * normalized_process_D
  | NormProc of normalised_process_Q

and normalised_process_Q = (normalised_process_R list) * (normalised_process_Repl option)

and normalised_process_Repl =
  {
    r_seq_names : (funsymb * new_args) list;
    r_seq_lets : (binder * term) list;
    r_proc : normalised_process_Q
  }

and normalised_process_R =
  | InNorm of term * binder * normalised_process_P * bool (* [true] when precise *)
  | OutNorm of term * term * normalised_process_Q
  | EventNorm of term * normalised_process_Q
  | InsertNorm of term * normalised_process_Q
  | GetNorm of binder * term * normalised_process_P * normalised_process_P * bool (* [true] when precise *)
  | LetFilterNorm of fact * normalised_process_P * normalised_process_P * bool (* [true] when precise *)
  | PhaseNorm of int * normalised_process_R

(************************************************
	Display of normalized processes
************************************************)

let rec display_norm_P align proc =
  if proc.seq_names != [] then
    begin
      print_string align;
      List.iter (fun (f,args) ->
	Display.Text.display_keyword "new";
	print_string " ";
	print_string (Display.string_of_fsymb f);
	print_string ".") proc.seq_names;
      print_newline()
    end;
  if proc.seq_lets != [] then
    begin
      print_string align;
      Display.Text.display_list (fun (b,t) ->
	Display.Text.display_keyword "let";
	print_string " ";
	Printf.printf "%s = " (Display.string_of_binder b);
	Display.Text.display_term t;
	print_string " ";
	Display.Text.display_keyword "in";
	) " " proc.seq_lets;
      print_newline()
    end;
  display_norm_D align proc.seq_cond

and display_norm_D align = function
    IfNorm(cond,p1,p2) ->
      print_string align;
      Display.Text.display_keyword "if";
      print_string " ";
      Display.Text.display_term cond;
      print_string " ";
      Display.Text.display_keyword "then";
      print_string " (\n";
      display_norm_D (align ^ "  ") p1;
      print_string (align ^ ") ");
      Display.Text.display_keyword "else";
      print_string " (\n";
      display_norm_D (align ^ "  ") p2;
      print_string (align ^ ")\n")
  | NormProc p -> display_norm_Q align p

and display_norm_Q align (procsR,procP) =
  print_string align;
  if procsR = [] && procP = None
  then print_string "Nil\n"
  else
    begin
      print_string "(\n";
      let rec display_par_list = function
	  [] -> ()
	| [p] ->
	    display_norm_R (align^"  ") p;
	    print_string (align^")")
	| p::l ->
	    display_norm_R (align^"  ") p;
	    print_string (align^") | (");
	    print_newline();
	    display_par_list l
      in
      display_par_list procsR;
      begin
	match procP with
	| None -> ()
	| Some p ->
	    if procsR != [] then print_string " | (\n";
	    print_string (align ^ "  !\n");
            display_norm_Repl (align^"  ") p;
	    print_string (align^")");
      end;
      print_newline()
  end

and display_norm_Repl align proc =
  if proc.r_seq_names != [] then
    begin
      print_string align;
      List.iter (fun (f,args) ->
	Display.Text.display_keyword "new";
	print_string " ";
	print_string (Display.string_of_fsymb f);
	print_string ".") proc.r_seq_names;
      print_newline()
    end;
  if proc.r_seq_lets != [] then
    begin
      print_string align;
      Display.Text.display_list (fun (b,t) ->
	Display.Text.display_keyword "let";
	print_string " ";
	Printf.printf "%s = " (Display.string_of_binder b);
	Display.Text.display_term t;
	print_string " ";
	Display.Text.display_keyword "in";
	) " " proc.r_seq_lets;
      print_newline()
    end;
  display_norm_Q align proc.r_proc

and display_norm_R align = function
  | InNorm(t,b,p,_) ->
      print_string align;
      Display.Text.display_keyword "in";
      print_string "(";
      Display.Text.display_term t;
      Printf.printf ",%s)." (Display.string_of_binder b);
      print_newline();
      display_norm_P align p
  | OutNorm(t1,t2,p) ->
      print_string align;
      Display.Text.display_keyword "out";
      print_string "(";
      Display.Text.display_term t1;
      Printf.printf ",";
      Display.Text.display_term t2;
      print_string ").";
      print_newline();
      display_norm_Q align p
  | EventNorm(t,p) ->
      print_string align;
      Display.Text.display_keyword "event";
      print_string "(";
      Display.Text.display_term t;
      print_string ").";
      print_newline();
      display_norm_Q align p
  | InsertNorm(t,p) ->
      print_string align;
      Display.Text.display_keyword "insert";
      print_string "(";
      Display.Text.display_term t;
      print_string ").";
      print_newline();
      display_norm_Q align p
  | GetNorm(x,t,p,p',_) ->
      print_string align;
      Display.Text.display_keyword "get";
      print_string " ";
      print_string (Display.string_of_binder x);
      print_string " ";
      Display.Text.display_keyword "suchthat";
      print_string " ";
      Display.Text.display_term t;
      print_string " ";
      Display.Text.display_keyword "then";
      display_norm_P (align^"  ") p;
      Display.Text.display_keyword "else";
      display_norm_P (align^"  ") p';
  | LetFilterNorm(fact,p,p',_) ->
      print_string align;
      Display.Text.display_keyword "if";
      print_string " ";
      Display.Text.display_fact fact;
      print_string " ";
      Display.Text.display_keyword "then";
      display_norm_P (align^"  ") p;
      Display.Text.display_keyword "else";
      display_norm_P (align^"  ") p';
  | PhaseNorm(n,p) ->
      print_string align;
      Display.Text.display_keyword "phase";
      print_string " ";
      print_int n;
      print_string ".";
      print_newline();
      display_norm_R align p


(*********************************************
             Copy of a process
**********************************************)

(* copy_process does not support linking a variable
   that occurs in the argument of a Restr to a non-variable
   term (because arguments of Restr are always variables,
   and it would need to replace that variable with a
   non-variable term). *)

(* [rename_private_name n] creates and returns a fresh private
   name with the same type as [n].
   The type of the arguments of the new name are reset to
   Param.tmp_type, so that they can be set by the subsequent
   translation into clauses. *)

let rename_private_name n =
  Terms.copy_name n Param.tmp_type

type copy_info_t =
    { add_in_glob_table : ((string, funsymb) Hashtbl.t * (string, term) Hashtbl.t) option;
      barrier_add_prefix : string }
    
let copy_binder copy_info b =
  let b' = Terms.copy_var b in
  begin
    match copy_info.add_in_glob_table with
    | Some(_,glob_table_var_name) ->
	if b.vname.orig_name <> "" then
	  Hashtbl.add glob_table_var_name b.vname.orig_name (Var b')
    | None -> ()
  end;
  match b.link with
    NoLink ->
      Terms.link b (TLink (Var b'));
      b'
  | _ -> Parsing_helper.internal_error ("unexpected link in copy_binder " ^ (Display.string_of_binder b))

let update_env env =
  Stringmap.StringMap.map (function
      (EVar b) as x ->
	begin
	match b.link with
	  TLink (Var b') -> EVar b'
	| _ -> x
	end
    | x -> x) env

let update_args_opt lopt =
  match lopt with
    None -> None, []
  | Some l ->
      let lets = ref [] in
      let new_args_opt =
	Some (List.map (fun b ->
	begin
	match b.link with
	  TLink (Var b') -> b'
	| TLink (FunApp(f, [Var b'])) when Terms.is_undo_catch_fail f -> b'
	| NoLink -> b
	| TLink t ->
	    let b' = Terms.copy_var b in
	    let glet_symb =  Terms.glet_fun b.btype in
	    lets := (b', FunApp(glet_symb, [t]))::(!lets);
	    b'
	| _ -> Parsing_helper.internal_error "unexpected link in Simplify.update_args_opt"
	end) l)
      in
      (new_args_opt, !lets)

let rec copy_pat copy_info = function
    PatVar b -> PatVar (copy_binder copy_info b)
  | PatTuple(f,l) -> PatTuple(f, List.map (copy_pat copy_info) l)
  | PatEqual(t) -> PatEqual (Terms.copy_term3 t)

let rec copy_process copy_info = function
    Nil -> Nil
  | Par(p1,p2) ->
      let p1' = copy_process copy_info p1 in
      let p2' = copy_process copy_info p2 in
      Par(p1', p2')
  | Restr(n,(args,env),p,occ) ->
      let (new_args,lets) = update_args_opt args in
      let n' = rename_private_name n in
      begin
	match copy_info.add_in_glob_table with
	| Some(glob_table, glob_table_var_name) ->
           begin
             match n.f_name with
               Fixed _ -> Parsing_helper.internal_error "names of restrictions should be renamable"
             | Renamable id ->
	        if id.orig_name <> "" then
	          begin
		    Hashtbl.add glob_table id.orig_name n';
		    Hashtbl.add glob_table_var_name id.orig_name (FunApp(n',[]));
	          end;
           end;
	| None -> ()
      end;
      Terms.put_lets (fun () -> 
	let occ' = new_occurrence() in
        Restr(n', (new_args,update_env env),
	      Reduction_helper.process_subst (copy_process copy_info p) n (FunApp(n',[])), occ')
	  ) lets
  | Repl(p,occ) ->
      let occ' = new_occurrence() in
      Repl(copy_process copy_info p, occ')
  | Let(pat, t, p, q, occ) ->
      Terms.auto_cleanup (fun () ->
	let pat' = copy_pat copy_info pat in
	let occ' = new_occurrence() in
	let p' = copy_process copy_info p in
	let q' = copy_process copy_info q in
	Let(pat', Terms.copy_term3 t, p', q', occ'))
  | Input(t, pat, p, occ) ->
      Terms.auto_cleanup (fun () ->
	let pat' = copy_pat copy_info pat in
	let occ' = new_occurrence ~precise:occ.precise () in
	Input(Terms.copy_term3 t, pat',
	      copy_process copy_info p, occ'))
  | Output(tc,t,p, occ) ->
      let occ' = new_occurrence() in
      Output(Terms.copy_term3 tc,
	     Terms.copy_term3 t,
	     copy_process copy_info p, occ')
  | Test(t,p,q,occ) ->
      let occ' = new_occurrence() in
      let p' = copy_process copy_info p in
      let q' = copy_process copy_info q in
      Test(Terms.copy_term3 t, p', q', occ')
  | Event(t, (args, env), p, occ) ->
      let (new_args,lets) = update_args_opt args in
      Terms.put_lets
	(fun () ->
	  let occ' = new_occurrence() in
	  Event(Terms.copy_term3 t, (new_args,update_env env),
		copy_process copy_info p, occ')) lets
  | Insert(t, p, occ) ->
      let occ' = new_occurrence() in
      Insert(Terms.copy_term3 t,
	     copy_process copy_info p, occ')
  | Get(pat, t, p, q, occ) ->
      Terms.auto_cleanup (fun () ->
	let pat' = copy_pat copy_info pat in
	let occ' = new_occurrence ~precise:occ.precise () in
	let p' = copy_process copy_info p in
	let q' = copy_process copy_info q in
	Get(pat', Terms.copy_term3 t, p', q', occ'))
  | Phase(n,p,occ) ->
      let occ' = new_occurrence() in
      Phase(n, copy_process copy_info p, occ')
  | Barrier(n,(tag, ext),p,occ) ->
      let occ' = new_occurrence() in
      Barrier(n, (copy_info.barrier_add_prefix^tag, ext), copy_process copy_info p, occ')
  | AnnBarrier _ ->
      Parsing_helper.internal_error "Annotated barriers should not occur in the initial process"
  | LetFilter(bl, f, p, q, occ) ->
      Terms.auto_cleanup (fun () ->
	let bl' = List.map (copy_binder copy_info) bl in
	let occ' = new_occurrence ~precise:occ.precise () in
	let p' = copy_process copy_info p in
	let q' = copy_process copy_info q in
	LetFilter(bl', Terms.copy_fact3 f, p', q', occ'))
  | NamedProcess(s, tl, p) ->
      Terms.auto_cleanup (fun () ->
	let p' = copy_process copy_info p in
	NamedProcess(s, List.map Terms.copy_term3 tl, p'))


let copy_process_desc copy_info p =
  { p with proc = copy_process copy_info p.proc; display_num = None }

(* Prepare a process by choosing new identifiers for names, variables... *)

let prepare_process pi_state =
  begin
    match pi_state.pi_need_vars_in_names with
      Computed (_ :: _) ->
	Parsing_helper.internal_error "Simplify.prepare_process should be called before computing pi_need_vars_in_names"
    | _ -> ()
  end;
  let glob_table = Hashtbl.create 7 in
  let glob_table_var_name = Hashtbl.create 7 in
  let copy_info =
    { add_in_glob_table = Some(glob_table, glob_table_var_name);
      barrier_add_prefix = "" }
  in
  let pi_process_query' =
    Terms.auto_cleanup (fun () ->
      Terms.reset_occurrence();
      match pi_state.pi_process_query with
	SingleProcess(p,ql) ->
	  let p' = copy_process_desc copy_info p in
	  SingleProcess(p',ql)
      | SingleProcessSingleQuery(p,q) ->
	  let p' = copy_process_desc copy_info p in
	  SingleProcessSingleQuery(p',q)
      | Equivalence(p1,p2) ->
	  let p1' = copy_process_desc copy_info p1 in
	  let p2' = copy_process_desc copy_info p2 in
	  Equivalence(p1',p2')
	    )
  in
  { pi_state with
    pi_process_query = pi_process_query';
    pi_glob_table = Set glob_table;
    pi_glob_table_var_name = Set glob_table_var_name;
    pi_terms_to_add_in_name_params = Unset }

let copy_process barrier_add_prefix p =
  copy_process { add_in_glob_table = None;
		 barrier_add_prefix = barrier_add_prefix } p

(*********************************************************************
     Create a copy of the process with occurrences nicely numbered.
***********************************************************************)

let rec new_occs = function
  | Nil -> Nil
  | NamedProcess(s, tl, p) -> NamedProcess(s, tl, new_occs p)
  | Par(p1,p2) ->
      let p1' = new_occs p1 in
      let p2' = new_occs p2 in
      Par(p1', p2')
  | Restr(n,opt,p,_) ->
      let occ = new_occurrence() in
      Restr(n, opt, new_occs p,occ)
  | Repl(p,_) ->
      let occ = new_occurrence() in
      Repl(new_occs p, occ)
  | Let(pat, t, p, q, _) ->
      let occ = new_occurrence() in
      let p' = new_occs p in
      let q' = new_occs q in
      Let(pat, t, p', q', occ)
  | Input(t, pat, p, occ_old) ->
      let occ = new_occurrence ~precise:occ_old.precise () in
      Input(t, pat, new_occs p, occ)
  | Output(tc,t,p, _) ->
      let occ = new_occurrence() in
      Output(tc, t, new_occs p, occ)
  | Test(t,p,q,_) ->
      let occ = new_occurrence() in
      let p' = new_occs p in
      let q' = new_occs q in
      Test(t, p', q',occ)
  | Event(t, opt, p, _) ->
      let occ = new_occurrence() in
      Event(t, opt, new_occs p, occ)
  | Insert(t, p, _) ->
      let occ = new_occurrence() in
      Insert(t, new_occs p, occ)
  | Get(pat, t, p, q, occ_old) ->
      let occ = new_occurrence ~precise:occ_old.precise () in
      let p' = new_occs p in
      let q' = new_occs q in
      Get(pat, t, p', q', occ)
  | Phase(n,p,_) ->
      let occ = new_occurrence() in
      Phase(n, new_occs p,occ)
  | LetFilter(bl, f, p, q, occ_old) ->
      let occ = new_occurrence ~precise:occ_old.precise () in
      let p' = new_occs p in
      let q' = new_occs q in
      LetFilter(bl, f, p', q', occ)
  | Barrier(n, tag, p, _) ->
      let occ = new_occurrence() in
      Barrier(n, tag, new_occs p, occ)
  | AnnBarrier _ ->
      Parsing_helper.internal_error "Annotated barriers should not appear in reset_occurrence"

let reset_occurrence p =
  Terms.reset_occurrence();
  new_occs p

(*************************************
	Follow links in a process
**************************************)

let rec follow_pattern = function
  | PatVar(x) -> PatVar(x)
  | PatTuple(f,l) -> PatTuple(f,List.map follow_pattern l)
  | PatEqual(t) -> PatEqual(Terms.copy_term3 t)

let rec follow_process = function
  | Nil -> Nil
  | NamedProcess(s, tl, p) ->
      NamedProcess(s, List.map (fun t -> Terms.copy_term3 t) tl, follow_process p)
  | Par(p1,p2) -> Par(follow_process p1,follow_process p2)
  | Repl(p,occ) -> Repl(follow_process p,occ)
  | Restr(f,args,p,occ) -> Restr(f,args,follow_process p,occ)
  | Test(t,p1,p2,occ) ->
      let t' = Terms.copy_term3 t
      and p1' = follow_process p1
      and p2' = follow_process p2 in
      Test(t',p1',p2',occ)
  | Input(t,pat,p,occ) ->
      let t' = Terms.copy_term3 t
      and pat' = follow_pattern pat
      and p' = follow_process p in
      Input(t',pat',p',occ)
  | Output(ch,t,p,occ) ->
      let ch' = Terms.copy_term3 ch
      and t' = Terms.copy_term3 t
      and p' = follow_process p in
      Output(ch',t',p',occ)
  | Let(pat,t,p1,p2,occ) ->
      let t' = Terms.copy_term3 t
      and pat' = follow_pattern pat
      and p1' = follow_process p1
      and p2' = follow_process p2 in
      Let(pat',t',p1',p2',occ)
  | LetFilter([],fact,p1,p2,occ) ->
      let fact' = Terms.copy_fact3 fact
      and p1' = follow_process p1
      and p2' = follow_process p2 in
      LetFilter([],fact',p1',p2',occ)
  | LetFilter(_,_,_,_,_) ->
      input_error "Merging and simplify do not support LetFilter in the process" dummy_ext
  | Event(t,args,p,occ) ->
      let t' = Terms.copy_term3 t in
      let p' = follow_process p in
      Event(t', args, p', occ)
  | Insert(t, p, occ) ->
      let t' = Terms.copy_term3 t in
      let p' = follow_process p in
      Insert(t', p', occ)
  | Get(pat, t, p, q, occ) ->
      let pat' = follow_pattern pat in
      let t' = Terms.copy_term3 t in
      let p' = follow_process p in
      let q' = follow_process q in
      Get(pat', t', p', q', occ)
  | Phase(n, proc,occ) -> Phase(n, follow_process proc, occ)
  | Barrier _ | AnnBarrier _ ->
     Parsing_helper.internal_error "Barriers should not appear here (8)"

let rec follow_process_P proc =
  { proc with
    seq_lets = List.map (fun (b,t) -> (b, Terms.copy_term3 t)) proc.seq_lets;
    seq_cond = follow_process_D proc.seq_cond
  }

and follow_process_D = function
    IfNorm(t,p1,p2) -> IfNorm(Terms.copy_term3 t, follow_process_D p1, follow_process_D p2)
  | NormProc(p) -> NormProc(follow_process_Q p)

and follow_process_Q (procs_R,proc_P) = match proc_P with
  | None -> (List.map follow_process_R procs_R,None)
  | Some p -> (List.map follow_process_R procs_R,Some (follow_process_Repl p))

and follow_process_Repl proc =
  { proc with
    r_seq_lets = List.map (fun (b,t) -> (b, Terms.copy_term3 t)) proc.r_seq_lets;
    r_proc = follow_process_Q proc.r_proc
  }

and follow_process_R = function
  | InNorm(t,x,p,pr) -> InNorm(Terms.copy_term3 t,x,follow_process_P p,pr)
  | OutNorm(ch,t,q) -> OutNorm(Terms.copy_term3 ch, Terms.copy_term3 t,follow_process_Q q)
  | EventNorm(t,q) -> EventNorm(Terms.copy_term3 t,follow_process_Q q)
  | InsertNorm(t,q) -> InsertNorm(Terms.copy_term3 t,follow_process_Q q)
  | GetNorm(x,t,p1,p2,pr) -> GetNorm(x,Terms.copy_term3 t,follow_process_P p1,follow_process_P p2,pr)
  | LetFilterNorm(fact,p1,p2,pr) -> LetFilterNorm(Terms.copy_fact3 fact,follow_process_P p1,follow_process_P p2,pr)
  | PhaseNorm(n,r) -> PhaseNorm(n,follow_process_R r)

(*********************************************
	      Helper functions
**********************************************)

(* [remove_from a l] returns the list [l] with the
   (first occurrence of) element [a] removed.
   The element [a] must occur in the list [l]. *)

let rec remove_from a = function
    [] -> Parsing_helper.internal_error "element should be in the list in remove_from"
  | a'::l ->
      if a' == a then l else a'::(remove_from a l)

(* [check_disjoint_append l1 l2] returns [l1 @ l2]
   and checks that the lists [l1] and [l2] do not have
   common elements *)

let rec check_disjoint_append l1 l2 =
  match l1 with
    [] -> l2
  | a::l ->
      if List.memq a l2 then
	Parsing_helper.internal_error "collision in check_disjoint_append"
      else
	a::(check_disjoint_append l l2)

(* [check_disjoint_pair_append l1 l2] returns [l1 @ l2]
   and checks that the lists [l1] and [l2] do not contain
   pairs with the same first element, corresponding to
   lets that bind the same variable or new names creating the
   same name. *)

let rec check_disjoint_pair_append l1 l2 =
  match l1 with
    [] -> l2
  | a::l ->
      let x = fst a in
      if List.exists (fun (x',t) -> x' == x) l2  then
	Parsing_helper.internal_error "collision in check_disjoint_pair_append"
      else
	a::(check_disjoint_pair_append l l2)

(*********************************************
              Normalize process
**********************************************)

(* [fst_snd_term next_f t] transforms the term [t] with choice into a pair of terms [t1,t2]
   and calls [next_f t1 t2].
   [fst_snd_term_list] is the same for lists of terms. *)

let rec fst_snd_term next_f = function
  | Var v -> next_f (Var v) (Var v)
  | FunApp({f_cat = Choice},[t1;t2]) ->
      fst_snd_term (fun t11 t12 ->
        fst_snd_term (fun t21 t22 ->
          next_f t11 t22
        ) t2
	  ) t1
  | FunApp({f_cat = ChoiceFst}, [t]) ->
      fst_snd_term (fun t1 t2 -> next_f t1 t1) t
  | FunApp({f_cat = ChoiceSnd}, [t]) ->
      fst_snd_term (fun t1 t2 -> next_f t2 t2) t
  | FunApp(f,args) ->
      fst_snd_term_list (fun q1 q2 ->
        next_f (FunApp(f,q1)) (FunApp(f,q2))
      ) args

and fst_snd_term_list next_f = function
  | [] -> next_f [] []
  | t::q ->
      fst_snd_term (fun t1 t2 ->
        fst_snd_term_list (fun q1 q2 ->
          next_f (t1::q1) (t2::q2)
        ) q
      ) t

let rec fst_snd_acc_unify next_f = function
  | [] -> next_f [] []
  | (a,b)::q ->
      fst_snd_term (fun a1 a2 ->
        fst_snd_term (fun b1 b2 ->
          fst_snd_acc_unify (fun q1 q2 ->
            next_f ((a1,b1)::q1) ((a2,b2)::q2)
          ) q
        ) b
      ) a

(****** Is always ? ******)

let rec unify_all accu_constra next_f = function
  | [] -> next_f accu_constra
  | (t1,t2)::q ->
      TermsEq.close_term_destr_eq accu_constra (fun accu_constra_1 t1' ->
	try
	  (* Check that inequality constraints are satisfiable at each step,
	     to cut impossible branches as soon as possible. *)
	  TermsEq.check_constraints accu_constra_1;
          TermsEq.close_term_destr_eq accu_constra_1 (fun accu_constra_2 t2' ->
	    try
	      TermsEq.check_constraints accu_constra_2;
	      (* Since close_term_destr_eq closes terms modulo equations, syntactic unification is enough *)
	      Terms.unify t1' t2';
              unify_all accu_constra_2 next_f q
	    with Terms.Unify | TermsEq.FalseConstraint -> ()
        ) t2
	with Terms.Unify | TermsEq.FalseConstraint -> ()
      ) t1


exception Unification_found

(* Check if there is at least one possible unification (no choice in term) *)
let is_unification_possible_no_choice acc_unify =
  try
    Terms.auto_cleanup (fun () ->
      unify_all Terms.true_constraints (fun _ -> raise Unification_found) acc_unify);
    false
  with Unification_found -> true

(* Check if there is at least one possible unification on right or left side *)
let is_unification_possible acc_unify =
  fst_snd_acc_unify (fun acc1 acc2 ->
       is_unification_possible_no_choice acc1
    || is_unification_possible_no_choice acc2
  ) acc_unify

let is_term_always_succeed_no_choice term acc_unify =
  try
    Terms.auto_cleanup (fun () ->
      unify_all Terms.true_constraints (fun accu_constra ->
        TermsEq.close_term_destr_eq accu_constra (fun neq_t t ->
          try
	    TermsEq.check_constraints neq_t;
            let new_t = Terms.copy_term2 t in
            Terms.cleanup();
            if Terms.is_may_fail_term new_t then
              raise Unification_found
          with Terms.Unify | TermsEq.FalseConstraint -> ()
        ) term
      ) acc_unify
    );
    true
  with Unification_found -> false

let is_term_always_succeed term acc_unify =
  fst_snd_acc_unify (fun acc1 acc2 ->
    fst_snd_term (fun t1 t2 ->
      (is_term_always_succeed_no_choice t1 acc1) &&
      (is_term_always_succeed_no_choice t2 acc2)
    ) term
  ) acc_unify

let is_term_always_true_no_choice term acc_unify =
  assert (Terms.equal_types (Terms.get_term_type term) Param.bool_type);
  try
    Terms.auto_cleanup (fun () ->
      unify_all Terms.true_constraints (fun accu_constra ->
        TermsEq.close_term_destr_eq accu_constra (fun neq_t t ->
          try
	    TermsEq.check_constraints neq_t;
	    (* Note: equal_open_terms_modulo follows links, so no need to copy t before *)
            if not (Reduction_helper.equal_open_terms_modulo t Terms.true_term)
            then raise Unification_found
          with Terms.Unify | TermsEq.FalseConstraint -> ()
        ) term;
      ) acc_unify
    );
    true
  with Unification_found -> false

let is_term_always_true term acc_unify =
  fst_snd_acc_unify (fun acc1 acc2 ->
    fst_snd_term (fun t1 t2 ->
        (is_term_always_true_no_choice t1 acc1) &&
        (is_term_always_true_no_choice t2 acc2)
    ) term
  ) acc_unify

let is_term_always_false_no_choice term acc_unify =
  assert (Terms.equal_types (Terms.get_term_type term) Param.bool_type);
  try
    Terms.auto_cleanup (fun () ->
      unify_all Terms.true_constraints (fun accu_constra ->
        TermsEq.close_term_destr_eq accu_constra (fun neq_t t ->
          try
	    TermsEq.check_constraints neq_t;
	    (* Note: equal_open_terms_modulo follows links, so no need to copy t before *)
            if not (Reduction_helper.equal_open_terms_modulo t Terms.false_term)
            then raise Unification_found
          with Terms.Unify | TermsEq.FalseConstraint -> ()
        ) term;
      ) acc_unify
    );
    true
  with Unification_found -> false

let is_term_always_false term acc_unify =
  fst_snd_acc_unify (fun acc1 acc2 ->
    fst_snd_term (fun t1 t2 ->
      (is_term_always_false_no_choice t1 acc1) &&
      (is_term_always_false_no_choice t2 acc2)
    ) term
  ) acc_unify

(****** Remove pattern ******)

let one_var_pattern_from_pattern pattern =

  let rec sub_one_var_pattern_from_pattern cor_term = function
    | PatVar(v) -> Terms.link v (TLink cor_term);
        Terms.true_term
    | PatTuple(f,[]) ->
        FunApp(Terms.equal_fun (snd f.f_type),[FunApp(f,[]);cor_term])
    | PatTuple(f,pat_list) ->
        let cor_term_list = List.map (fun f -> FunApp(f,[cor_term])) (Terms.get_all_projection_fun f) in
        let t1 = List.hd cor_term_list in
	let tuple_test = FunApp(Terms.success_fun (Terms.get_term_type t1),[t1]) in
        Terms.make_and tuple_test (sub_one_var_pattern_from_pattern_list cor_term_list pat_list)
    | PatEqual(t) ->
       FunApp(Terms.equal_no_fail_fun (Terms.get_term_type t),[t;cor_term])

  and sub_one_var_pattern_from_pattern_list cor_term_list pattern_list =
    match pattern_list,cor_term_list with
    | [],[] -> Terms.true_term
    | [],_ | _,[] -> internal_error "[one_var_pattern_from_pattern] The two list should have the same size"
    | pat::pat_l, cor::cor_l ->
        Terms.make_and (sub_one_var_pattern_from_pattern cor pat)
          (sub_one_var_pattern_from_pattern_list cor_l pat_l)
  in

  let x = Terms.new_var_def (Terms.get_pat_type pattern) in

  let test_success = sub_one_var_pattern_from_pattern (Var(x)) pattern in
  PatVar(x),test_success


(******  Simplify pattern and term evaluation:
	 make sure that patterns are always variables and
	 that term evaluations never fail ******)

let rec get_occ_rec accu = function
    Nil -> accu
  | NamedProcess(_, _, p) -> get_occ_rec accu p
  | Par(p1,p2) -> get_occ_rec (get_occ_rec accu p1) p2
  | Repl(_,occ) | Restr(_,_,_,occ) | Test(_,_,_,occ)
  | Input(_,_,_,occ) | Output(_,_,_,occ) | Let(_,_,_,_,occ)
  | LetFilter(_,_,_,_,occ) | Event(_,_,_,occ) | Insert(_,_,occ)
  | Get(_,_,_,_,occ) | Phase(_,_,occ) | Barrier(_,_,_,occ)
  | AnnBarrier(_,_,_,_,_,_,occ) ->
      let occ_str = "{" ^(string_of_int occ.occ) ^"}" in
      if accu = "" then
	occ_str
      else
        accu ^ ", " ^ occ_str

let get_occ_string p =
  let res = get_occ_rec "" p in
  if res = "" then "(parallel composition of 0) " else "at occurrence(s) " ^ res ^ " "

let rec verify_unification proc acc_unify =
  if is_unification_possible acc_unify
  then canonical_process proc acc_unify
  else
    begin
      if proc <> Nil
      then print_string ("Warning: A part of the protocol " ^ (get_occ_string proc) ^ "will never be executed\n");
      Nil
    end

and canonical_process process acc_unify = match process with
  | Nil -> Nil
  | NamedProcess(s, tl, p) ->
      canonical_process p acc_unify
  | Par (proc1,proc2) -> Par (canonical_process proc1 acc_unify,canonical_process proc2 acc_unify)
  | Repl (proc, occ) -> Repl (canonical_process proc acc_unify,occ)
  | Restr (funsymb,args,proc,occ) -> Restr (funsymb,args,canonical_process proc acc_unify,occ)
  | Test (term,proc1,proc2,occ) ->
      if is_term_always_succeed term acc_unify
      then Test(term,verify_unification proc1 ((term,Terms.true_term)::acc_unify), verify_unification proc2 ((term,Terms.false_term)::acc_unify), occ)
      else
        let type_term = Terms.get_term_type term in
        let x = Terms.new_var_def type_term in
        let catch = FunApp(Terms.glet_fun type_term,[term]) in
        let test = FunApp(Terms.not_caught_fail_fun type_term,[Var x]) in

        Let (PatVar x, catch,
          Test(test,
            Test(Var x,
              verify_unification proc1 ((test,Terms.true_term)::(Var x,Terms.true_term)::acc_unify),
              verify_unification proc2 ((test,Terms.true_term)::(Var x,Terms.false_term)::acc_unify),
              occ),
            Nil,
            new_occurrence ()
          ),
          Nil,
          new_occurrence ()
        )
  | Input(term,pat,proc,occ) ->
      begin match pat with
        | PatVar _ ->
            if is_term_always_succeed term acc_unify
            then Input(term,pat,canonical_process proc acc_unify,occ)
            else
              let type_term = Terms.get_term_type term in
              let x = Terms.new_var_def type_term in
              let catch = FunApp(Terms.glet_fun type_term,[term]) in
              let test = FunApp(Terms.not_caught_fail_fun type_term,[Var x]) in

              Let (PatVar x, catch,
               	Test(test,
               	  Input(Var x,pat,verify_unification proc ((Var x, catch)::(test,Terms.true_term)::acc_unify),occ),
               	  Nil,
               	  new_occurrence ()
                ),
                Nil,
                new_occurrence ()
              )
        | _ ->
            (* Test current_bound_vars *)
            assert (!Terms.current_bound_vars == []);

            let pat_x,test_success = one_var_pattern_from_pattern pat in

            let new_proc = match test_success with
              | FunApp(f,[]) when f == Terms.true_cst -> proc
              | _ -> Test(test_success,proc, Nil, new_occurrence ()) in

            let proc_substituted = follow_process new_proc in
            Terms.cleanup ();

            canonical_process (Input(term,pat_x,proc_substituted,occ)) acc_unify
      end
  | Output(ch_term,term,proc,occ) ->
      if is_term_always_succeed ch_term acc_unify
      then
        if is_term_always_succeed term acc_unify
        then Output(ch_term,term, canonical_process proc acc_unify,occ)
        else
          let type_term = Terms.get_term_type term in
          let x = Terms.new_var_def type_term in
          let catch = FunApp(Terms.glet_fun type_term,[term]) in
          let test = FunApp(Terms.not_caught_fail_fun type_term,[Var x]) in

          Let (PatVar x, catch,
            Test(test,
              Output(ch_term,Var x,verify_unification proc ((Var x, catch)::(test,Terms.true_term)::acc_unify),occ),
              Nil,
              new_occurrence ()
            ),
            Nil,
            new_occurrence ()
          )
      else
        if is_term_always_succeed term acc_unify
        then
          let type_ch_term = Terms.get_term_type ch_term in
          let x_ch = Terms.new_var_def type_ch_term in
          let catch_ch = FunApp(Terms.glet_fun type_ch_term,[ch_term]) in
          let test_ch = FunApp(Terms.not_caught_fail_fun type_ch_term,[Var x_ch]) in

          Let (PatVar x_ch, catch_ch,
            Test(test_ch,
              Output(Var x_ch,term,verify_unification proc ((Var x_ch, catch_ch)::(test_ch,Terms.true_term)::acc_unify),occ),
              Nil,
              new_occurrence ()
            ),
            Nil,
            new_occurrence ()
          )
        else
          let type_ch_term = Terms.get_term_type ch_term in
          let type_term = Terms.get_term_type term in

          let x_ch = Terms.new_var_def type_ch_term in
          let x = Terms.new_var_def type_term in

          let catch_ch = FunApp(Terms.glet_fun type_ch_term,[ch_term]) in
          let catch = FunApp(Terms.glet_fun type_term,[term]) in

          let test_ch = FunApp(Terms.not_caught_fail_fun type_ch_term,[Var x_ch]) in
          let test = FunApp(Terms.not_caught_fail_fun type_term,[Var x]) in

          Let (PatVar x_ch, catch_ch,
            Test(test_ch,
              Let (PatVar x, catch,
                Test(test,
                  Output(Var x_ch,Var x,verify_unification proc ((Var x, catch)::(test,Terms.true_term)::(Var x_ch, catch_ch)::(test_ch,Terms.true_term)::acc_unify),occ),
                  Nil,
                  new_occurrence ()
                ),
                Nil,
                new_occurrence ()
              ),
              Nil,
              new_occurrence ()
            ),
            Nil,
            new_occurrence ()
          )
  | Let(pat,term,proc1,proc2,occ) ->
      begin match pat with
        | PatVar x ->
            if is_term_always_succeed term []
               (* The "let"s can be moved above conditions by normalization,
		  so I cannot take into account previous conditions in acc_unify
		  to test whether the "let" always succeeds. *)
            then
              begin
                if proc2 <> Nil
                then (
                  print_string "Warning: The else branch in ";
                  Display.Text.display_occ occ;
                  print_string " will never be executed.\n"
                );

                Let(pat,term,verify_unification proc1 ((Var x, term)::acc_unify),Nil,occ)

              end
            else
              let type_term = Terms.get_term_type term in
              let catch = FunApp(Terms.glet_fun type_term,[term]) in
              let test = FunApp(Terms.not_caught_fail_fun type_term,[Var x]) in

              Let (PatVar x, catch,
               	Test(test,
               	  verify_unification proc1 ((Var x, catch)::(test,Terms.true_term)::acc_unify),
               	  verify_unification proc2 ((Var x, catch)::(test,Terms.false_term)::acc_unify),
               	  occ
               	),
                Nil,
                new_occurrence ()
              )
        | _ ->
            (* Test current_bound_vars *)
            assert (!Terms.current_bound_vars == []);

	    try
	      let rec decompose_pat_term pat term (pat_accu, term_accu) =
		match pat, term with
		| PatTuple(f,l), FunApp(f',l') when f.f_cat = Tuple && f == f' ->
		    simplif_done := true;
		    List.fold_right2 decompose_pat_term l l' (pat_accu, term_accu)
		| PatTuple(f,l), FunApp(f',l') when f.f_cat = Tuple && f'.f_cat = Tuple && f != f' ->
	            (* The let always fails *)
		    raise Not_found
		| _ -> pat::pat_accu, term::term_accu
	      in

	      let (pat_list, term_list) = decompose_pat_term pat term ([], []) in

              let pat_test_list = List.map one_var_pattern_from_pattern pat_list in

	      let term_test_list = List.map2 (fun (pat_x, _) t ->
		if is_term_always_succeed t []
                  (* The "let"s can be moved above conditions by normalization,
		     so I cannot take into account previous conditions in acc_unify
		     to test whether the "let" always succeeds. *)
		then
		  (t, Terms.true_term)
		else
		  match pat_x with
		    PatVar x ->
		      let type_term = Terms.get_term_type t in
		      let catch = FunApp(Terms.glet_fun type_term,[t]) in
		      let test = FunApp(Terms.not_caught_fail_fun type_term,[Var x]) in
		      (catch, test)
		  | _ -> Parsing_helper.internal_error "[simplify.ml >> canonical_process] patterns returned by one_var_pattern_from_pattern should be variables"
			) pat_test_list term_list
	      in

              let new_proc =
		match Terms.and_list ((List.map snd term_test_list) @ (List.map snd pat_test_list)) with
		| FunApp(f,[]) when f == Terms.true_cst ->
                    if proc2 <> Nil
                    then (
                      print_string "Warning: The else branch in ";
                      Display.Text.display_occ occ;
                      print_string " will never be executed.\n"
			);
		    proc1
		| t -> Test(t,proc1, proc2, new_occurrence ())
	      in

              let proc_substituted = follow_process new_proc in
              Terms.cleanup ();

	      let rec put_lets pat_test_list term_list p =
		match pat_test_list, term_list with
		  [],[] -> p
		| (pat_x, _)::l, (term,_)::l' ->
		    Let(pat_x, term, put_lets l l' p, Nil, new_occurrence ())
		| _ -> Parsing_helper.internal_error "[simplify.ml >> canonical_process] the list of patterns and terms should have the same length"
	      in

              canonical_process (put_lets pat_test_list term_test_list proc_substituted) acc_unify
	    with Not_found ->
	      canonical_process proc2 acc_unify
      end
  | LetFilter([],Pred(pr,args),proc1,proc2,occ) ->

      if List.for_all (fun t -> is_term_always_succeed t acc_unify) args
      then LetFilter([],Pred(pr,args),canonical_process proc1 acc_unify,canonical_process proc2 acc_unify,occ)
      else
        let rec generate_tests args' acc_unify' = function
          | [] -> LetFilter([],Pred(pr,List.rev args'),verify_unification proc1 acc_unify',verify_unification proc2 acc_unify',occ)
          | t::q ->
              if is_term_always_succeed t acc_unify'
              then generate_tests (t::args') acc_unify' q
              else
                let type_term = Terms.get_term_type t in
                let x = Terms.new_var_def type_term in
                let catch = FunApp(Terms.glet_fun type_term,[t]) in
                let test = FunApp(Terms.not_caught_fail_fun type_term,[Var x]) in

                Let (PatVar x, catch,
                  Test(test,
                    generate_tests ((Var x)::args') ((Var x, catch)::(test,Terms.true_term)::acc_unify') q,
                    Nil,
                    new_occurrence ()
                  ),
                  Nil,
                  new_occurrence ()
                )
        in

        generate_tests [] acc_unify args
  | LetFilter(_,_,_,_,_) -> internal_error "[simplify.ml >> canonical_process] LetFilter should not be in the process"
  | Event ((FunApp(f,args) as term),(_,env),proc,occ) ->
      (* Events are not ignored anymore when proving equivalences.
         Note however that environments are ignored.*)
      if is_term_always_succeed term acc_unify
      then Event(term,(None,env),canonical_process proc acc_unify,occ)
      else
        let rec generate_tests args' acc_unify' = function
          | [] -> Event(FunApp(f,List.rev args'),(None,env),verify_unification proc acc_unify',occ)
          | t::q ->
              if is_term_always_succeed t acc_unify'
              then generate_tests (t::args') acc_unify' q
              else
                let type_term = Terms.get_term_type t in
                let x = Terms.new_var_def type_term in
                let catch = FunApp(Terms.glet_fun type_term,[t]) in
                let test = FunApp(Terms.not_caught_fail_fun type_term,[Var x]) in

                Let (PatVar x, catch,
                  Test(test,
                    generate_tests ((Var x)::args') ((Var x, catch)::(test,Terms.true_term)::acc_unify') q,
                    Nil,
                    new_occurrence ()
                  ),
                  Nil,
                  new_occurrence ()
                )
        in

        generate_tests [] acc_unify args
  | Event(_,_,_,_) -> internal_error "[simplify.ml >> canonical_process] Event should be application functions."
  | Insert (term,proc,occ) ->
      if is_term_always_succeed term acc_unify
      then Insert(term,canonical_process proc acc_unify,occ)
      else
        let type_term = Terms.get_term_type term in
        let x = Terms.new_var_def type_term in
        let catch = FunApp(Terms.glet_fun type_term,[term]) in
        let test = FunApp(Terms.not_caught_fail_fun type_term,[Var x]) in

        Let (PatVar x, catch,
          Test(test,
            Insert(Var x,verify_unification proc ((Var x, catch)::(test,Terms.true_term)::acc_unify),occ),
            Nil,
            new_occurrence ()
          ),
          Nil,
          new_occurrence ()
        )
  | Get(pat,term,proc1,proc2,occ) ->
      let term' =
        if is_term_always_succeed term acc_unify then term else
	FunApp(Terms.is_true_fun(), [term])
      in
      begin match pat with
        | PatVar _ ->
            Get(pat,term',verify_unification proc1 ((term, Terms.true_term)::acc_unify),canonical_process proc2 acc_unify,occ)
        | _ ->
            (* Test current_bound_vars *)
            assert (!Terms.current_bound_vars == []);

            let pat_x,test_success = one_var_pattern_from_pattern pat in

            let new_term = Terms.make_and test_success term' in

            let proc_substituted = follow_process proc1 in
	    let term_substituted = Terms.copy_term3 new_term in
            Terms.cleanup ();

            Get(pat_x,term_substituted,
		verify_unification proc_substituted ((term_substituted, Terms.true_term)::acc_unify),
		canonical_process proc2 acc_unify,occ)
      end
  | Phase(n,proc,occ) -> Phase(n,canonical_process proc acc_unify,occ)
  | Barrier _ | AnnBarrier _ ->
     Parsing_helper.internal_error "Barriers should not appear here (9)"

(****** Normalisation ******)

(* Check if some term [t] in the process satisfies [f t] *)

let rec exists_term_P f p =
  (List.exists (fun (b,t) -> f t) p.seq_lets) ||
  (exists_term_D f p.seq_cond)

and exists_term_D f = function
    IfNorm(t,p1,p2) ->
      (f t) || (exists_term_D f p1) || (exists_term_D f p2)
  | NormProc(q) -> exists_term_Q f q

and exists_term_Q f (rlist, popt) =
  (List.exists (exists_term_R f) rlist) ||
  (match popt with
    None -> false
  | Some p -> exists_term_Repl f p)

and exists_term_Repl f p =
  (List.exists (fun (b,t) -> f t) p.r_seq_lets) ||
  (exists_term_Q f p.r_proc)

and exists_term_R f = function
    InNorm(t,x,p,_) -> (f t) || (exists_term_P f p)
  | OutNorm(t1,t2,q) -> (f t1) || (f t2) || (exists_term_Q f q)
  | EventNorm(t,q) -> (f t) || (exists_term_Q f q)
  | InsertNorm(t, q) -> (f t) || (exists_term_Q f q)
  | GetNorm(x,t,p1,p2,_) -> (f t) || (exists_term_P f p1) || (exists_term_P f p2)
  | LetFilterNorm(Pred(_,args),p1,p2,_) -> List.exists f args || (exists_term_P f p1) || (exists_term_P f p2)
  | PhaseNorm(n,r) -> exists_term_R f r

(* Apply [f] to each subprocess of a decision tree *)

let rec map_D f = function
    IfNorm(t, p1,p2) -> IfNorm(t, map_D f p1, map_D f p2)
  | NormProc(p) -> NormProc(f p)

(* Check if some subprocess [p] of a decision tree
   satisfies [f p] *)

let rec exists_D f = function
    IfNorm(t,p1,p2) -> (exists_D f p1) || (exists_D f p2)
  | NormProc(p) -> f p

(* Remove names and lets to avoid duplicates *)

let rec remove_names names = function
  | [] -> []
  | (a,args)::rest ->
      let rest' = remove_names names rest in
      try
	let args0 = List.assq a names in
	assert(args == args0);
	rest'
      with Not_found ->
	(a,args)::rest'

let union_names names names' = names @ (remove_names names names')

let rec remove_lets lets = function
  | [] -> []
  | (b,t)::rest ->
      let rest' = remove_lets lets rest in
      try
	let t0 = List.assq b lets in
	assert (Terms.equal_terms t t0);
	rest'
      with Not_found ->
	(b,t)::rest'

let union_lets lets lets' = lets @ (remove_lets lets lets')

let rec remove_lets_names_P lets names p =
  { seq_names = remove_names names p.seq_names;
    seq_lets = remove_lets lets p.seq_lets;
    seq_cond = remove_lets_names_D lets names p.seq_cond }

and remove_lets_names_D lets names = function
  | IfNorm(t, p1, p2) ->
      IfNorm(t, remove_lets_names_D lets names p1,
	     remove_lets_names_D lets names p2)
  | NormProc q ->
      NormProc(remove_lets_names_Q lets names q)

and remove_lets_names_Q lets names (rl, replopt) =
  (List.map (remove_lets_names_R lets names) rl,
   match replopt with
   | None -> None
   | Some repl -> Some (remove_lets_names_Repl lets names repl))

and remove_lets_names_Repl lets names r =
  { r_seq_names = remove_names names r.r_seq_names;
    r_seq_lets = remove_lets lets r.r_seq_lets;
    r_proc = remove_lets_names_Q lets names r.r_proc }

and remove_lets_names_R lets names = function
  | InNorm(t,b,p,precise)->
      InNorm(t,b,remove_lets_names_P lets names p,precise)
  | OutNorm(t1,t2,p) ->
      OutNorm(t1,t2,remove_lets_names_Q lets names p)
  | EventNorm(t,p) ->
      EventNorm(t,remove_lets_names_Q lets names p)
  | InsertNorm(t,p) ->
      InsertNorm(t,remove_lets_names_Q lets names p)
  | GetNorm(b,t,p1,p2,precise) ->
      GetNorm(b,t,remove_lets_names_P lets names p1,
	      remove_lets_names_P lets names p2,precise)
  | LetFilterNorm(f,p1,p2,precise) ->
      LetFilterNorm(f,remove_lets_names_P lets names p1,
		    remove_lets_names_P lets names p2,precise)
  | PhaseNorm(n,p) ->
      PhaseNorm(n,remove_lets_names_R lets names p)
    
		     
(* Normalization of replication: several helper functions *)

(* Renaming of terms *)

let rec rename_term subst_var subst_names = function
    Var x ->
      begin
	try
	  Var (List.assq x subst_var)
	with Not_found ->
	  Var x
      end
  | FunApp(f, []) ->
      begin
	try
	  FunApp (List.assq f subst_names, [])
	with Not_found ->
	  FunApp(f, [])
      end
  | FunApp(f, l) -> FunApp(f, List.map (rename_term subst_var subst_names) l)

(* Renaming of a sequence of lets. The terms are renamed, and at the
   same time new variables are created to store them. *)

let rec rename_lets subst_vars subst_names = function
    [] -> []
  | ((b,t)::l) ->
      let b' = Terms.copy_var ~orig:false b in
      let t' = rename_term subst_vars subst_names t in
      (b',t')::(rename_lets ((b,b')::subst_vars) subst_names l)

(* Renaming of normalized processes *)

let rec rename_P subst_vars subst_names p =
  { seq_names = p.seq_names;
    seq_lets = List.map (fun (b,t) -> (b, rename_term subst_vars subst_names t)) p.seq_lets;
    seq_cond = rename_D subst_vars subst_names p.seq_cond }

and rename_D subst_vars subst_names = function
    IfNorm(t,p1,p2) ->
      IfNorm(rename_term subst_vars subst_names t,
	     rename_D subst_vars subst_names p1,
	     rename_D subst_vars subst_names p2)
  | NormProc(p) ->
      NormProc(rename_Q subst_vars subst_names p)

and rename_Q subst_vars subst_names (l, popt) =
  (List.map (rename_R subst_vars subst_names) l,
   match popt with
     None -> None
   | Some p -> Some (rename_Repl subst_vars subst_names p))

and rename_Repl subst_vars subst_names p =
  { r_seq_names = p.r_seq_names;
    r_seq_lets = List.map (fun (b,t) -> (b, rename_term subst_vars subst_names t)) p.r_seq_lets;
    r_proc = rename_Q subst_vars subst_names p.r_proc }

and rename_R subst_vars subst_names = function
    InNorm(t,x,p,pr) ->
      InNorm(rename_term subst_vars subst_names t, x,
	     rename_P subst_vars subst_names p,
             pr)
  | OutNorm(t1,t2,p) ->
      OutNorm(rename_term subst_vars subst_names t1,
	      rename_term subst_vars subst_names t2,
        rename_Q subst_vars subst_names p)
  | EventNorm(t,p) ->
      EventNorm(rename_term subst_vars subst_names t,
        rename_Q subst_vars subst_names p)
  | InsertNorm(t,p) ->
      InsertNorm(rename_term subst_vars subst_names t,
		 rename_Q subst_vars subst_names p)
  | GetNorm(x,t,p1,p2,pr) ->
      GetNorm(x, rename_term subst_vars subst_names t,
	      rename_P subst_vars subst_names p1,
	      rename_P subst_vars subst_names p2,
              pr)
  | LetFilterNorm(Pred(p,args),p1,p2,pr) ->
      LetFilterNorm(Pred(p,List.map (rename_term subst_vars subst_names) args),
	      rename_P subst_vars subst_names p1,
	      rename_P subst_vars subst_names p2,
              pr)
  | PhaseNorm(n,p) ->
      PhaseNorm(n, rename_R subst_vars subst_names p)

(* [put_lets p l] adds the sequence of lets in [l] on top
   of process [p], removing the lets that are not used in [p]. *)

let rec put_lets p = function
    [] -> p
  | (x,t)::l ->
      let p' = put_lets p l in
      (* Keep only the lets in which the bound variable is used. *)
      if exists_term_Repl (Terms.occurs_var x) p' then
	{ p' with
          r_seq_lets = (x,t)::(p'.r_seq_lets)
        }
      else
	p'

(* [put_names p names] adds the sequence of new names [names]
   on top of process [p], removing the names that are not used
   in [p]. *)

let rec put_names p names =
  { p with
    (* Keep only the restrictions in which the name is used. *)
    r_seq_names = List.filter (fun (a,_) -> exists_term_Repl (Terms.occurs_f a) p) names }

(* [build_repl_cond_tree names lets cond_tree] transforms each process [p]
   inside the condition tree [cond_tree] into [! names lets p] where
   [names] is a sequence of fresh names that are created and
   [lets] is a sequence of lets.
   Furthermore, the names in [names] and variables in [lets] are
   renamed, unused names and variables are removed, and two simplifications
   are applied:
   - Remove the double replication when possible:
	       ! let x = ... in ! Q
	       becomes
               ! let x = ... in Q.
   - ! new ... let ... in 0 becomes just 0 *)

let rec build_repl_cond_tree names lets = function
    NormProc(p) ->
      begin
	let seq_names = List.map (fun (a,args) -> (rename_private_name a,args)) names in
	let subst_names = List.map2 (fun (a,_) (a',_) -> (a,a')) names seq_names in
	let seq_lets = rename_lets [] subst_names lets in
	let subst_vars = List.map2 (fun (b,_) (b',_) -> (b,b')) lets seq_lets in
	let p' = rename_Q subst_vars subst_names p in
	let repl_p = put_names (put_lets {r_seq_names = []; r_seq_lets = []; r_proc = p'} seq_lets) seq_names in
	match repl_p with
	  { r_seq_names = []; r_seq_lets = lets'; r_proc = ([],Some repl_p') } ->
	    (* Remove the double replication when possible:
	       ! let x = ... in ! Q
	       becomes
               ! let x = ... in Q *)
	    NormProc([], Some({ repl_p' with
                                r_seq_lets = check_disjoint_pair_append lets' repl_p'.r_seq_lets }))
	|	{ r_proc = ([], None) } ->
	    (* ! new ... let ... in 0 becomes just 0 *)
	    NormProc([], None)
	| _ ->
	    NormProc([], Some repl_p)
      end
  | IfNorm(t,p1,p2) ->
      IfNorm(t,
	     build_repl_cond_tree names lets p1,
	     build_repl_cond_tree names lets p2)

(* [exists_term_P_in_top_cond f p] returns true when some terms [t]
   in the top lets and conditions of [p] is such that [f t = true]. *)

let rec exists_term_P_in_top_cond f p =
  (List.exists (fun (b,t) -> f t) p.seq_lets) ||
  (exists_term_D_in_top_cond f p.seq_cond)

and exists_term_D_in_top_cond f = function
    IfNorm(t,p1,p2) ->
      (f t) || (exists_term_D_in_top_cond f p1) || (exists_term_D_in_top_cond f p2)
  | NormProc(q) -> false

(* [put_lets_top p l]  adds the sequence of lets in [l] on top
   of process [p], removing the lets that are not used in [p].
   The variables defined in [l] are supposed to be referenced only
   inside the top lets and conditions of [p], so that we do not need
   to look further inside [p]. *)

let rec put_lets_top p = function
    [] -> p
  | (x,t)::l ->
      let p' = put_lets_top p l in
      (* Keep only the lets in which the bound variable is used.
	 Given the previous renaming, the variable can be used only in
	 top lets and condition, so we optimise by not looking further in the process *)
      if exists_term_P_in_top_cond (Terms.occurs_var x) p' then
	{ p' with
          seq_lets = (x,t)::(p'.seq_lets)
        }
      else
	p'

(* [put_names_top p names] adds the sequence of new names [names]
   on top of process [p], removing the names that are not used
   in [p].
   The names in [names] are supposed to be referenced only
   inside the top lets and conditions of [p], so that we do not need
   to look further inside [p]. *)

let rec put_names_top p names =
  { p with
    (* Keep only the restrictions in which the name is used.
       Given the previous renaming, the name can be used only in
       top lets and condition, so we optimise by not looking further in the process *)
    seq_names = List.filter (fun (a,_) -> exists_term_P_in_top_cond (Terms.occurs_f a) p) names }

(* [partition_lets names vars l] returns [(l1,l2)]
   where [l1] is the sublist of the list of lets [l]
   that refer directly or indirectly to names in [names] or variables in
   [vars], [l2] contains the other elements of [l]. *)

let rec partition_lets names vars = function
    [] -> ([],[])
  | (b, t)::l ->
      if (List.exists (fun a -> Terms.occurs_f a t) names)
      || (List.exists (fun x -> Terms.occurs_var x t) vars) then
	let (l1,l2) = partition_lets names (b::vars) l in
	((b,t)::l1, l2)
      else
	let (l1,l2) = partition_lets names vars l in
	(l1, (b,t)::l2)

(* Normalization of parallel composition *)

let rec add_par q = function
    IfNorm(t, p1,p2) -> IfNorm(t, add_par q p1, add_par q p2)
  | NormProc(p) -> NormProc(par_Q p q)

and par_D proc1 = function
    IfNorm(t,p1,p2) -> IfNorm(t, par_D proc1 p1, par_D proc1 p2)
  | NormProc(q) -> add_par q proc1

and par_P proc1 proc2 =
  {
    seq_names = check_disjoint_pair_append proc1.seq_names proc2.seq_names;
    seq_lets = check_disjoint_pair_append proc1.seq_lets proc2.seq_lets;
    seq_cond = par_D proc1.seq_cond proc2.seq_cond
  }

and par_Q (procs_R1,proc_S1) (procs_R2,proc_S2) =
  (procs_R1 @ procs_R2, par_S proc_S1 proc_S2)

and par_S proc_S1 proc_S2 =
  match proc_S1,proc_S2 with
  | None, None -> None
  | Some p1, None -> Some p1
  | None,Some p2 -> Some p2
  | Some p1,Some p2 ->
      Some { r_seq_names = check_disjoint_pair_append p1.r_seq_names p2.r_seq_names;
	     r_seq_lets = check_disjoint_pair_append p1.r_seq_lets p2.r_seq_lets;
	     r_proc = par_Q p1.r_proc p2.r_proc }

(* Add the phase prefix to a normalized process *)

let put_phase phase p =
  match phase with
    None -> p
  | Some n -> PhaseNorm(n,p)

(* Main normalization function *)

(** We assume here that all pattern in proc are variables. Moreover, all [D] in [let x = D] always succeed *)
let rec norm phase proc = match proc with
  | Nil -> { seq_names = []; seq_lets = []; seq_cond = NormProc([],None) }
  | NamedProcess(_, _, p) -> norm phase p
  | Input (c,var,p,occ) ->
      let bind = match var with
        | PatVar (b) -> b
        | _ -> internal_error "[simplify.ml >> norm] The pattern should be a variable"
      in

      let next_norm_p = norm None p in
      { seq_names = []; seq_lets = []; seq_cond = NormProc([ put_phase phase (InNorm(c,bind,next_norm_p,occ.precise))],None) }

  | Output (c,t,p,_) ->
      let next_norm_p = norm None p in
      { next_norm_p with
        seq_cond = map_D (fun q -> ([put_phase phase (OutNorm(c,t,q))], None)) next_norm_p.seq_cond
      }
  | Event(t,_,p,_) ->
      let next_norm_p = norm None p in
      { next_norm_p with
        seq_cond = map_D (fun q -> ([put_phase phase (EventNorm(t,q))], None)) next_norm_p.seq_cond
      }
  | Par(p1,p2) -> par_P (norm phase p1) (norm phase p2)
  | Repl(p,_) ->
      let next_norm_p = norm phase p in

      (* Move the condition tree above the replication *)
      let (dup_lets, no_dup_lets) = partition_lets (List.map fst next_norm_p.seq_names) [] next_norm_p.seq_lets in
      let p = { seq_names = []; seq_lets = no_dup_lets;
		seq_cond = build_repl_cond_tree
		  next_norm_p.seq_names dup_lets next_norm_p.seq_cond }
      in
      put_names_top (put_lets_top p dup_lets) next_norm_p.seq_names
  | Restr(a,(args,env),p,_) ->
      let next_norm_p = norm phase p in
      if exists_term_P (Terms.occurs_f a) next_norm_p then
	{ next_norm_p with seq_names = (a,(None (*The arguments are ignored because it would be difficult to track them and they might prevent some transformations*),env))::next_norm_p.seq_names }
      else
	(* Remove the restriction when the name is not used *)
	next_norm_p
  | Let(pat,term,proc1,proc2,_) ->
      assert (proc2 = Nil);
      let next_norm_p = norm phase proc1 in

      let x = match pat with
        | PatVar x -> x
        | _ -> internal_error "[simplify.ml >> norm] It should be a variable as pattern"
      in

      if exists_term_P (Terms.occurs_var x) next_norm_p then
	{ next_norm_p with
          seq_lets = (x,term)::(next_norm_p.seq_lets)
        }
      else
	(* Remove the let when the bound variable is not used *)
	next_norm_p
  | Test (term,proc1,proc2,_) ->
      let next_norm_p = norm phase proc1
      and next_norm_p' = norm phase proc2 in

      if next_norm_p.seq_cond = NormProc([],None) && next_norm_p'.seq_cond = NormProc([],None) then
	{ seq_names = []; seq_lets = []; seq_cond = NormProc([],None) }
      else if next_norm_p.seq_lets = [] && next_norm_p'.seq_lets = [] then
	{
        seq_names = check_disjoint_pair_append next_norm_p.seq_names next_norm_p'.seq_names;
        seq_lets = [];
        seq_cond = IfNorm(term, next_norm_p.seq_cond, next_norm_p'.seq_cond)
        }
      else
	let test_v = Terms.new_var_def Param.bool_type in
	let add_let = (test_v, term) in
	let p_lets = List.map (fun (x,t) ->
	  let gtest_fun = Terms.gtest_fun x.btype in
	  let caught_fail = FunApp(Terms.glet_constant_fun x.btype,[]) in
	  (x,FunApp(gtest_fun, [Var test_v; t; caught_fail]))
	     ) next_norm_p.seq_lets
	in
	let p'_lets = List.map (fun (x,t) ->
	  let gtest_fun = Terms.gtest_fun x.btype in
	  let caught_fail = FunApp(Terms.glet_constant_fun x.btype,[]) in
	  (x,FunApp(gtest_fun, [Var test_v; caught_fail; t]))
	     ) next_norm_p'.seq_lets
	in
	{
        seq_names = check_disjoint_pair_append next_norm_p.seq_names next_norm_p'.seq_names;
        seq_lets = add_let :: (check_disjoint_pair_append p_lets p'_lets);
        seq_cond = IfNorm(Var test_v, next_norm_p.seq_cond, next_norm_p'.seq_cond)
        }
  | Insert(term,proc,_) ->
      let next_norm_p = norm None proc in
      { next_norm_p with
        seq_cond = map_D (fun q ->  ([put_phase phase (InsertNorm(term,q))],None)) next_norm_p.seq_cond
      }
  | Get(pat,term,proc1,proc2,occ) ->
      let x = match pat with
        | PatVar x -> x
        | _ -> internal_error "[simplify.ml >> norm] It should be a variable as pattern (2)"
      in
      { seq_names = []; seq_lets = []; seq_cond = NormProc([put_phase phase (GetNorm(x,term,norm None proc1,norm None proc2,occ.precise))],None) }

  | Phase(n,proc,_) ->
      begin match phase with
        | None -> norm (Some n) proc
        | Some n' when n > n' -> norm (Some n) proc
        | Some n' -> { seq_names = []; seq_lets = []; seq_cond = NormProc([],None) }
      end
  | Barrier _ | AnnBarrier _ ->
     Parsing_helper.internal_error "Barriers should not appear here (10)"
  | _ -> internal_error "Filter should not happen"

(*********************************************
               Merging process
**********************************************)

(* Helper functions for merging of replicated processes *)

(* [get_names p] returns the list of all new names created at the top of
   process [p], possibly under lets and replications. *)

let rec get_names p =
  check_disjoint_append (List.map fst p.r_seq_names)
  (match p.r_proc with
    (_,None) -> []
  | (_,Some p') -> get_names p')

(* [get_variables p] returns the list of all variables bound by let
   at the top of process [p], possibly under lets and replications. *)

let rec get_variables p =
  check_disjoint_append (List.map fst p.r_seq_lets)
  (match p.r_proc with
    (_,None) -> []
  | (_,Some p') -> get_variables p')

(* [put_some p] returns the process of type [normalised_process_Repl option]
   corresponding to the process [p] of type [normalised_process_Repl].
   In general, it is [Some p], but when [p] is [([], None)],
   it is just [None]: we simplify [!0] into [0]. *)

let put_some p =
  match p.r_proc with
    ([],None) -> None
  | _ -> Some p

(* [split_processes names variables p] splits the process [p]
   of type [normalised_process_Repl] into [(sel_p, non_sel_p)]
   when the part of the process that uses names in [names] or
   variables in [variables] is in [sel_p] and the rest is in
   [non_sel_p].

   In case a process in [sel_p] uses a name or variables
   not in [names] or [variables] and still bound inside [p],
   the resulting process [sel_p] is not well-formed. This problem
   is solved by [partition_processes_rec] below, by redoing
   the computation with added names and variables.
*)

let rec split_processes names variables p =
  let (sel_names, non_sel_names) = List.partition (fun (a,_) -> List.memq a names) p.r_seq_names in
  let (sel_lets, non_sel_lets) = List.partition (fun (b,_) -> List.memq b variables) p.r_seq_lets in
  let (listR, repl_opt) = p.r_proc in
  let (sel_R, non_sel_R) = List.partition (fun p' -> exists_term_R (fun t ->
    List.exists (fun a -> Terms.occurs_f a t) names ||
    List.exists (fun x -> Terms.occurs_var x t) variables) p') listR in
  let (sel_repl_opt, non_sel_repl_opt) =
    match repl_opt with
      None -> (None, None)
    | Some p' ->
	let sel_p', non_sel_p' = split_processes names variables p' in
	(put_some sel_p', put_some non_sel_p')
  in
  { r_seq_names = sel_names;
    r_seq_lets = sel_lets;
    r_proc = (sel_R, sel_repl_opt) },
  { r_seq_names = non_sel_names;
    r_seq_lets = non_sel_lets;
    r_proc = (non_sel_R, non_sel_repl_opt) }

(* [partition_processes_rec sel_names non_sel_names sel_variables non_sel_variables p]
   splits [p] into [sel_p, non_sel_p] such that [non_sel_p] does not use names
   and variable in [sel_names] and [sel_variables] and is the largest possible.
   In other words, [sel_p] is the smallest well-formed subprocess of [p]
   that contains all processes that use names in [sel_names] or variables in [sel_variables].
   [non_sel_names] must contain all names bound at the root of [p] and not in [sel_names].
   Similarly for variables. *)

let rec partition_processes_rec sel_names non_sel_names sel_variables non_sel_variables p =
  let (sel_p, non_sel_p) = split_processes sel_names sel_variables p in
  let (new_sel_names, new_non_sel_names) =
    List.partition (fun a -> exists_term_Repl (Terms.occurs_f a) sel_p) non_sel_names
  in
  let (new_sel_variables, new_non_sel_variables) =
    List.partition (fun x -> exists_term_Repl (Terms.occurs_var x) sel_p) non_sel_variables
  in
  if (new_sel_names != []) || (new_sel_variables != []) then
    partition_processes_rec (new_sel_names @ sel_names) new_non_sel_names
      (new_sel_variables @ sel_variables) new_non_sel_variables p
  else
    (sel_p, non_sel_p)

(* [partition_processes r p] splits [p] into [sel_p, non_sel_p] such that
   [sel_p] contains the subprocess [r] of [p] and is the smallest possible
   to be well-formed. *)

let partition_processes r p =
  let all_names = get_names p in
  let (sel_names, non_sel_names) = List.partition (fun a -> exists_term_R (Terms.occurs_f a) r) all_names in
  let all_variables = get_variables p in
  let (sel_variables, non_sel_variables) =  List.partition (fun x -> exists_term_R (Terms.occurs_var x) r) all_variables in
  if (sel_variables == []) && (sel_names == []) then
    { r_seq_names = [];
      r_seq_lets = [];
      r_proc = ([r], None) },
    { r_seq_names = p.r_seq_names;
      r_seq_lets = p.r_seq_lets;
      r_proc = let (l,popt) = p.r_proc in (remove_from r l, popt) }
  else
    partition_processes_rec sel_names non_sel_names sel_variables non_sel_variables p

(* Type of the state used internally by the function
   [merge_replP_inside] *)

type repl_merge_state =
    { merged_part_names : (funsymb * new_args) list;
      merged_part_lets : (binder * term) list;
      merged_part_proc : normalised_process_R list;
      in_group_to_merge_left : normalised_process_Q;
      in_group_to_merge_right : normalised_process_Q;
      rest_left : normalised_process_Repl;
      rest_right : normalised_process_Repl }

(* We define an exception that will express that no merging is possible between two protocols *)

exception No_Merging

(* [choose next_f [] l] calls [next_f a (l without a)] for each element
   [a] of the list [l].
   It raises [No_Merging] when the call [next_f a (l without a)] raises
   [No_Merging] for all elements [a] of [l]. *)

let rec choose next_f seen = function
    [] -> raise No_Merging
  | a::l ->
      let is_mergeable = ref false in
      begin
	try
	  next_f a (List.rev_append seen l);
	  is_mergeable := true
	with No_Merging -> ()
      end;
      begin
	try
	  choose next_f (a::seen) l;
	  is_mergeable := true
	with No_Merging -> ()
      end;
      if not (!is_mergeable) then raise No_Merging

(* [choose_g next_f p1 l], where [l] is the first component of [p1.r_proc],
   calls [next_f p1_sel p1_non_sel] for each smallest well-formed
   subgroup [p1_sel] of processes of [p1], where [p1_non_sel] is the rest
   of [p1].
   (A single element of [l] may be well-formed, when it uses a name
   or variable bound at the top of [p1] and also used by other elements
   of [l]. In this case, the group of processes must also contain
   these other processes, and the needed names and variables above
   them.) *)

let rec choose_g next_f p1 = function
    [] -> raise No_Merging
  | a::l ->
      let (p1_sel, p1_non_sel) = partition_processes a p1 in
      let is_mergeable = ref false in
      begin
	try
	  next_f p1_sel p1_non_sel;
	  is_mergeable := true
	with No_Merging -> ()
      end;
      begin
	(* It is useless to retry with a process in p1_sel,
	   since it will lead to the same partition p1_sel / p1_non_sel,
	   so we remove these processes from l *)
	let (rl,_) = p1_sel.r_proc in
	let l' = List.filter (fun r -> not (List.memq r rl)) l in
	try
	  choose_g next_f p1 l';
	  is_mergeable := true
	with No_Merging -> ()
      end;
      if not (!is_mergeable) then raise No_Merging

(* [apply_test cond t1 t2] returns a term equal to [if cond then t1 else t2],
   making some simplifications when possible. *)

let apply_test cond t1 t2 =
  if Terms.equal_terms t1 t2 then t1 else
  let ty = Terms.get_term_type t1 in
  assert (Terms.equal_types ty (Terms.get_term_type t2));
  let test = Terms.gtest_fun ty in
  match t1 with
    FunApp(test', [cond'; t1'; t2']) when test' == test && Terms.equal_terms t2' t2 ->
      FunApp(test, [FunApp(Terms.and_fun(), [cond; cond']); t1'; t2])
  | FunApp(test', [cond'; t1'; t2']) when test' == test && Terms.equal_terms t1' t2 ->
      FunApp(test, [FunApp(Terms.and_fun(), [cond; Terms.make_not cond']); t2'; t2])
  | _ ->
      match t2 with
	FunApp(test', [cond'; t1'; t2']) when test' == test && Terms.equal_terms t1 t1' ->
	  FunApp(test, [FunApp(Terms.or_fun(), [cond; cond']); t1; t2'])
      |	FunApp(test', [cond'; t1'; t2']) when test' == test && Terms.equal_terms t1 t2' ->
	  FunApp(test, [FunApp(Terms.or_fun(), [cond; Terms.make_not cond']); t1; t1'])
      |	_ ->
	  let choice_true_false = FunApp(Param.choice_fun Param.bool_type, [Terms.true_term; Terms.false_term]) in
	  if Terms.equal_terms cond choice_true_false then
	    FunApp(Param.choice_fun ty, [t1; t2])
	  else
	    FunApp(test,[cond;t1;t2])

(* Main merging functions *)

let rec merge_R cond proc1 proc2 next_f = match proc1,proc2 with
  | OutNorm(ch1,t1,q1),OutNorm(ch2,t2,q2)
      when Terms.equal_types (Terms.get_term_type ch1) (Terms.get_term_type ch2)
        && Terms.equal_types (Terms.get_term_type t1) (Terms.get_term_type t2) ->
      let ch = apply_test cond ch1 ch2
      and t = apply_test cond t1 t2 in

      merge_Q cond q1 q2 (fun proc ->
        next_f (OutNorm(ch,t,proc))
      )
  | EventNorm(FunApp(f1,args1),q1),EventNorm(FunApp(f2,args2),q2)
      when f1 == f2 && List.for_all2 (fun t1 t2 -> Terms.equal_types (Terms.get_term_type t1) (Terms.get_term_type t2)) args1 args2 ->

      let args = List.map2 (fun t1 t2 -> apply_test cond t1 t2) args1 args2 in

      merge_Q cond q1 q2 (fun proc ->
        next_f (EventNorm(FunApp(f1,args),proc))
      )
  | InNorm(ch1,x1,p1,pr1),InNorm(ch2,x2,p2,pr2)
      when Terms.equal_types (Terms.get_term_type ch1) (Terms.get_term_type ch2)
        && Terms.equal_types x1.Types.btype x2.Types.btype ->

      let type_x = x1.Types.btype in
      let y = Terms.new_var_def type_x in

      Terms.link x1 (TLink (Var y));
      Terms.link x2 (TLink (Var y));

      let new_p1 = follow_process_P p1
      and new_p2 = follow_process_P p2 in

      Terms.cleanup ();

      let ch = apply_test cond ch1 ch2 in

      merge_P cond new_p1 new_p2 (fun proc ->
        next_f (InNorm(ch,y,proc,pr1 || pr2))
      )
  | InsertNorm(t1,q1), InsertNorm(t2,q2)
      when Terms.equal_types (Terms.get_term_type t1) (Terms.get_term_type t2) ->
      let t = apply_test cond t1 t2 in

      merge_Q cond q1 q2 (fun proc ->
        next_f (InsertNorm(t,proc))
      )
  | GetNorm(x1,t1,pthen1,pelse1,pr1),GetNorm(x2,t2,pthen2,pelse2,pr2)
      when Terms.equal_types (Terms.get_term_type t1) (Terms.get_term_type t2)
        && Terms.equal_types x1.Types.btype x2.Types.btype ->

      let type_x = x1.Types.btype in

      let y = Terms.new_var_def type_x in

      Terms.link x1 (TLink (Var y));
      Terms.link x2 (TLink (Var y));

      let new_t1 = Terms.copy_term3 t1
      and new_t2 = Terms.copy_term3 t2 in

      let new_pthen1 = follow_process_P pthen1
      and new_pthen2 = follow_process_P pthen2 in

      Terms.cleanup ();

      let t = apply_test cond new_t1 new_t2 in

      merge_P cond new_pthen1 new_pthen2 (fun proc_then ->
        merge_P cond pelse1 pelse2 (fun proc_else ->
          next_f (GetNorm(y,t,proc_then,proc_else,pr1 || pr2))
        )
      )
  | LetFilterNorm(Pred(p1,args1),pthen1,pelse1,pr1),LetFilterNorm(Pred(p2,args2),pthen2,pelse2,pr2)
      when p1 == p2
        && List.for_all2 (fun t1 t2 -> Terms.equal_types (Terms.get_term_type t1) (Terms.get_term_type t2)) args1 args2 ->

      let args = List.map2 (apply_test cond) args1 args2 in

      merge_P cond pthen1 pthen2 (fun proc_then ->
        merge_P cond pelse1 pelse2 (fun proc_else ->
          next_f (LetFilterNorm(Pred(p1,args),proc_then,proc_else,pr1 || pr2))
        )
      )
  | PhaseNorm(n1,p1),PhaseNorm(n2,p2) when n1 = n2 ->
      merge_R cond p1 p2 (fun proc ->
        next_f (PhaseNorm(n1,proc))
      )
  | _,_ ->
    raise No_Merging

(* [merge_all_list_R cond procs_R1 seen_R2 procs_R2 next_f]
   merges the first element of [procs_R1] with an element of [procs_R2]
   and the other elements of [procs_R1] with elements of [seen_R2 + procs_R2],
   then calls [next_f] with the merged list.

   In particular,
   [merge_all_list_R cond procs_R1 [] procs_R2 next_f]
   merges the elements of [procs_R1] with elements of [procs_R2],
   then calls [next_f] with the merged list. *)

and merge_all_list_R cond procs_R1 seen_R2 procs_R2 next_f =
  match procs_R1,procs_R2 with
  | [],[] -> assert(seen_R2 == []); next_f []
  | [],_  -> internal_error "[simplify.ml >> merge_all_list_R] Both lists should be of equal length"
  | _ ,[] ->
      (* We tried to merge the first element of [procs_R1] with all elements of the other side,
         which are now all in [seen_R2], since [proc_R2] is empty. The merging fails. *)
      raise No_Merging
  | p1::l1,p2::l2 ->
      let is_mergeable = ref false in
      begin
	try
	  (* try merging p1 and p2, then merging the rest, that is,
	     l1 with seen_R2 + l2 *)
	  merge_R cond p1 p2 (fun proc ->
            merge_all_list_R cond l1 [] (List.rev_append seen_R2 l2) (fun proc_l ->
              next_f (proc::proc_l)
		)
	      );
	  is_mergeable := true
	with No_Merging -> ()
      end;
      begin
	try
	  (* try merging p1 with an element of l2, then merging
	     the rest *)
	  merge_all_list_R cond procs_R1 (p2::seen_R2) l2 next_f;
	  is_mergeable := true
	with No_Merging -> ()
      end;
      if not (!is_mergeable) then raise No_Merging

and merge_Q cond (procs_R1,proc_S1) (procs_R2,proc_S2) next_f =
  if List.length procs_R1 = List.length procs_R2
  then
    merge_all_list_R cond procs_R1 [] procs_R2 (fun procs_R ->
      merge_replP cond proc_S1 proc_S2 (fun proc_S ->
        next_f (procs_R,proc_S)
          )
        )
  else raise No_Merging


and merge_replP cond p1opt p2opt next_f =
  match p1opt, p2opt with
    None, None -> next_f None
  | Some _, None | None, Some _ -> raise No_Merging
  | Some p1, Some p2 ->
      match p1.r_proc, p2.r_proc with
	([],r1),([],r2) ->
	  merge_replP cond r1 r2 (fun merged_r ->
	    let names = union_names p1.r_seq_names p2.r_seq_names in
	    let lets = union_lets p1.r_seq_lets p2.r_seq_lets in
	    next_f (put_some {
	    r_seq_names = names;
            r_seq_lets = lets;
	    r_proc = remove_lets_names_Q lets names ([],merged_r)
	  }))
      | ([],r1),_ ->
	  merge_replP cond r1 p2opt (fun merged_r ->
	    next_f (put_some {
	    r_seq_names = p1.r_seq_names;
            r_seq_lets = p1.r_seq_lets;
	    r_proc = remove_lets_names_Q p1.r_seq_lets p1.r_seq_names ([],merged_r)
	  }))
      | _,([],r2) ->
	  merge_replP cond p1opt r2 (fun merged_r ->
	    next_f (put_some {
	    r_seq_names = p2.r_seq_names;
            r_seq_lets = p2.r_seq_lets;
	    r_proc = remove_lets_names_Q p2.r_seq_lets p2.r_seq_names ([],merged_r)
	  }))
      | (l1,_),_ ->
	  choose_g (fun p1_sel p1_non_sel ->
	    let state =
	      { merged_part_names = p1_sel.r_seq_names;
		merged_part_lets = p1_sel.r_seq_lets;
		merged_part_proc = [];
		in_group_to_merge_left = p1_sel.r_proc;
		in_group_to_merge_right = ([],None);
		rest_left = p1_non_sel;
		rest_right = remove_lets_names_Repl p1_sel.r_seq_lets p1_sel.r_seq_names p2 }
	    in
	    merge_replP_inside cond state next_f
	      ) p1 l1

and merge_replP_inside cond state next_f =
  match state.in_group_to_merge_left, state.in_group_to_merge_right with
    ([],repl1),([],repl2) ->
      (* We have finished merging a coherent group of non-replicated
	 processes. Add a replication over the rest, and continue *)
      merge_replP cond (par_S (put_some state.rest_left) repl1)
	(par_S (put_some state.rest_right) repl2) (fun merged_r ->
	next_f (put_some {
	  r_seq_names = state.merged_part_names;
	  r_seq_lets = state.merged_part_lets;
	  r_proc = (state.merged_part_proc, merged_r)
        }))
  | (a1::l1, repl1), ([], repl2) ->
      (* There is at least one non-replicated process on the left-hand side,
         a1, but no non-replicated process in the currently selected group
         on the right-hand side. Select a new process to merge with
         a1, add its group, and continue *)
      choose (fun a2 _ ->
	merge_R cond a1 a2 (fun merged_a ->
	  let (sel2, non_sel2) = partition_processes a2 state.rest_right in
	  let (l2,repl2') = sel2.r_proc in
	  let l2_to_merge = remove_from a2 l2 in
	  let state' =
	  { merged_part_names = union_names sel2.r_seq_names state.merged_part_names;
            merged_part_lets = union_lets sel2.r_seq_lets state.merged_part_lets;
            merged_part_proc = List.map (remove_lets_names_R sel2.r_seq_lets sel2.r_seq_names) (merged_a::state.merged_part_proc);
	    in_group_to_merge_left = remove_lets_names_Q sel2.r_seq_lets sel2.r_seq_names (l1,repl1);
	    in_group_to_merge_right = remove_lets_names_Q sel2.r_seq_lets sel2.r_seq_names (l2_to_merge,par_S repl2 repl2');
	    rest_left = remove_lets_names_Repl sel2.r_seq_lets sel2.r_seq_names state.rest_left;
	    rest_right = non_sel2
	  }
	  in
	  merge_replP_inside cond state' next_f
	  )
	) [] (fst state.rest_right.r_proc)
  | (l1, repl1), (a2::l2, repl2) ->
      (* There is at least one non-replicated process on the right-hand side,
         a2. Try to merge it with an element of l1, if possible.
	 Otherwise, select a new process in rest_left to merge with a2,
	 add its group, and continue *)
      let is_mergeable = ref false in
      begin
	try
	  choose (fun a1 rest1 ->
	    merge_R cond a1 a2 (fun merged_a ->
	      let state' =
		{ state with
	          merged_part_proc = merged_a::state.merged_part_proc;
	          in_group_to_merge_left = (rest1, repl1);
	          in_group_to_merge_right = (l2, repl2)
                }
	      in
	      merge_replP_inside cond state' next_f
		)
	    ) [] l1;
	  is_mergeable := true
	with No_Merging -> ()
      end;
      begin
	try
	  choose (fun a1 _ ->
	    merge_R cond a1 a2 (fun merged_a ->
	      let (sel1, non_sel1) = partition_processes a1 state.rest_left in
	      let (l1',repl1') = sel1.r_proc in
	      let l1_to_merge = remove_from a1 l1' in
	      let state' =
		{ merged_part_names = union_names sel1.r_seq_names state.merged_part_names;
		  merged_part_lets = union_lets sel1.r_seq_lets state.merged_part_lets;
		  merged_part_proc = List.map (remove_lets_names_R sel1.r_seq_lets sel1.r_seq_names) (merged_a::state.merged_part_proc);
		  in_group_to_merge_left = remove_lets_names_Q sel1.r_seq_lets sel1.r_seq_names (l1_to_merge @ l1,par_S repl1 repl1');
		  in_group_to_merge_right = remove_lets_names_Q sel1.r_seq_lets sel1.r_seq_names (l2,repl2);
		  rest_left = non_sel1;
		  rest_right = remove_lets_names_Repl sel1.r_seq_lets sel1.r_seq_names state.rest_right
		}
	      in
	      merge_replP_inside cond state' next_f
		)
	      ) [] (fst state.rest_left.r_proc);
	  is_mergeable := true
	with No_Merging -> ()
      end;
      if not (!is_mergeable) then raise No_Merging

(* This is an old simple code for merging replicated
   processes, by just keeping the structure, without
   adding double replications.
and merge_replP cond p1 p2 next_f =
    merge_Q cond p1.r_proc p2.r_proc (fun merged_Q ->
      next_f {
        r_seq_names = p1.r_seq_names @ p2.r_seq_names;
        r_seq_lets = p1.r_seq_lets @ p2.r_seq_lets;
        r_proc = merged_Q
      })
*)

and merge_P cond proc_1 proc_2 next_f =
  next_f {
    seq_names = union_names proc_1.seq_names proc_2.seq_names;
    seq_lets = union_lets proc_1.seq_lets proc_2.seq_lets;
    seq_cond = IfNorm(cond, remove_lets_names_D proc_2.seq_lets proc_2.seq_names proc_1.seq_cond,
		    remove_lets_names_D proc_1.seq_lets proc_1.seq_names proc_2.seq_cond)
  }

(* Mergebranches *)

let rec filter_dead_D acc_unify = function
    IfNorm(cond, p1, p2) ->
      if is_term_always_false cond acc_unify then
	filter_dead_D acc_unify p2
      else if is_term_always_true cond acc_unify then
	filter_dead_D acc_unify p1
      else
	IfNorm(cond, filter_dead_D ((cond, Terms.true_term)::acc_unify) p1,
	             filter_dead_D ((cond, Terms.false_term)::acc_unify) p2)
  | NormProc(p) -> NormProc(p)

(* [select_leaf_D accu_cond context next_f p]
   selects one leaf [q] of [p] and calls [next_f cond_list q rest].
   [accu_cond] is the list of conditions that must hold to reach [p].
   [context] is a function that puts the context of [p] around its argument.
   [cond_list] is the list of conditions that must hold to reach the leaf [q].
   [rest] is the process [p] and its context with the leaf [q] removed.

   [select_leaf_D [] (fun p -> p) next_f p]
   selects one leaf [q] of [p] and calls [next_f cond_list q rest]
   where [p] is equivalent to [if cond_list then q else rest].
*)

let rec select_leaf_D accu_cond context next_f = function
    IfNorm(cond, p1, p2) ->
      begin
	try
	  match p1 with
	    NormProc(q) ->
	    (* The input process is equivalent to
	       if (cond::accu_cond) then q else (context p2)
	       Try merging q with some other process. *)
	      next_f (cond::accu_cond) q (context p2)
	  | _ ->
	    (* Look into the leaves of p1 *)
	      select_leaf_D (cond::accu_cond) (fun p_hole -> context(IfNorm(cond, p_hole, p2))) next_f p1
	with No_Merging ->
	  match p2 with
	    NormProc(q) ->
	    (* The input process is equivalent to
	       if (not cond::accu_cond) then q else (context p1)
	       Try merging q with some other process. *)
	      next_f ((Terms.make_not cond)::accu_cond) q (context p1)
	  | _ ->
	    (* Look into the leaves of p2 *)
	      select_leaf_D ((Terms.make_not cond)::accu_cond) (fun p_hole -> context(IfNorm(cond, p1, p_hole))) next_f p2
      end
  | NormProc(p) ->
      Parsing_helper.internal_error "Should not reach the leaves"

(* [find_remove_elem a l] returns
   [None] when [a] is not in [l] and
   [Some l'] when [a] is in [l] and [l'] is [l] with [a] removed (once) *)

let rec find_remove_elem a = function
    [] -> None
  | a'::l ->
      if Terms.equal_terms a a' then
	Some l
      else
	match find_remove_elem a l with
	  None -> None
	| Some l' -> Some (a'::l')

(* [intersect l1 l2] returns [(common, l1 minus common, l2 minus common)]
   where [common] is the intersect of the lists [l1] and [l2]. *)

let rec intersect l1 = function
    [] -> ([], l1, [])
  | a::l ->
      match find_remove_elem a l1 with
	None ->
	  let (common, restl1, restl2) = intersect l1 l in
	  (common, restl1, a::restl2)
      |	Some l1' ->
	  let (common, restl1, restl2) = intersect l1' l in
	  (a::common, restl1, restl2)

(* [or_and cond cond_list1 cond_list2] returns a term equal to
   (cond && cond_list1) || ((not cond) && cond_list2) after making some
   simplifications *)

let or_and cond cond_list1 cond_list2 =
  let (common, rest1, rest2) = intersect cond_list1 cond_list2 in
  (* The condition is equal to (common && ((cond && rest1) || ((not cond) && rest2))) *)
  let choice_true_false = FunApp(Param.choice_fun Param.bool_type, [Terms.true_term; Terms.false_term]) in
  if Terms.equal_terms cond choice_true_false then
    Terms.and_list ((FunApp(Param.choice_fun Param.bool_type, [Terms.and_list rest1; Terms.and_list rest2]))::common)
  else
    if rest1 = [] then
      if rest2 = [] then
	Terms.and_list common
      else
	Terms.and_list ((FunApp(Terms.or_fun(), [cond; Terms.and_list rest2]))::common)
    else
      if rest2 = [] then
	Terms.and_list ((FunApp(Terms.or_fun(), [Terms.make_not cond; Terms.and_list rest1]))::common)
      else
	let test = Terms.gtest_fun Param.bool_type in
	Terms.and_list ((FunApp(test, [cond; Terms.and_list rest1; Terms.and_list rest2]))::common)

(* A version of [merge_Q] that sets [simplif_done]
   when the merging has been done. *)

let merge_Q cond q1 q2 next_f =
  merge_Q cond q1 q2 (fun q_proc ->
    let old_simplif_done = !simplif_done in
    simplif_done := true;
    next_f q_proc;
    simplif_done := old_simplif_done)

(* [merge_2_D next_f cond p1 p2] tries merging each leaf of [p1] with a leaf of [p2].
   A merging that succeeds is not undone when future mergings fail.
   [merge_2_D next_f cond p1 p2] starts from a process
   [if cond then p1 else p2] and calls [next_f] with a process
   equivalent to that process after merging.

   [next_f] should never raise No_Merging;
   [merge_2_D] never raises No_Merging *)
let rec merge_2_D next_f cond p1 p2 =
  try
    match p1, p2 with
      NormProc(q1), NormProc(q2) ->
	merge_Q cond q1 q2 (fun q_proc -> next_f (NormProc(q_proc)))
    | NormProc(q1), _ ->
	(* Try merging q1 with one leaf of p2 *)
	select_leaf_D [] (fun p -> p) (fun cond_list q2 rest ->
	  merge_Q cond q1 q2 (fun q_proc -> next_f (IfNorm(FunApp(Terms.or_fun(), [cond; Terms.and_list cond_list]), NormProc(q_proc), rest)))) p2
    | _, NormProc(q2) ->
	(* Try merging q2 with one leaf of p1 *)
	select_leaf_D [] (fun p -> p) (fun cond_list q1 rest ->
	  merge_Q cond q1 q2 (fun q_proc -> next_f (IfNorm(FunApp(Terms.and_fun(), [cond; Terms.or_not_list cond_list]), rest, NormProc(q_proc))))) p1
    | _,_ ->
	(* Try merging each leaf of p1 with a leaf of p2
	   A merging that succeeds is not undone when future mergings fail *)
	select_leaf_D [] (fun p -> p) (fun cond_list1 q1 rest1 ->
	  select_leaf_D [] (fun p -> p) (fun cond_list2 q2 rest2 ->
	    merge_Q cond q1 q2 (fun q_proc ->
	      let cond_q_proc = or_and cond cond_list1 cond_list2 in
	      merge_2_D (fun p' -> next_f (IfNorm(cond_q_proc, NormProc(q_proc), p'))) cond rest1 rest2
		)
	      ) p2
	    ) p1
  with No_Merging ->
    next_f (IfNorm(cond, p1, p2))

(* next_f should never raise No_Merging *)
let rec merge_leaves_D next_f = function
    IfNorm(cond, p1, p2) ->
      merge_leaves_D (fun p1' ->
	merge_leaves_D (fun p2' ->
	  merge_2_D next_f cond p1' p2'
	  ) p2
	) p1
  | NormProc(p) -> next_f (NormProc(p))


let rec mergebranches_P process acc_unify next_f  =
  let acc_unify' = (List.map (fun (b,t) -> (Var b,t)) process.seq_lets)@acc_unify in
  let seq_cond_1 = filter_dead_D acc_unify' process.seq_cond in
  merge_leaves_D (mergebranches_D acc_unify' (fun seq_cond1' -> next_f { process with seq_cond = seq_cond1' })) seq_cond_1

and mergebranches_D acc_unify next_f = function
    NormProc(q) -> mergebranches_Q q acc_unify (fun q' -> next_f (NormProc(q')))
  | IfNorm(cond,p1,p2) ->
      if (!reject_choice_true_false) &&
	(let choice_true_false = FunApp(Param.choice_fun Param.bool_type, [Terms.true_term; Terms.false_term]) in
	 Terms.equal_terms cond choice_true_false) then
	(* Reject a process that still contains choice[true,false]
	   as condition: it is very likely that we will not be able to
	   prove observational equivalence for this process. *)
	()
      else
	mergebranches_D ((cond, Terms.true_term)::acc_unify) (fun p1' ->
	  mergebranches_D ((cond, Terms.false_term)::acc_unify) (fun p2' ->
	    next_f (IfNorm(cond, p1', p2'))
	      ) p2
	    ) p1

and mergebranches_Q (procs_R,proc_P) acc_unify next_f = match proc_P with
  | None ->
      mergebranches_R_list procs_R acc_unify (fun procs_R' ->
        next_f (procs_R',None)
      )
  | Some p ->
      mergebranches_R_list procs_R acc_unify (fun procs_R' ->
        mergebranches_Repl p acc_unify (fun p' ->
          next_f (procs_R',Some p')
        )
      )

and mergebranches_Repl process acc_unify next_f  =
  let acc_unify' = (List.map (fun (b,t) -> (Var b,t)) process.r_seq_lets)@acc_unify in
  mergebranches_Q process.r_proc acc_unify' (fun q' -> next_f { process with r_proc = q' })

and mergebranches_R_list procs_R acc_unify next_f = match procs_R with
  | [] -> next_f []
  | r::r_liste ->
      mergebranches_R r acc_unify (fun r' ->
        mergebranches_R_list r_liste acc_unify (fun r_liste' ->
          next_f (r'::r_liste')
        )
      )

and mergebranches_R proc_R acc_unify next_f = match proc_R with
  | InNorm(ch,x,p,pr) -> mergebranches_P p acc_unify (fun p' -> next_f (InNorm(ch,x,p',pr)))
  | OutNorm(ch,t,q) -> mergebranches_Q q acc_unify (fun q' -> next_f (OutNorm(ch,t,q')))
  | EventNorm(t,q) -> mergebranches_Q q acc_unify (fun q' -> next_f (EventNorm(t,q')))
  | InsertNorm(t,q) -> mergebranches_Q q acc_unify (fun q' -> next_f (InsertNorm(t,q')))
  | GetNorm(x,t,pthen,pelse,pr) ->
      mergebranches_P pthen acc_unify (fun pthen' ->
        mergebranches_P pelse acc_unify (fun pelse' ->
          next_f (GetNorm(x,t,pthen',pelse',pr))
        )
      )
  | LetFilterNorm(fact,pthen,pelse,pr) ->
      mergebranches_P pthen acc_unify (fun pthen' ->
        mergebranches_P pelse acc_unify (fun pelse' ->
          next_f (LetFilterNorm(fact,pthen',pelse',pr))
        )
      )
  | PhaseNorm(n,r) -> mergebranches_R r acc_unify (fun r' -> next_f (PhaseNorm(n,r')))


(*********************************************
               Get process
**********************************************)

(* [get_proc_P proc] transforms a normalized process into
   a standard ProVerif process. *)

let rec get_names next_proc = function
  | [] -> next_proc
  | (a,args)::q -> Restr (a,args,get_names next_proc q,new_occurrence ())

let rec get_lets next_proc = function
  | [] -> next_proc
  | (x,t)::q -> Let (PatVar x,t,get_lets next_proc q,Nil,new_occurrence ())

let rec get_proc_P proc =
  get_names (get_lets (get_proc_D proc.seq_cond) proc.seq_lets) proc.seq_names

and get_proc_D = function
    IfNorm(cond,p1,p2) -> Test(cond,get_proc_D p1, get_proc_D p2,  new_occurrence ())
  | NormProc(q) -> get_proc_Q q

and get_proc_Q (procs_R,proc_P) =
  match proc_P with
    | None ->
        List.fold_right (fun proc_r acc ->
          if acc = Nil
          then get_proc_R proc_r
          else Par(get_proc_R proc_r,acc)
        ) procs_R Nil
    | Some p ->
        List.fold_right (fun proc_r acc ->
          Par(get_proc_R proc_r,acc)
        ) procs_R (Repl(get_proc_Repl p,new_occurrence ()))

and get_proc_Repl proc =
  get_names (get_lets (get_proc_Q proc.r_proc) proc.r_seq_lets) proc.r_seq_names

and get_proc_R = function
  | InNorm(ch,x,p,pr) -> Input(ch, PatVar x, get_proc_P p,new_occurrence ~precise:pr ())
  | OutNorm(ch,t,q) -> Output(ch, t, get_proc_Q q,new_occurrence ())
  | EventNorm(t,q) -> Event(t,(None, Stringmap.StringMap.empty),get_proc_Q q,new_occurrence ())
  | InsertNorm(t,q) -> Insert(t,get_proc_Q q,new_occurrence ())
  | GetNorm(x,t,pthen,pelse,pr) -> Get(PatVar x, t, get_proc_P pthen, get_proc_P pelse,new_occurrence ~precise:pr ())
  | LetFilterNorm(fact,pthen,pelse,pr) -> LetFilter([],fact, get_proc_P pthen, get_proc_P pelse,new_occurrence ~precise:pr ())
  | PhaseNorm(n,r) -> Phase(n,get_proc_R r,new_occurrence ())


(*******************************************************
   [verify_process [] proc] verifies that the process [proc] is closed.
   It is useful as a sanity check on the final processes after simplification or merging
 *******************************************************)

let rec verify_term free_var = function
  | Var v ->
      if not (List.memq v free_var)
      then
        begin
          Display.Text.display_term2 (Var v);
          internal_error "The previous variable is not declared:\n"
        end;
  |FunApp(_,l) -> List.iter (verify_term free_var) l

let verify_fact free_var = function
  | Pred(_,args) -> List.iter (verify_term free_var) args

let rec verify_pattern free_var = function
  | PatVar(x) -> [x]
  | PatTuple(_,l) -> List.concat (List.map (verify_pattern free_var) l)
  | PatEqual(t) -> verify_term free_var t; []

let rec verify_process free_var proc =
  match proc with
  | Nil -> ()
  | NamedProcess(_, tl, p) ->
      List.iter (fun x -> verify_term free_var x) tl;
      verify_process free_var p
  | Par(p1,p2) -> verify_process free_var p1;
      verify_process free_var p2
  | Repl(p,_) -> verify_process free_var p
  | Restr(_,_,p,_) -> verify_process free_var p
  | Test(t,p1,p2,_) ->
      verify_term free_var t;
      verify_process free_var p1;
      verify_process free_var p2
  | Input(t,pat,p,_) ->
      let binders = verify_pattern free_var pat in

      verify_term free_var t;
      verify_process (binders@free_var) p
  | Output(t1,t2,p,_) ->
      verify_term free_var t1;
      verify_term free_var t2;
      verify_process free_var p
  | Let(pat,t,p1,p2,_) ->
      let binders = verify_pattern free_var pat in

      verify_term free_var t;
      verify_process (binders@free_var) p1;
      verify_process free_var p2
  | Phase(_, proc,_) -> verify_process free_var proc
  | Barrier _ | AnnBarrier _ ->
     Parsing_helper.internal_error "Barriers should not appear here (11)"
  | LetFilter([],fact,p1,p2,_) ->
      verify_fact free_var fact;
      verify_process free_var p1;
      verify_process free_var p2
  | LetFilter(_,_,_,_,_) -> input_error "verify_process does not support LetFilter in the process" dummy_ext
  | Event(t,_,p,_) | Insert(t, p, _) ->
      verify_term free_var t;
      verify_process free_var p

  | Get(pat, t, p, q, _) ->
      let binders = verify_pattern free_var pat in
      let new_free_var = binders @ free_var in

      verify_term new_free_var t;
      verify_process new_free_var p;
      verify_process new_free_var q

(*********************************************
               Simplify process
**********************************************)
(** [simplify_process] is not a deterministic function:
    [simplify_process process next_f] calls [next_f p]
    for each simplified process [p] obtained from the initial
    process [process] *)

let simplify_process process next_f =
  simplif_done := false;
  let cano_proc = canonical_process process [] in
  (*print_string "Canonical process:\n";
  Display.Text.display_process "" cano_proc;*)

  let norm_proc = norm None cano_proc in

  (*print_string "Normalized process before merging:\n";
  display_norm_P "" norm_proc;*)

  mergebranches_P norm_proc [] (fun norm_proc' ->
    if (!simplif_done) || (not (!Param.reject_no_simplif)) then
      begin
	(*print_string "Normalized process after merging:\n";
	display_norm_P "" norm_proc';*)
	let simp_proc = get_proc_P norm_proc' in
	next_f simp_proc
      end
  )

(*********************************************
           State : handles both the case
	   of simplification of a process and
           transformation of a biprocess into a process
**********************************************)

let simplify_state state next_f =
  let process_desc, query =
    match state.pi_process_query with
      SingleProcessSingleQuery(p, ((ChoiceQuery | ChoiceQEnc _) as q)) ->
	p, q
    | Equivalence(process_1, process_2) ->
	if !Param.reject_choice_true_false then
	  reject_choice_true_false := true;
	let choice_symb = Param.choice_fun Param.bool_type in
	let cond = FunApp(choice_symb,[Terms.true_term;Terms.false_term]) in
	{ proc = Test(cond,process_1.proc,process_2.proc,new_occurrence ());
	  bi_pro = true;
	  display_num = None;
	  construction = Merge(process_1, process_2) }, ChoiceQuery
    | _ ->
	Parsing_helper.internal_error "Simplify.simplify_state should be called only for equivalence or choice queries"
  in
  simplify_process process_desc.proc (fun process' ->
    let process_desc' =
      { proc = process';
	bi_pro = true;
	display_num = None;
	construction = Simplify(process_desc) }
    in
    next_f
      { state with
        pi_process_query = SingleProcessSingleQuery(process_desc', query);
        pi_glob_table = Unset;
        pi_glob_table_var_name = Unset;
        pi_terms_to_add_in_name_params = Unset;
        pi_min_choice_phase = Unset;
        pi_need_vars_in_names = Computed [];
        pi_name_args_exact = false })
