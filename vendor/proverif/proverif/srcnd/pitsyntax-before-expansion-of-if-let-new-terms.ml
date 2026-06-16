
open Parsing_helper
open Ptree
open Pitptree
open Types
open Pitypes
open Stringmap

let occ_count = ref 0

let new_occurrence () =
  incr occ_count;
  !occ_count

(* Parse a file *)

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
    user_error ("File error: " ^ s ^ "\n")

(** Types **)

let get_type_polym polym (s, ext) =
  if s = "any_type" then
    if polym then
      Param.any_type
    else
      input_error "polymorphic type not allowed here" ext
  else
  try
    List.find (fun t -> t.tname = s) (!Param.all_types)
  with Not_found -> 
    input_error ("type " ^ s ^ " not declared") ext

let get_type (s, ext) = get_type_polym false (s,ext)

let check_type_decl (s, ext) =
  if s = "any_type" then
    input_error "type any_type reserved for polymorphism" ext;
  if List.exists (fun t -> t.tname = s) (!Param.all_types) then
    input_error ("type " ^ s ^ " already declared") ext;
  Param.all_types := { tname = s } :: (!Param.all_types)

(* Global table of identifiers, including names, functions, variables,
   and predicates.
   Is a map from strings to the description of the ident *)

let global_env = ref (StringMap.empty : envElement StringMap.t)

(* Table of bound names of the process *)

let glob_table = Hashtbl.create 7

let check_single ext s =
  let vals = Hashtbl.find_all glob_table s in
  match vals with
    _::_::_ -> input_error (s ^ " cannot be used in queries. Its definition is ambiguous. (For example, several restrictions might define " ^ s ^ ".)") ext
  | _ -> ()
  


(* Functions *)
    
let fun_decls = Param.fun_decls

let true_cst =
  { f_name = "true";
    f_type = [], Param.bool_type;
    f_cat = Tuple;
    f_initial_cat = Tuple;
    f_private = false;
    f_options = 0 }

let false_cst =
  { f_name = "false";
    f_type = [], Param.bool_type;
    f_cat = Tuple;
    f_initial_cat = Tuple;
    f_private = false;
    f_options = 0 }

let not_cat = 
  Red [[FunApp(true_cst, [])], FunApp(false_cst, []); (* not(true) = false *)
       [FunApp(false_cst, [])], FunApp(true_cst, [])] (* not(false) = true *)

let not_fun =
  { f_name = "not";
    f_type = [Param.bool_type], Param.bool_type;
    f_cat = not_cat;
    f_initial_cat = not_cat;
    f_private = false;
    f_options = 0 }

let init_fun_decl () =
  Hashtbl.add fun_decls "true" true_cst;
  global_env := StringMap.add "true" (EFun true_cst) (!global_env);
  Hashtbl.add fun_decls "false" false_cst;
  global_env := StringMap.add "false" (EFun false_cst) (!global_env);
  Hashtbl.add fun_decls "not" not_fun;
  global_env := StringMap.add "not" (EFun not_fun) (!global_env)


let special_functions = ["choice"; "||"; "&&"; "="; "<>"]

let get_fun env (s,ext) tl =
  if List.mem s special_functions then
    input_error (s ^ " not allowed here") ext;
  try
    match StringMap.find s env with
      EFun r -> 
	if not (Terms.eq_lists (fst r.f_type) tl) then
	  input_error ("function " ^ s ^ " expects arguments of type " ^ 
		       (Terms.tl_to_string ", " (fst r.f_type)) ^
		       " but is given arguments of type " ^
		       (Terms.tl_to_string ", " tl)) ext;
	r
    | _ ->
	input_error (s ^ " should be a function") ext
  with Not_found ->
    input_error ("function " ^ s ^ " not defined") ext

let check_fun_decl (name, ext) argtypes restype options =
  let tyarg = List.map get_type argtypes in
  let tyres = get_type restype in
  if StringMap.mem name (!global_env) then
    input_error ("identifier " ^ name ^ " already defined (as a free name, a function, or a predicate)") ext;
  let is_tuple = ref false in
  let is_private = ref false in
  let opt = ref 0 in
  List.iter (function 
	("data",_) -> is_tuple := true
      |	("private",_) -> is_private := true
      |	("typeConverter",_) -> 
	  if List.length tyarg != 1 then
	    input_error "only unary functions can be declared \"typeConverter\"" ext;
	  opt := (!opt) lor Param.fun_TYPECONVERTER
      |	(_,ext) ->
	input_error "for functions, the only allowed options are data, private, and typeConverter" ext) options;
  let cat = if !is_tuple (* || ((arity == 0) && (not is_private)) *) then Tuple else Eq [] in
  let r = { f_name = name;
	    f_type = tyarg, tyres;
	    f_cat = cat;
	    f_initial_cat = cat;
	    f_private = !is_private;
	    f_options = !opt }
  in
  Hashtbl.add fun_decls name r;
  global_env := StringMap.add name (EFun r) (!global_env)

let get_var env (s,ext) =
  try 
    match StringMap.find s env with
      EVar v -> v
    | _ -> input_error (s ^ " should be a variable") ext
  with Not_found -> 
    input_error ("variable " ^ s ^ " not declared") ext

let add_env env l =
  let env_ref = ref env in
  List.iter (fun ((s,ext),ty) ->
      let t = get_type ty in
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

let create_env l = 
  add_env (!global_env) l

let f_eq_tuple f ext =
  match f.f_cat with
    Eq _ | Tuple -> ()
  | _ -> input_error ("function " ^ f.f_name ^ " has been defined by reduction. It should not appear in equations or clauses") ext

let f_any f ext = ()

let rec check_eq_term f_allowed env (term,ext) = 
  match term with
    (PIdent (s,ext)) -> 
      let t = 
	try 
	  match StringMap.find s env with
	    EVar v -> Var v
	  | EFun f -> 
	      if fst f.f_type <> [] then 
		input_error ("function " ^ s ^ " expects " ^ 
			     (string_of_int (List.length (fst f.f_type))) ^
			     " arguments but is used without arguments") ext;
	      f_allowed f ext;
	      FunApp(f, [])
	  | _ -> input_error ("identifier " ^ s ^ " should be a function or a variable") ext
	with Not_found -> 
	  input_error ("identifier " ^ s ^ " not defined as a function or as a variable") ext
      in
      (t, Terms.get_term_type t)
  | (PFunApp ((f,ext), tlist)) ->
      let (tl', tyl) = List.split (List.map (check_eq_term f_allowed env) tlist) in
      let f' = get_fun env (f,ext) tyl in
      f_allowed f' ext;
      if (f'.f_options land Param.fun_TYPECONVERTER != 0) && (!Param.ignore_types) then
	match tl' with
	  [t] -> (t, snd f'.f_type)
	| _ -> internal_error "type converter functions should always be unary"
      else
	(FunApp(f', tl'), snd f'.f_type)
  | (PTuple tlist) ->
      let (tl', tyl) = List.split (List.map (check_eq_term f_allowed env) tlist) in
      (FunApp (Terms.get_tuple_fun tyl, tl'), Param.bitstring_type)


(* Equations *)

let check_equation env t1 t2 =
   let var_env = create_env env in
   let (t1', ty1) = check_eq_term f_eq_tuple var_env t1 in
   let (t2', ty2) = check_eq_term f_eq_tuple var_env t2 in
   if ty1 != ty2 then
     begin
       let ext = merge_ext (snd t1) (snd t2) in
       input_error "the two members of an equation should have the same type" ext
     end;
   TermsEq.register_equation (t1',t2')

(* Definitions of destructors by rewrite rules *)

let check_red tlist options =
  match tlist with 
    (_,(PFunApp((f,ext),l),_),_)::_ ->
      begin 
	if List.mem f special_functions then
	  input_error (f ^ " not allowed here") ext;	
        if StringMap.mem f (!global_env) then
          input_error ("identifier " ^ f ^ " already defined (as a free name, a function, or a predicate)") ext;
	let red_list, ty_red_list = List.split (List.map 
		 (function (env, (PFunApp((f',ext'),l1),_), t2) -> 
                    if f <> f' then 
                      input_error ("In \"reduc\", all rewrite rules should begin with the same function " ^ f) ext';
                    let var_env = create_env env in
                    let ((lhs, tylhs), (rhs, tyrhs)) = (List.split (List.map (check_eq_term f_eq_tuple var_env) l1), 
							check_eq_term f_eq_tuple var_env t2)
		    in
		    let var_list_rhs = ref [] in
		    Terms.get_vars var_list_rhs rhs;
		    if not (List.for_all (fun v -> List.exists (Terms.occurs_var v) lhs) (!var_list_rhs)) then
		      Parsing_helper.input_error "All variables of the right-hand side of a \"reduc\" definition\nshould also occur in the left-hand side." ext';
		    (lhs, rhs), (tylhs, tyrhs)
                | _, (_, ext1), _ -> input_error ("In \"reduc\", all rewrite rules should begin with function application") ext1) tlist)
	in
	match ty_red_list with
	  [] -> internal_error "reduction with empty list"
	| (tylhs,tyrhs)::r ->
	    List.iter (fun (tylhs',tyrhs') ->
	      if not ((Terms.eq_lists tylhs tylhs') && tyrhs == tyrhs') then
		input_error ("the arguments of function " ^ f ^ " do not have the same type in all rewrite rules") ext) r;
	    let cat = Red red_list in
	    let is_private = ref false in
	    List.iter (function 
	      | ("private",_) -> is_private := true
	      | (_,ext) ->
		  input_error "for functions defined by rewrite rules, the only allowed option is private" ext) options;
            let fsymb = { f_name = f;
                          f_type = tylhs, tyrhs;
                          f_private = !is_private;
			  f_options = 0;
                          f_cat = cat;
			  f_initial_cat = cat
			}
            in
            Hashtbl.add fun_decls f fsymb;
	    global_env := StringMap.add f (EFun fsymb) (!global_env)
      end
  | (_,(_, ext1), _) :: l -> 
      input_error ("In \"reduc\", all rewrite rules should begin with function application") ext1
  | [] -> internal_error "reduction with empty list"

(* Check clauses *)
	
let pred_env = Param.pred_env

let rec interpret_info ty r = function
    ("memberOptim", ext) -> 
      if List.length ty != 2 then
	input_error "memberOptim makes sense only for predicates of arity 2" ext;
      r.p_prop <- r.p_prop lor Param.pred_ELEM
  | ("elimVar",ext) -> r.p_prop <- r.p_prop lor Param.pred_ANY
  | ("elimVarStrict",ext) -> r.p_prop <- r.p_prop lor Param.pred_ANY_STRICT
  | ("decompData",ext) -> 
      if List.exists (fun t -> t != Param.any_type) ty then
	input_error "decompData makes sense only for predicates that are polymorphic in all their arguments" ext;
      r.p_prop <- r.p_prop lor Param.pred_TUPLE
  | ("decompDataSelect",ext) -> 
      if List.exists (fun t -> t != Param.any_type) ty then
	input_error "decompDataSelect makes sense only for predicates that are polymorphic in all their arguments" ext;
      r.p_prop <- r.p_prop lor Param.pred_TUPLE lor Param.pred_TUPLE_SELECT
  | ("block",_) -> r.p_prop <- r.p_prop lor Param.pred_BLOCKING
	  (* add other qualifiers here *)
  | (s,ext) -> input_error ("unknown predicate qualifier " ^ s) ext

let check_pred (c,ext) tl info =
  if c = "attacker" || c = "mess" || c = "event" || c = "inj-event" then
    input_error ("predicate name " ^ c ^ " is reserved. You cannot declare it") ext;
  if StringMap.mem c (!global_env) then
    input_error ("identifier " ^ c ^ " already defined (as a free name, a function, or a predicate)") ext;
  let tyl = List.map (get_type_polym true) tl in
  let r = { p_name = c; p_type = tyl; p_prop = 0; p_info = [] } in
  List.iter (interpret_info tyl r) info;
  if List.exists (fun t -> t == Param.any_type) tyl then
    r.p_info <- [PolymPred(c, r.p_prop, tyl)];
  Hashtbl.add pred_env c r;
  global_env := StringMap.add c (EPred r) (!global_env) 

let get_pred env (c, ext) tl =
  try
    match StringMap.find c env with
      EPred r ->
	if not ((List.length r.p_type == List.length tl) && (List.for_all2 (fun t1 t2 -> t1 == t2 || t1 == Param.any_type) r.p_type tl)) then
	  input_error ("predicate " ^ c ^ " expects arguments of type " ^ 
		       (Terms.tl_to_string ", " r.p_type) ^
		       " but is given arguments of type " ^
		       (Terms.tl_to_string ", " tl)) ext;
	if List.exists (fun t -> t == Param.any_type) r.p_type then
	  Param.get_pred (PolymPred(r.p_name, r.p_prop, tl))
	else
	  r
    | _ -> input_error (c ^ " should be a predicate") ext
  with Not_found ->
    input_error ("undeclared predicate " ^ c ) ext


let add_rule hyp concl constra tag =
  Param.red_rules := (hyp, concl, constra, tag) :: (!Param.red_rules)


let equal_fact t1 t2 =
  Pred(Param.get_pred (Equal(Terms.get_term_type t1)), [t1;t2])

let check_cterm env (p,t) =
  let (tl, tyl) = List.split (List.map (check_eq_term f_any env) t) in
  (get_pred env p tyl, tl)

let rec check_hyp (hyp_accu,constra_accu) env (fact, ext) = 
  match fact with
    PIdent p -> 
      let (p',l') = check_cterm env (p,[]) in
      (Pred(p',l')::hyp_accu, constra_accu)
  | PTuple _ -> input_error "tuples not allowed here" ext
  | PFunApp((f,fext) as p, l) ->
      match f,l with
	"<>", [t1;t2] ->
	  let (t1', ty1) = check_eq_term f_any env t1 in
	  let (t2', ty2) = check_eq_term f_any env t2 in
	  if ty1 != ty2 then
	    input_error "the two arguments of an inequality test should have the same type" ext;
	  (hyp_accu, [Neq(t1', t2')] :: constra_accu)
      | "=", [t1;t2] ->
	  let (t1', ty1) = check_eq_term f_any env t1 in
	  let (t2', ty2) = check_eq_term f_any env t2 in
	  if ty1 != ty2 then
	    input_error "the two arguments of an equality test should have the same type" ext;
	  ((equal_fact t1' t2')::hyp_accu, constra_accu)
      |	"&&", [h1;h2] ->
	  check_hyp (check_hyp (hyp_accu,constra_accu) env h1) env h2
      |	("<>" | "=" | "&&"), _ -> internal_error ("Bad arity for special function " ^ f)
      |	("||" | "not" | "choice"), _ -> input_error (f ^ " not allowed here") fext
      | _ ->
	  let (p',l') = check_cterm env (p,l) in
	  (Pred(p',l')::hyp_accu, constra_accu)

let check_simple_fact env (fact, ext) = 
  match fact with
    PIdent p -> 
      let (p',l') = check_cterm env (p,[]) in
      Pred(p',l')
  | PTuple _ -> input_error "tuples not allowed here" ext
  | PFunApp((f,fext) as p,l) ->
      match f with
	"=" | "<>" | "&&" | "||" | "not" | "choice" -> input_error (f ^ " not allowed here") fext
      |	_ -> 
	  let (p',l') = check_cterm env (p,l) in
	  Pred(p',l')

let check_clause = function
    (env, PFact(c)) ->
      begin
	let env = create_env env in
	let concl = check_simple_fact env c in
	add_rule [] concl [] LblClause
      end
  | (env, PClause(i,c)) ->
      begin
      try 
	let env = create_env env in
	let (hyp, constra) = check_hyp ([],[]) env i in
	let concl = check_simple_fact env c in
	add_rule hyp concl
	  (Rules.simplify_constra_list (concl :: hyp) constra) LblClause
      with Rules.FalseConstraint -> ()
      end
  | (env, PEquiv(i,c,select)) ->
      let env = create_env env in
      let (hyp, constra) = check_hyp ([],[]) env i in
      if constra != [] then 
	Parsing_helper.user_error "Inequality constraints not allowed in equivalences";
      let concl = check_simple_fact env c in
      add_rule hyp concl [] LblEquiv;
      List.iter (fun h -> add_rule [concl] h [] LblEquiv) hyp;
      Rules.add_equiv (hyp, concl, -1); (* TO DO should give a real rule number, but that's not easy... *)
      if not select then Terms.add_unsel concl

      
(* List of the free names of the process *)

let freenames = Param.freenames

let create_name s ty is_free =
  let cat = Name { prev_inputs = None; prev_inputs_meaning = [] } in
   { f_name = s; 
     f_type = ty;
     f_cat = cat;
     f_initial_cat = cat;
     f_private = not is_free;
     f_options = 0 }

let create_name_uniq s ty is_free =
  let cat = Name { prev_inputs = None; prev_inputs_meaning = [] } in
   { f_name = s ^ "_" ^ (string_of_int (Terms.new_var_name())); 
     f_type = ty;
     f_cat = cat;
     f_initial_cat = cat;
     f_private = not is_free;
     f_options = 0 }

let add_free_names name_type options =
  let is_private = ref false in
  List.iter (function 
    | ("private",_) -> is_private := true
    | (_,ext) ->
	input_error "for free names, the only allowed option is private" ext) options;
  List.iter (fun ((s,ext), t) -> 
    let ty = get_type t in
    if StringMap.mem s (!global_env) then
      input_error ("identifier " ^ s ^ " already declared (as a free name, a function, or a predicate)") ext;
    let r = create_name s ([],ty) (not (!is_private)) in 
    global_env := StringMap.add s (EName r) (!global_env);
    freenames := r :: !freenames) name_type


(* Elimtrue *)

let format_get_ident_any env (s,ext) =
  try 
    match StringMap.find s env with
      EVar v -> FVar v
    | EFun r ->
	if fst r.f_type != [] then
	  input_error ("function " ^ s ^ " expects " ^ 
		       (string_of_int (List.length (fst r.f_type))) ^
		       " arguments but is used without arguments") ext;
	(match r.f_cat with
	  Eq _ | Tuple -> ()
	| _ -> input_error ("function " ^ s ^ " has been defined by reduction. It should not appear in formats") ext);
	FFunApp (r, [])
    | _ ->  input_error ("identifier " ^ s ^ " should be a function or a variable") ext
  with Not_found ->
    input_error ("identifier " ^ s ^ " not defined as a function or as a variable") ext

let rec check_format env = function 
    (Ptree.PFIdent i) -> 
      let t = format_get_ident_any env i in
      (t, Terms.get_format_type t)
  | (Ptree.PFFunApp((s,ext),l)) -> 
      let (l', tyl) = List.split (List.map (check_format env) l) in
      let f = get_fun env (s,ext) tyl in
      (match f.f_cat with
	Eq _ | Tuple -> ()
      | _ -> input_error ("function " ^ s ^ " has been defined by reduction. It should not appear in formats") ext);
      if (f.f_options land Param.fun_TYPECONVERTER != 0) && (!Param.ignore_types) then
	match l' with
	  [t] -> (t, snd f.f_type)
	| _ -> internal_error "type converter functions should always be unary"
      else
	(FFunApp(f, l'), snd f.f_type)
  | (Ptree.PFTuple l) -> 
      let (l', tyl) = List.split (List.map (check_format env) l) in
      (FFunApp(Terms.get_tuple_fun tyl, l'), Param.bitstring_type)
  | (Ptree.PFName((s,ext),l)) -> 
      internal_error "Names not allowed in formats with -in pi"
  | Ptree.PFAny i -> 
      let v = get_var env i in
      (FAny v, v.btype)


let check_cformat_fact env (p,l) =
  let (l', tyl) = List.split (List.map (check_format env) l) in
  (get_pred env p tyl, l')

(* Check non-interference terms *)

let get_non_interf_name env (s,ext) =
   try
     match StringMap.find s env  with
       EName r -> 
	 check_single ext s;
	 if not r.f_private then
	   input_error ("Non-interference is certainly false on public values, such as " ^ s) ext
	 else
	   r
     | _ ->
	 input_error ("Non-interference can only be tested on private free names") ext
   with Not_found ->
     input_error ("Name " ^ s ^ " is not declared") ext

let rec check_ni_term env (term,ext) = 
  match term with
    (PIdent (s,ext)) -> 
      let t = 
	try
	  match StringMap.find s env with
	    EVar v -> Var v
	  | EFun f ->
	      if fst f.f_type <> [] then 
		input_error ("function " ^ s ^ " expects " ^ 
			     (string_of_int (List.length (fst f.f_type))) ^
			     " arguments but is used without arguments") ext;
	      (match f.f_cat with
		Eq _ | Tuple -> ()
	      | _ -> input_error ("function " ^ s ^ " has been defined by reduction. It should not appear in non-interference queries") ext);
	      FunApp(f, [])
	  | EName r -> 
	      FunApp (r, [])
	  | _ -> input_error ("identifier " ^ s ^ " should be a variable, a function, or a name") ext
	with Not_found ->
	  input_error ("identifier " ^ s ^ " not defined as a variable, a function, or a name") ext
      in
      (t, Terms.get_term_type t)
  | (PFunApp ((s,ext), tlist)) ->
      let (tl, tyl) = List.split (List.map (check_ni_term env) tlist) in
      let f = get_fun env (s,ext) tyl in
      (match f.f_cat with
	Eq _ | Tuple -> ()
      | _ -> input_error ("function " ^ s ^ " has been defined by reduction. It should not appear in non-interference queries") ext);
      if (f.f_options land Param.fun_TYPECONVERTER != 0) && (!Param.ignore_types) then
	match tl with
	  [t] -> (t, snd f.f_type)
	| _ -> internal_error "type converter functions should always be unary"
      else
	(FunApp(f, tl), snd f.f_type)
  | (PTuple tlist) ->
      let (l, tl) = List.split (List.map (check_ni_term env) tlist) in
      (FunApp (Terms.get_tuple_fun tl, l), Param.bitstring_type)

let get_non_interf env (id, lopt) =
  let n = get_non_interf_name (create_env env) id in
  (n, 
   match lopt with
     None -> None
   | Some l -> 
       Some (List.map (fun t -> 
	 let (t', ty) = check_ni_term (create_env env) t in
	 if ty != snd n.f_type then
	   input_error ("this term has type " ^ ty.tname ^ " but should have type " ^ (snd n.f_type).tname) (snd t);
	 t'
	     ) l))

(* Get an ident when anything is allowed *)

let get_ident_any env (s, ext) =
   try
     match StringMap.find s env with
         EVar b -> Var b
       | EName r -> FunApp (r,[])
       | EFun f -> 
	   if fst f.f_type = [] then
	     FunApp(f,[])
	   else
	     input_error ("function " ^ s ^ " expects " ^ 
			  (string_of_int (List.length (fst f.f_type))) ^
			  " arguments but is used without arguments") ext
       | _ -> input_error ("identifier " ^ s ^ " should be a variable, a function, or a name") ext
   with Not_found ->
     input_error ("Variable, function, or name " ^ s ^ " not declared") ext

let rec check_term env (term, _) =
  match term with 
    (PIdent i) -> 
      let t = get_ident_any env i in
      (t, Terms.get_term_type t)
  | (PFunApp((s,ext),l)) -> 
      let (l',tl') = List.split (List.map (check_term env) l) in
      let f = 
	if s = "choice" then 
	  match tl' with
	    [t1;t2] when t1 == t2 -> Param.choice_fun t1
	  | _ -> 
	      input_error ("function choice expects two arguments of same type but is given arguments of type " ^
			   (Terms.tl_to_string ", " tl')) ext
	else
	  get_fun env (s,ext) tl'
      in
      if (f.f_options land Param.fun_TYPECONVERTER != 0) && (!Param.ignore_types) then
	match l' with
	  [t] -> (t, snd f.f_type)
	| _ -> internal_error "type converter functions should always be unary"
      else
	(FunApp(f, l'), snd f.f_type)
  | (PTuple l) -> 
      let (l',tl') = List.split (List.map (check_term env) l) in
      (FunApp(Terms.get_tuple_fun tl', l'), Param.bitstring_type)

let check_fl_term env (p,l) =
  let (l', tl') = List.split (List.map (check_term env) l) in
  (get_pred env p tl', l')

let pdeftbl = (Hashtbl.create 7 : (string, binder list * process) Hashtbl.t)

(* Copy a process *)

let copy_binder b =
  let b' = Terms.new_var b.sname b.btype in
  match b.link with
    NoLink ->
      Terms.link b (TLink (Var b'));
      b'
  | _ -> Parsing_helper.internal_error "unexpected link in copy_binder"

let rec copy_pat = function
    PatVar b -> PatVar (copy_binder b)
  | PatTuple(f,l) -> PatTuple(f, List.map copy_pat l)
  | PatEqual(t) -> PatEqual (Terms.copy_term3 t)

let rec copy_process add_in_glob_table = function
    Nil -> Nil
  | Par(p1,p2) -> Par(copy_process add_in_glob_table p1, copy_process add_in_glob_table p2)
  | Restr(n,p) -> 
      if add_in_glob_table then
	(* If it is the final copy, create a distinct name for each restriction and add it in the glob_table *)
	let n' = create_name_uniq n.f_name n.f_type false in
	Hashtbl.add glob_table n.f_name n';
	Restr(n', Reduction_helper.process_subst (copy_process add_in_glob_table p) n (FunApp(n',[])))
      else
	Restr(n, copy_process add_in_glob_table p)
  | Repl(p,occ) -> Repl(copy_process add_in_glob_table p, new_occurrence())
  | Let(pat, t, p, q, occ) -> 
      let pat' = copy_pat pat in 
      Let(pat', Terms.copy_term3 t, copy_process add_in_glob_table p, copy_process add_in_glob_table q, new_occurrence())
  | Input(t, pat, p, occ) -> 
      let pat' = copy_pat pat in 
      Input(Terms.copy_term3 t, pat', copy_process add_in_glob_table p, new_occurrence())
  | Output(tc,t,p, occ) -> Output(Terms.copy_term3 tc, Terms.copy_term3 t, copy_process add_in_glob_table p, new_occurrence())
  | Test(t,t',p,q,occ) -> Test(Terms.copy_term3 t, Terms.copy_term3 t', copy_process add_in_glob_table p, copy_process add_in_glob_table q,new_occurrence())
  | Event(t, p, occ) -> Event(Terms.copy_term3 t, copy_process add_in_glob_table p, new_occurrence())
  | Phase(n,p) -> Phase(n, copy_process add_in_glob_table p)
  | LetFilter(bl, f, p, q, occ) -> 
      let bl' = List.map copy_binder bl in 
      LetFilter(bl', Terms.copy_fact3 f, copy_process add_in_glob_table p, copy_process add_in_glob_table q, new_occurrence())


let rec check_pat env tyopt = function
  PPatVar ((s,e), topt) -> 
    let ty = 
      match topt, tyopt with
	None, None ->
	  input_error ("variable " ^ s ^ " should be declared with a type") e
      |	Some (t,e), None -> 
	  get_type (t,e) 
      |	None, Some ty ->
	  ty
      |	Some (t,e), Some ty ->
	  let ty' = get_type (t,e) in
	  if ty != ty' then
	    input_error ("variable " ^ s ^ " is declared of type " ^ t ^ " but should be of type " ^ ty.tname) e;
	  ty
    in
    if (StringMap.mem s env) then
      input_warning ("identifier " ^ s ^ " rebound") e;
    let v = Terms.new_var s ty in
    (PatVar v, StringMap.add s (EVar v) env)
| PPatTuple l ->
    let (l',env') = check_pat_list dummy_ext env (List.map (fun _ -> None) l) l in
    (PatTuple(Terms.get_tuple_fun (List.map Terms.get_pat_type l'), l'), env')
| PPatFunApp((s,ext),l) ->
    begin
      try
	match StringMap.find s env with
	  EFun f -> 
	    begin
	      match tyopt with
		None -> ()
	      |	Some ty -> 
		  if ty != snd f.f_type then
		    input_error ("pattern is of type " ^ (snd f.f_type).tname ^ " but should be of type " ^ ty.tname) ext;
	    end;
	    let (l',env') = check_pat_list ext env (List.map (fun t -> Some t) (fst f.f_type)) l in
	    if f.f_cat <> Tuple then
	      input_error ("only data functions are allowed in patterns, not " ^ s) ext;
	    if (f.f_options land Param.fun_TYPECONVERTER != 0) && (!Param.ignore_types) then
	      match l' with
		[t] -> (t, env')
	      | _ -> internal_error "type converter functions should always be unary"
	    else
	      (PatTuple(f, l'), env')
	| _ ->
	    input_error ("only functions can be applied, not " ^ s) ext
      with Not_found ->
	input_error ("function " ^ s ^ " not defined") ext
    end
| PPatEqual t ->
    let (t', ty') = check_term env t in
    begin
      match tyopt with
	None -> ()
      |	Some ty -> 
	  if ty != ty' then
	    input_error ("pattern is of type " ^ ty'.tname ^ " but should be of type " ^ ty.tname) (snd t);
    end;
    (PatEqual t', env)

and check_pat_list ext env tyl tl = 
  match (tl, tyl) with
    [],[] -> ([], env)
  | (a::l),(ty::tyl)  -> 
      let (a',env') = check_pat env ty a in
      let (l',env'') = check_pat_list ext env' tyl l in
      (a'::l', env'')
  | _ -> input_error "wrong arity for pattern" ext

let event_fun_table = Hashtbl.create 7

let get_event_fun (s,ext) tl =
  try
    let p = Hashtbl.find event_fun_table s in
    if not (Terms.eq_lists (fst p.f_type) tl) then
      input_error ("function " ^ s ^ " expects arguments of type " ^ 
		   (Terms.tl_to_string ", " (fst p.f_type)) ^
		   " but is given arguments of type " ^
		   (Terms.tl_to_string ", " tl)) ext;
    p
  with Not_found ->
    let p = { f_name = s; 
	      f_type = tl, Param.event_type; 
	      f_cat = Eq[]; 
	      f_initial_cat = Eq[]; 
	      f_private = true;
	      f_options = 0 } 
    in
    Hashtbl.add event_fun_table s p;
    p

let rec check_process add_in_glob_table env = function 
    PNil -> Nil
  | PPar (p1,p2) -> 
      Par(check_process add_in_glob_table env p1, check_process add_in_glob_table env p2)
  | PRepl p -> 
      Repl(check_process add_in_glob_table env p, new_occurrence())
  | PTest(c,p1,p2) -> 
      let rec interpret_cond p1 p2 = function
	  (PIdent pred), ext -> interpret_cond p1 p2 (PFunApp(pred,[]), ext) 
	| (PTuple _), ext ->
	    input_error "tuples allowed in terms, but not at this level of conditions" ext
	| (PFunApp((f,fext), l)), ext ->
	    match f, l with
	      "||", [c1;c2] -> 
	        (* if c1 || c2 then p1 else p2
		   is equivalent to
		   if c1 then p1 else (if c2 then p1 else p2) *)
		interpret_cond p1 (PTest(c2,p1,p2)) c1
	    | "&&", [c1;c2] ->
	        (* if c1 && c2 then p1 else p2
		   is equivalent to
		   if c1 then (if c2 then p1 else p2) else p2 *)
		interpret_cond (PTest(c2,p1,p2)) p2 c1
	    | "not", [c] -> 
		interpret_cond p2 p1 c
	    | "=", [t1;t2] ->
		let (t1', ty1) = check_term env t1 in
		let (t2', ty2) = check_term env t2 in
		if ty1 != ty2 then
		  input_error "the two arguments of an equality test should have the same type" ext;
		Test(t1', t2',
		     check_process add_in_glob_table env p1, check_process add_in_glob_table env p2, new_occurrence())
	    | "<>", [t1;t2] ->
		let (t1', ty1) = check_term env t1 in
		let (t2', ty2) = check_term env t2 in
		if ty1 != ty2 then
		  input_error "the two arguments of an inequality test should have the same type" ext;
		Test(t1', t2',
		     check_process add_in_glob_table env p2, check_process add_in_glob_table env p1, new_occurrence())
	    | ("||" | "&&" | "=" | "<>" | "not"), _ ->
		internal_error ("Bad arity for special function " ^ f)
	    | "choice", _ -> 
		input_error "choice allowed in terms, but not at this level of conditions" ext
	    | _ -> 
		let (pred',l') = check_fl_term env ((f,fext),l) in
		LetFilter([], Pred(pred',l'), check_process add_in_glob_table env p1, check_process add_in_glob_table env p2, new_occurrence())
      in
      interpret_cond p1 p2 c
  | PLetDef ((s,ext), args) ->
      let (tl, tyl) = List.split (List.map (check_term env) args) in
      begin
	try
          let (param, p') = Hashtbl.find pdeftbl s in
	  let ptype = List.map (fun b -> b.btype) param in
	  if not (Terms.eq_lists ptype tyl) then
	    input_error ("process " ^ s ^ " expects arguments of type " ^ 
			 (Terms.tl_to_string ", " ptype) ^
			 " but is given arguments of type " ^
			 (Terms.tl_to_string ", " tyl)) ext;
	  if !Terms.current_bound_vars != [] then
	    Parsing_helper.internal_error "bound vars should be cleaned up (pitsyntax)";
	  List.iter2 (fun t p -> Terms.link p (TLink t)) tl param;
	  let p'' = copy_process add_in_glob_table p' in
	  Terms.cleanup();
	  p''
        with Not_found ->
          input_error ("process " ^ s ^ " not defined") ext
      end
  | PRestr((s,ext),t,p) -> 
      let ty = get_type t in
      if (StringMap.mem s env) then
	input_warning ("identifier " ^ s ^ " rebound") ext;
      if add_in_glob_table then
	let r = create_name_uniq s (Param.tmp_type, ty) false in
	Hashtbl.add glob_table s r;
	Restr(r, check_process add_in_glob_table (StringMap.add s (EName r) env) p)
      else
	let r = create_name s (Param.tmp_type, ty) false in
	Restr(r, check_process add_in_glob_table (StringMap.add s (EName r) env) p)
  | PInput(tc,pat,p) ->
      let (tc', tyc) = check_term env tc in
      if tyc != Param.channel_type then
	input_error ("this term has type " ^ tyc.tname ^ " but should have type channel") (snd tc);
      let (pat',env') = check_pat env None pat in
      Input(tc', pat', check_process add_in_glob_table env' p, new_occurrence())
  | POutput(tc,t,p) ->
      let (tc', tyc) = check_term env tc in
      if tyc != Param.channel_type then
	input_error ("this term has type " ^ tyc.tname ^ " but should have type channel") (snd tc);
      let (t, ty) = check_term env t in
      Output(tc', t,
	     check_process add_in_glob_table env p, new_occurrence())
  | PLet(pat,t,p,p') ->
      let (t', ty) = check_term env t in
      let (pat', env') = check_pat env (Some ty) pat in
      Let(pat',t',check_process add_in_glob_table env' p,check_process add_in_glob_table env p', new_occurrence())
  | PLetFilter(identlist,(fact,ext),p,q) ->
      let (env', vlist) = List.fold_left (fun (env, vlist) ((s,e),t) ->
	if (StringMap.mem s env) then
	  input_warning ("identifier " ^ s ^ " rebound") e;
	let ty = get_type t in
	let v = Terms.new_var s ty in
	(StringMap.add s (EVar v) env, v:: vlist)) (env,[]) identlist in
      let vlist = List.rev vlist in
      let f' = 
	match fact with
	  PIdent p -> 
	    let (p',l') = check_fl_term env' (p,[]) in
	    Pred(p',l')
	| PTuple _ -> input_error "tuples not allowed here" ext
	| PFunApp((f,fext) as p,l) ->
	    match f, l with
	      "=", [t1;t2] ->  
		let (t1', ty1) = check_term env' t1 in
		let (t2', ty2) = check_term env' t2 in
		if ty1 != ty2 then
		  input_error "the two arguments of an equality test should have the same type" ext;
		equal_fact t1' t2'
	    | "=", _ -> internal_error ("Bad arity for special function " ^ f)
	    | ("<>" | "&&" | "||" | "not" | "choice"), _ -> input_error (f ^ " not allowed here") fext
	    | _ -> 
		let (p',l') = check_fl_term env' (p,l) in
		Pred(p',l')
      in
      LetFilter(vlist, f', check_process add_in_glob_table env' p, check_process add_in_glob_table env q, new_occurrence())
  | PEvent((i,ext),l,p) ->
      let (l', tl) = List.split (List.map (check_term env) l) in
      if !Param.key_compromise == 0 then
	let f = get_event_fun (i,ext) tl in
	Event(FunApp(f, l'), check_process add_in_glob_table env p, new_occurrence())
      else
	let f = get_event_fun (i,ext) (Param.sid_type :: tl) in
	Event(FunApp(f, (Terms.new_var_def Param.sid_type) :: l'), check_process add_in_glob_table env p, new_occurrence())
  | PPhase(n, p) ->
      Phase(n, check_process add_in_glob_table env p)

let query_list = ref ([] : (envdecl * tquery list) list)
let need_vars_in_names = Reduction_helper.need_vars_in_names
let noninterf_list = ref ([] : (funsymb * term list option) list list)
let not_list = ref ([] : (envdecl * gterm_e) list)
let nounif_list = ref ([] : (envdecl * nounif_t) list)
let weaksecret_list = ref ([] : funsymb list)

(* Compute need_vars_in_names: the list of pairs (restriction, variable name)
   such that the variable "variable name" must occur as argument in the
   pattern that models names created by "restriction", because the
   structure "restriction[... variable name = ... ]" is used in the input 
   file. *)

let rec nvn_t (term, ext0) =
  match term with
    PGIdent _ -> ()
  | PGFunApp(_,l) -> List.iter nvn_t l
  | PGPhase(_,l, _) -> List.iter nvn_t l
  | PGTuple l -> List.iter nvn_t l
  | PGName ((s,ext),bl) ->
      List.iter (fun ((s',ext'),t) -> 
	(* The replication indices do not need to be added in 
	   need_vars_in_names, because they are always included as
	   arguments of names, whether or not they occur in 
	   the input file. 
	   They must not be added to need_vars_in_names, because 
	   they are not correctly computed by trace reconstruction,
	   so adding them would cause bugs in trace reconstruction. *)
	if (s' <> "") && (s'.[0] != '!') then
	  begin
	    try 
	      let r = Hashtbl.find glob_table s in
	      (* print_string ("Need " ^ s' ^ " in " ^ r.f_name ^ "\n");  *)
	      need_vars_in_names := (r.f_name, s',ext') :: (!need_vars_in_names)
	    with Not_found ->
	      ()
	  end;
	nvn_t t
						) bl
  | PGLet(_,t,t') -> nvn_t t; nvn_t t'

let nvn_q  = function
    PRealQuery q -> nvn_t q
  | PPutBegin(i, l) -> ()

let rec nvn_f (f,ext0) = 
  match f with
    PFGIdent (s,ext) -> ()
  | PFGFunApp((s,ext),l) -> List.iter nvn_f l
  | PFGTuple l -> List.iter nvn_f l
  | PFGName ((s,ext),bl) ->
      List.iter (fun ((s',ext'),t) -> 
	(* The replication indices do not need to be added in 
	   need_vars_in_names, because they are always included as
	   arguments of names, whether or not they occur in 
	   the input file. 
	   They must not be added to need_vars_in_names, because 
	   they are not correctly computed by trace reconstruction,
	   so adding them would cause bugs in trace reconstruction. *)
	if (s' <> "") && (s'.[0] != '!') then
	  begin
	    try 
	      let r = Hashtbl.find glob_table s in
	      (* print_string ("Need " ^ s' ^ " in " ^ r.f_name ^ "\n");  *)
	      need_vars_in_names := (r.f_name, s',ext') :: (!need_vars_in_names)
	    with Not_found ->
	      ()
	  end;
	nvn_f t
						) bl
  | PFGAny (s,ext) -> ()
  | PFGLet(_,t,t') -> nvn_f t; nvn_f t'

let rec nvn_nounif = function
    BFLet(_,t,nounif) ->  nvn_f t; nvn_nounif nounif
  | BFNoUnif((id,fl,n),_) -> List.iter nvn_f fl

(* Handle all declarations *)

let rec check_all = function
    (TTypeDecl(i))::l -> check_type_decl i; check_all l
  | (TFunDecl(f,argt,rest,i))::l -> check_fun_decl f argt rest i; check_all l
  | (TConstDecl(f,rest,i))::l -> check_fun_decl f [] rest i; check_all l
  | (TEquation(env,t1,t2))::l ->
      check_equation env t1 t2;
      check_all l
  | (TReduc (r,i))::l -> 
      check_red r i; 
      check_all l
  | (TPredDecl (p, argt, info)) :: l ->
      check_pred p argt info;
      check_all l
  | (TPDef ((s,ext), args, p)) :: l -> 
      let env = ref (!global_env) in
      let arglist = List.map (fun ((s',ext'),ty) ->
	let t = get_type ty in
	begin
	  try
	    match StringMap.find s' (!env) with
	      EVar _ -> input_error ("variable " ^ s' ^ " already defined") ext'
	    | _ -> ()
	  with Not_found ->
	    ()
	end;
	let v = Terms.new_var s' t in
	env := StringMap.add s' (EVar v) (!env);
	v
	       ) args
      in
      let p' = check_process false (!env) p in
      Hashtbl.add pdeftbl s (arglist, p'); 
      check_all l
  | (TQuery (env,q)) :: l -> 
      query_list := (env,q) :: (!query_list); 
      check_all l
  | (TNoninterf (env, lnoninterf)) :: l -> 
      noninterf_list := (List.map (get_non_interf env) lnoninterf) :: (!noninterf_list); 
      check_all l
  | (TWeaksecret i) :: l ->
      weaksecret_list := (get_non_interf_name (!global_env) i) ::(!weaksecret_list);
      check_all l
  | (TNoUnif (env, nounif)) :: l ->
      nounif_list := (env, nounif) :: (!nounif_list);
      check_all l
  | (TElimtrue(env, factformat)) :: l ->
      let env = create_env env in
      Rules.add_elimtrue (check_cformat_fact env factformat);
      check_all l
  | (TNot (env, no)) :: l -> 
      not_list := (env, no) :: (!not_list); 
      check_all l
  | (TFree (name_type,i)) :: l -> 
      add_free_names name_type i;
      check_all l
  | (TClauses c) :: l ->
      List.iter check_clause c;
      check_all l
  | [TProcess p] -> 
      let r = check_process true (!global_env) p in
      List.iter (fun (_, q) -> List.iter nvn_q q) (!query_list);
      List.iter (fun (_, no) -> nvn_t no) (!not_list);
      List.iter (fun (_, nounif) -> nvn_nounif nounif) (!nounif_list);
      r
  | _ -> internal_error "The first process part is not the last element of the file"

(* Get the maximum phase number *)

let rec set_max_used_phase = function
    Nil -> ()
  | Par(p1,p2) -> set_max_used_phase p1; set_max_used_phase p2
  | Repl (p,_) ->  set_max_used_phase p
  | Restr(n,p) -> set_max_used_phase p
  | Test(_,_,p1,p2,_) -> set_max_used_phase p1; set_max_used_phase p2
  | Input(_,_, p,_) -> set_max_used_phase p
  | Output(_,_,p,_) -> set_max_used_phase p
  | Let(_,_,p1, p2,_) -> set_max_used_phase p1; set_max_used_phase p2
  | LetFilter(_,_,p,q,_) -> set_max_used_phase p; set_max_used_phase q
  | Event(_,p,_) -> set_max_used_phase p
  | Phase(n,p) ->
      if n > !Param.max_used_phase then
	Param.max_used_phase := n;
      set_max_used_phase p

let parse_file s = 
  init_fun_decl();
  let decl = parse s in
  (* ignoreTypes must be set before doing the rest of the work
     Setting all parameters beforehand does not hurt. *)
  List.iter (function
      TSet((p,ext),v) -> 
	begin
	  match (p,v) with
	    "attacker", S ("passive",_) -> Param.active_attacker := false
	  | "attacker", S ("active",_) -> Param.active_attacker := true
	  | "keyCompromise", S ("strict",_) -> Param.key_compromise := 2
	  | "keyCompromise", S ("approx",_) -> Param.key_compromise := 1
	  | "keyCompromise", S ("none",_) -> Param.key_compromise := 0
	  | "movenew", _ -> Param.boolean_param Param.move_new p ext v
	  | "verboseClauses", S ("explained",_) -> Param.verbose_explain_clauses := Param.ExplainedClauses
	  | "verboseClauses", S ("clauses",_) -> Param.verbose_explain_clauses := Param.Clauses
	  | "verboseClauses", S ("none",_) -> Param.verbose_explain_clauses := Param.NoClauses
	  | "explainDerivation", _ -> Param.boolean_param Param.explain_derivation p ext v
	  | "predicatesImplementable", S("check",_) -> Param.check_pred_calls := true
	  | "predicatesImplementable", S("nocheck",_) -> Param.check_pred_calls := false
	  | "eqInNames", _ ->
	      Param.boolean_param Param.eq_in_names p ext v;
	      if !Param.eq_in_names then Param.reconstruct_trace := false
	  | "reconstructTrace", _ -> Param.boolean_param Param.reconstruct_trace p ext v
	  | "traceBacktracking", _ -> Param.boolean_param Param.trace_backtracking p ext v
	  | "unifyDerivation", _ -> Param.boolean_param Param.unify_derivation p ext v
	  | "traceDisplay", S ("none",_) -> Param.trace_display := Param.NoDisplay
	  | "traceDisplay", S ("short",_) -> Param.trace_display := Param.ShortDisplay
	  | "traceDisplay", S ("long",_) -> Param.trace_display := Param.LongDisplay
	  | "ignoreTypes", S (("all" | "true"), _) -> Param.ignore_types := true
	  | "ignoreTypes", S ("attacker", _) -> Param.ignore_types := false; Param.untyped_attacker := true
	  | "ignoreTypes", S (("none" | "false"), _) -> Param.ignore_types := false; Param.untyped_attacker := false
	  | _,_ -> Param.common_parameters p ext v
	end
    | _ -> ()) decl;
  let p = check_all (List.filter (function 
      TSet _ -> false
    | _ -> true) decl)
  in
  if !Param.key_compromise = 2 then
    Param.max_used_phase := 1
  else
    set_max_used_phase p;
  p

let display () =
   print_string "Functions ";
   Hashtbl.iter (fun _ fsymb -> 
     print_string (fsymb.f_name ^ "(" ^ (Terms.tl_to_string ", " (fst fsymb.f_type)) 
		   ^ "):" ^ (snd fsymb.f_type).tname ^ ". ")
       ) fun_decls;
   print_string "\n"

(* queries *)

let non_compromised_session = FunApp(Param.session1, [])


(* Note: when check_query, get_queries are applied before the
   translation of the process into Horn clauses has been done, 
   the arity of names may not be correctly initialized. In this case,
   update_arity_names should be called after the translation of the
   process to update it.  *)

let get_ident_any env (s, ext) =
   try
     match StringMap.find s env with
         EVar b -> 
	   begin
	     match b.link with
	       TLink t -> t
	     | NoLink -> Var b
	     | _ -> internal_error "unexpected link in get_ident_any"
	   end
       | EName r -> 
	   FunApp(r, [])
       | EFun f -> 
	   if fst f.f_type == [] then 
	     FunApp(f,[]) 
	   else
	     input_error ("function " ^ s ^ " has expects " ^ 
			  (string_of_int (List.length (fst f.f_type))) ^
			  " arguments but is used without arguments") ext
       | _ -> input_error ("identifier " ^ s ^ " should be a variable, a free name, or a function") ext
   with Not_found ->
     input_error ("identifier " ^ s ^ " not defined") ext

let rec check_query_term env (term, ext0) =
  match term with
    PGIdent i -> 
      let t = get_ident_any env i in
      (t, Terms.get_term_type t)
  | PGPhase _ -> input_error ("phase unexpected in query terms") ext0
  | PGFunApp((s,ext),l) -> 
      if List.mem s ["="; "<>"; "==>"; "&&"; "||"; "event"; "inj-event"] then
	input_error (s ^ " unexpected in query terms") ext;
      begin
        try
          match StringMap.find s env with
            EFun f -> 
              (match f.f_cat with
                 Eq _ | Tuple -> ()
               | _ ->  input_error ("function " ^ s ^ " is defined by \"reduc\". Such a function should not be used in a query") ext);
	      let (l', tl') = List.split (List.map (check_query_term env) l) in
	      if Terms.eq_lists (fst f.f_type) tl' then 
		if (f.f_options land Param.fun_TYPECONVERTER != 0) && (!Param.ignore_types) then
		  match l' with
		    [t] -> (t, snd f.f_type)
		  | _ -> internal_error "type converter functions should always be unary"
		else
		  (FunApp(f, l'), snd f.f_type)
	      else
		input_error ("function " ^ s ^ " expects arguments of type " ^ 
			     (Terms.tl_to_string ", " (fst f.f_type)) ^
			     " but is given arguments of type " ^
			     (Terms.tl_to_string ", " tl')) ext
          | _ -> input_error("only functions can be applied, not " ^ s) ext
        with Not_found ->
          input_error ("function " ^ s ^ " not defined") ext
      end
  | PGTuple l -> 
      let (l', tl') = List.split (List.map (check_query_term env) l) in
      (FunApp(Terms.get_tuple_fun tl', l'), Param.bitstring_type)
  | PGName ((s,ext),bl) -> 
      begin
	try
	  let r = Hashtbl.find glob_table s in
	  check_single ext s;
	  if fst r.f_type == Param.tmp_type then
	    begin
	      let v = Terms.new_var Param.def_var_name (snd r.f_type) in
	      v.link <- PGTLink (env, (term,ext0));
	   (Var v, snd r.f_type)
	    end
	  else
	    begin
	      match r.f_cat with 
		Name { prev_inputs_meaning = sl } ->
		  List.iter (fun ((s',ext'),_) -> 
		    if not (List.mem s' sl) then
		      input_error ("variable " ^ s' ^ " not defined at restriction " ^ s) ext') bl;
		  let p = List.map2 (fun s'' ty ->
		    if s'' = "!comp" then non_compromised_session else
		    binding_find env s'' ty bl) sl (fst r.f_type)
		  in
		  (FunApp(r, p), snd r.f_type)
	      | _ -> internal_error "name expected here"
	    end
	with Not_found ->
	  input_error (s ^ " should be a name") ext
      end
  | PGLet(id,t,t') -> check_query_term (add_binding env (id,t)) t'

and binding_find env s ty = function
    [] -> Terms.new_var_def ty
  | ((s',ext),t)::l ->
      if s' = s then
	begin
	  let (t', ty') = check_query_term env t in
	  if ty' != ty then
	    input_error ("this variable is of type " ^ ty.tname ^ " but is given a value of type " ^ ty'.tname) ext;
	  t'
	end
      else
	binding_find env s ty l

and add_binding env ((i,ext),t) =
  begin
    try
      match StringMap.find i env with
	EVar _ -> input_error ("variable " ^ i ^ " already defined") ext
      | _ -> ()
    with Not_found -> ()
  end;
  let (t', ty') = check_query_term env t in
  let v = Terms.new_var i ty' in
  v.link <- TLink t';
  StringMap.add i (EVar v) env

let find_event_type (s, ext) tl =
  try
    let f = Hashtbl.find event_fun_table s in
    if not (Terms.eq_lists (fst f.f_type) tl) then
      input_error ("event " ^ s ^ " expects arguments of type " ^ 
		   (Terms.tl_to_string ", " (fst f.f_type)) ^
		   " but is given arguments of type " ^
		   (Terms.tl_to_string ", " tl)) ext
    else
      f
  with Not_found ->
    input_error ("unknown event " ^ s) ext

let check_mess env e tl n =
  match tl with
    [t1;t2] ->
      if n > !Param.max_used_phase then
	begin
	  input_warning "phase greater than the maximum phase used in the process.\nIs that really what you want?" e;
	  Param.max_used_phase := n;
	end;
      let (t1', ty1) = check_query_term env t1 in
      let (t2', ty2) = check_query_term env t2 in
      if ty1 != Param.channel_type then
	input_error ("First argument of mess is of type " ^ ty1.tname ^ " and should be of type channel") e;
      let mess_n = Param.get_pred (Mess((if n = -1 then (!Param.max_used_phase) else n),
					ty2))
      in
      QFact(mess_n, [t1';t2'])
  | _ -> 
      input_error "arity of predicate mess should be 2" e

let check_attacker env e tl n =
  match tl with
    [t1] ->
      if n > !Param.max_used_phase then
	begin
	  input_warning "phase greater than the maximum phase used in the process.\nIs that really what you want?" e;
	  Param.max_used_phase := n;
	end;
      let (t1', ty1) = check_query_term env t1 in
      let att_n = Param.get_pred (Attacker((if n = -1 then (!Param.max_used_phase) else n),
	                                   ty1)) 
      in
      QFact(att_n, [t1'])
  | _ -> 
      input_error "arity of predicate attacker should be 1" e

let rec check_event env (f,e) =
  match f with
    PGFunApp(("<>", _), [t1; t2]) ->
      let (t1', ty1) = check_query_term env t1 in
      let (t2', ty2) = check_query_term env t2 in
      if ty1 != ty2 then
	input_error "the two arguments of an inequality test should have the same type" e;      
      QNeq(t1', t2')
  | PGFunApp(("=", _), [t1; t2]) ->
      let (t1', ty1) = check_query_term env t1 in
      let (t2', ty2) = check_query_term env t2 in
      if ty1 != ty2 then
	input_error "the two arguments of an equality test should have the same type" e;      
      QEq(t1', t2')
  | PGFunApp(("event",e'),tl0) ->
      begin
	match tl0 with
	  [PGFunApp((s,e''), tl),_] ->
	    let (tl', tyl') = List.split (List.map (check_query_term env) tl) in
	    if !Param.key_compromise == 0 then
	      QSEvent(false, FunApp((find_event_type (s, e'') tyl'), tl'))
	    else
	      QSEvent(false, FunApp((find_event_type (s, e'') (Param.sid_type :: tyl')),
				    (Terms.new_var_def Param.sid_type)::tl'))
	| _ -> input_error "predicate event should have one argument, which is a function application" e'
      end
  | PGFunApp(("inj-event",e'),tl0) ->
      begin
	match tl0 with
	  [PGFunApp((s,e''), tl),_] ->
	    let (tl', tyl') = List.split (List.map (check_query_term env) tl) in
	    if !Param.key_compromise == 0 then
	      QSEvent(true, FunApp((find_event_type (s, e'') tyl'), tl'))
	    else
	      QSEvent(true, FunApp((find_event_type (s, e'') (Param.sid_type :: tyl')),
				   (Terms.new_var_def Param.sid_type)::tl'))
	| _ -> input_error "predicate inj-event should have one argument, which is a function application" e'
      end
  | PGFunApp(("attacker",_), tl) ->
      check_attacker env e tl (-1)
  | PGFunApp(("mess",_), tl) ->
      check_mess env e tl (-1)
  | PGFunApp((s, ext) as p, tl) ->
      if List.mem s ["||"; "&&"; "not"; "==>"] then
	input_error (s ^ " unexpected in events") ext;
      let (tl', tyl) = List.split (List.map (check_query_term env) tl) in
      QFact(get_pred env p tyl, tl')
  | PGPhase((s, ext), tl, n) ->
      begin
	match s with
	  "mess" -> check_mess env e tl n
	| "attacker" -> check_attacker env e tl n
	| _ -> input_error "phases can be used only with attacker or mess" ext
      end
  | PGIdent p -> 
      QFact(get_pred env p [], [])
  | PGLet(id,t,t') -> check_event (add_binding env (id,t)) t'
  | _ -> input_error "an event should be a predicate application" e
      
let rec check_hyp env = function
    PGFunApp(("==>", _), [ev; hypll]), _ ->
      let ev' = check_event env ev in
      (
       match ev' with
	 QNeq _ | QEq _ -> input_error "Inequalities or equalities cannot occur before ==> in queries" (snd ev)
       | _ -> ()
      );
      let hypll' = check_hyp env hypll in
      [[NestedQuery(Before(ev', hypll'))]]
  | PGFunApp(("||", _), [he1;he2]), _ -> 
      (check_hyp env he1) @ (check_hyp env he2)
  | PGFunApp(("&&", _), [he1;he2]), _ ->
      let he1' = check_hyp env he1 in
      let he2' = check_hyp env he2 in
      List.concat (List.map (fun e1 -> List.map (fun e2 -> e1 @ e2) he2') he1')
  | PGLet(id,t,t'), _ -> check_hyp (add_binding env (id,t)) t'
  | ev -> [[QEvent(check_event env ev)]]

let rec check_real_query_top env = function
    PGFunApp(("==>", _), [ev; hypll]), _ ->
      let ev' = check_event env ev in
      let ev'' = 
	match ev' with
	  QNeq _ | QEq _ -> user_error "Inequalities or equalities cannot occur before ==> in queries\n"
	| QFact _ -> ev'
	| QSEvent _ when !Param.key_compromise == 0 -> ev'
	| QSEvent(inj, FunApp(f, sid::l)) ->
	    QSEvent(inj, FunApp(f, non_compromised_session::l))
	| QSEvent(_,_) ->
	    internal_error "Bad format for events in queries"
      in
      let hypll' = check_hyp env hypll in
      Before(ev'', hypll')
  | PGLet(id,t,t'), _ -> check_real_query_top (add_binding env (id,t)) t'
  | ev ->
      let ev' = check_event env ev in
      let ev'' = 
	match ev' with
	  QNeq _ | QEq _ -> user_error "Inequalities or equalities cannot occur alone queries\n"
	| QFact _ -> ev'
	| QSEvent _ when !Param.key_compromise == 0 -> ev'
	| QSEvent(inj, FunApp(f, sid::l)) ->
	    QSEvent(inj, FunApp(f, non_compromised_session::l))
	| QSEvent(_,_) ->
	    internal_error "Bad format for events in queries"
      in
      Before(ev'', [])

let rec check_query_list env = function
    [] -> []
  | (PRealQuery q)::lq -> 
      (RealQuery(check_real_query_top env q))::(check_query_list env lq)
  | (PPutBegin(i, l))::lq ->
      let l' = List.map (fun (s,e) ->
	try
	  Hashtbl.find event_fun_table s
	with Not_found ->
	  input_error ("unknown event " ^s) e) l
      in
      (PutBegin(i,l'))::(check_query_list env lq)

let rec has_inj = function
    Before(_,ll) ->
      List.exists (List.exists (function
	  NestedQuery q -> has_inj q
	| QEvent (QSEvent (i,_)) -> i
	| QEvent (_) -> false)) ll

let rec check_inj_coherent_r q = 
  if has_inj q then
    match q with 
      Before(e,ll) ->
	let e' = 
	match e with
	  QFact _ | QNeq _ | QEq _ -> user_error "In a query e ==> h, if h contains an injective event, then e must be an event or better inj-event\n"
	| QSEvent(_,t) -> QSEvent(true, t) (* set the event injective *)
	in
	Before(e', List.map (List.map (function 
	    QEvent e -> QEvent e
	  | NestedQuery q' -> NestedQuery (check_inj_coherent_r q'))) ll)
  else q

let check_inj_coherent = function
    (PutBegin(_,_) as q) -> q
  | RealQuery q -> RealQuery (check_inj_coherent_r q)


let transl_query (env,q) =
  let q' = check_query_list (create_env env) q in
  let q'' = List.map check_inj_coherent q' in
  Pievent.init_event_status_table event_fun_table;
  List.iter Pievent.set_event_status q'';
  q''

(* Give the fact to query from the detailed query
   This is used only to create a resembling specification for SPASS
 *)

let query_to_facts q =
  let facts = ref [] in
  List.iter (function
      PutBegin(_) -> ()
    | RealQuery(Before(e,_)) -> match e with
	QSEvent(_,(FunApp(f,l) as param)) -> 
	  facts := 
	    (if (Pievent.get_event_status f).end_status = Inj then
	      Pred(Param.end_pred_inj, [Var(Terms.new_var "endsid" Param.sid_type);param])
	    else
	      Pred(Param.end_pred, [param])) :: (!facts)
      | QSEvent(_, _) ->
	  user_error ("Events should be function applications\n")
      | QFact(p,l) ->
	  facts := (Pred(p,l)) :: (!facts)
      | QNeq _ | QEq _ -> internal_error "no Neq/Eq queries"
	    ) q;
  !facts

(* After its translation, the arguments of names in the query are
   given type Param.tmp_type The exact types of the arguments of each
   name function symbol is computed during the translation of the
   process. The following functions scan the query to update the names
   with their real type. *)

let rec update_type_names_t = function
    Var v ->
      begin
	match v.link with
	  PGTLink (env, t) ->
	    let (t', _) = check_query_term env t in
	    v.link <- TLink t';
	    t'
	| TLink t -> t
	| NoLink -> Var v
	| _ -> internal_error "unexpected link in update_type_names_t"
      end
  | FunApp(f,l) -> FunApp(f, List.map update_type_names_t l)
      

let update_type_names_e = function
    QSEvent(b,t) -> QSEvent(b, update_type_names_t t)
  | QFact(p,tl) -> QFact(p, List.map update_type_names_t tl)
  | QNeq(t1,t2) -> QNeq(update_type_names_t t1, update_type_names_t t2)
  | QEq(t1,t2) -> QEq(update_type_names_t t1, update_type_names_t t2)

let rec update_type_names_r = function
    Before(ev,hypll) -> Before(update_type_names_e ev, List.map (List.map update_type_names_h) hypll)

and update_type_names_h = function
    QEvent(ev) -> QEvent(update_type_names_e ev)
  | NestedQuery(q) -> NestedQuery(update_type_names_r q)

let update_type_names = function
    PutBegin(b,l) -> PutBegin(b,l)
  | RealQuery q -> RealQuery(update_type_names_r q)

(* Noninterf queries *)

let get_noninterf_queries () =
  !noninterf_list

(* Weaksecret queries *)

let get_weaksecret_queries () =
  !weaksecret_list

(* Not declarations *)

let get_not() =
  List.map (fun (env, no) -> check_event (create_env env) no) (!not_list)

(* For Nounif. Very similar to queries, except that *v is allowed
   and events are not allowed *)

let fget_ident_any env (s, ext) =
   try
     match StringMap.find s env with
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



let rec check_gformat env (term, ext0) =
  match term with
    PFGIdent i -> fget_ident_any env i
  | PFGFunApp((s,ext),l) -> 
      begin
        try
          match StringMap.find s env with
            EFun f -> 
              (match f.f_cat with
                 Eq _ | Tuple -> ()
               | _ ->  input_error ("function " ^ s ^ " is defined by \"reduc\". Such a function should not be used in a \"nounif\" declaration") ext);
	      let (l', tl') = List.split (List.map (check_gformat env) l) in
	      if Terms.eq_lists (fst f.f_type) tl' then 
		if (f.f_options land Param.fun_TYPECONVERTER != 0) && (!Param.ignore_types) then
		  match l' with
		    [t] -> (t, snd f.f_type)
		  | _ -> internal_error "type converter functions should always be unary"
		else
		  (FFunApp(f, l'), snd f.f_type)
	      else
		input_error ("function " ^ s ^ " expects arguments of type " ^ 
			     (Terms.tl_to_string ", " (fst f.f_type)) ^
			     " but is given arguments of type " ^
			     (Terms.tl_to_string ", " tl')) ext
          | _ -> input_error("only functions can be applied, not " ^ s) ext
        with Not_found ->
          input_error ("function " ^ s ^ " not defined") ext
      end
  | PFGTuple l -> 
      let (l', tl') = List.split (List.map (check_gformat env) l) in
      (FFunApp(Terms.get_tuple_fun tl', l'), Param.bitstring_type)
  | PFGAny (s,ext) -> 
      begin
	try
	  match StringMap.find s env with
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
  | PFGName ((s,ext),bl) -> 
      begin
	try
	  let r = Hashtbl.find glob_table s in
	  check_single ext s;
	  if fst r.f_type == Param.tmp_type then
	    Parsing_helper.internal_error "Names should have their arity at this point"
	  else
	    begin
	      match r.f_cat with 
		Name { prev_inputs_meaning = sl } ->
		  List.iter (fun ((s',ext'),_) -> 
		    if not (List.mem s' sl) then
		      input_error ("variable " ^ s' ^ " not defined at restriction " ^ s) ext') bl;
		  let p = List.map2 (fun s'' ty ->
		    fbinding_find env s'' ty bl) sl (fst r.f_type) 
		  in
		  (FFunApp(r, p), snd r.f_type)
	      | _ -> internal_error "name expected here"
	    end
	with Not_found ->
	  input_error (s ^ " should be a name") ext
      end
  | PFGLet(id,t,t') -> check_gformat (add_fbinding env (id,t)) t'

and fbinding_find env s ty = function
    [] -> FAny (Terms.new_var Param.def_var_name ty)
  | ((s',ext),t)::l ->
      if s' = s then
	begin
	  let (t', ty') = check_gformat env t in
	  if ty' != ty then
	    input_error ("this variable is of type " ^ ty.tname ^ " but is given a value of type " ^ ty'.tname) ext;
	  t'
	end
      else
	fbinding_find env s ty l

and add_fbinding env ((i,ext),t) =
  begin
    try
      match StringMap.find i env with
	EVar _ -> input_error ("variable " ^ i ^ " already defined") ext
      | _ -> ()
    with Not_found -> ()
  end;
  let (t', ty') = check_gformat env t in
  let v = Terms.new_var i ty' in
  v.link <- FLink t';
  StringMap.add i (EVar v) env


let check_gfact_format env ((s, ext), tl, n) =
  match s with
    "attacker" ->
      begin
	match tl with
	  [t1] ->
	    if n > !Param.max_used_phase then
	      input_warning "nounif declaration for a phase greater than used" ext;
	    let (t1', ty1) = check_gformat env t1 in
	    let att_n = Param.get_pred (Attacker((if n = -1 then (!Param.max_used_phase) else n), ty1)) 
	    in
	    (att_n, [t1'])
	| _ -> 
	    input_error "arity of predicate attacker should be 1" ext
      end
  | "mess" ->
      begin
	match tl with
	  [t1;t2] ->
	    if n > !Param.max_used_phase then
	      input_warning "nounif declaration for a phase greater than used" ext;
	    let (t1', ty1) = check_gformat env t1 in
	    let (t2', ty2) = check_gformat env t2 in
	    if ty1 != Param.channel_type then
	      input_error ("First argument of mess is of type " ^ ty1.tname ^ " and should be of type channel") ext;
	    let mess_n = Param.get_pred (Mess((if n = -1 then (!Param.max_used_phase) else n), ty2)) 
	    in
	    (mess_n, [t1';t2'])
	| _ -> 
	    input_error "arity of predicate mess should be 2" ext
      end
  | s ->
      if n != -1 then
	input_error "declared predicates do not depend on phases, so no phase should be specified in such facts in queries" ext;
      let (tl', tyl) = List.split (List.map (check_gformat env) tl) in
      (get_pred env (s,ext) tyl, tl')

let rec handle_nounif env = function
    BFLet(id,t,nounif) -> handle_nounif (add_fbinding env (id,t)) nounif
  | BFNoUnif(fact,n) -> (check_gfact_format env fact, -n)

let get_nounif() =
  List.map (fun (env, nounif) -> handle_nounif (create_env env) nounif) (!nounif_list)
  

