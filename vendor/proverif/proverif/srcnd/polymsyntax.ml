let rec gen_env polym env = function
    [] -> env
  | ((s,ext),ty)::l ->
      let t = get_type_polym polym ty in
      try
	ignore(Hashtbl.find fun_decls s);
	input_error ("variable " ^ s ^ " already defined as a function") ext
      with Not_found ->
      try
	ignore(Hashtbl.find name_env s);
	input_error ("variable " ^ s ^ " already defined as a name") ext
      with Not_found ->
      try
	ignore(Hashtbl.find env s);
	input_error ("variable " ^ s ^ " already defined") ext
      with Not_found ->
	let v = Terms.new_var s t in
	Hashtbl.add env s v;
	gen_env env l

let create_env polym l = gen_env polym (Hashtbl.create 7) l

(* Tools to instantiate polymorphic variables *)

let change_type_term env' = function
    Var v ->
      begin
	try
	  List.assq env' v
	with
	  Not_found -> v
      end
  | FunApp(f,l) -> FunApp(f,l) (* No polymorphic function for now *)

let change_type_fact env' = function
    Out(t,l) -> Out(t,l)
  | Pred(p,l) -> 
      let l' = List.map (change_type_term env') l in
      let tl' = List.map Terms.get_term_type l' in
      if not (List.for_all2 (fun t1 t2 -> t1 == t2 || t1 == Param.any_type) p.p_type tl') then
	internal_error ("predicate " ^ c ^ " expects arguments of type " ^ 
			(Terms.tl_to_string ", " p.p_type) ^
			" but is given arguments of type " ^
			(Terms.tl_to_string ", " tl')) ext;
      let p' = 
	if List.exists (fun t -> t == Param.any_type) p.p_type then
	  Param.get_pred (PolymPred(p.p_name, p.p_prop, tl'))
	else
	  p
      in
      Pred(p',l')

let iter_polym_env f env =
  let iter_rec f remap_env = function
      [] -> f remap_env
    | (v::l) ->
	if v.btype == Param.any_type then
	  List.iter (fun t' -> iter_rec f ((v,Terms.new_var v.sname t')::remap_env) l) (!Param.all_types)
	else
	  iter_rec f remap_env l
  in
  let var_list = ref [] in
  Hashtbl.iter (fun _ v -> var_list := v :: (!var_list)) env;
  iter_rec f [] (!var_list)




  | (TNoUnif (env,fact,n)) :: l ->
      let env = create_env true env in
      nounif_list = (env, check_cformat_fact env fact, -n) :: (!nounif_list);
      check_all l



	List.iter (fun (f,n) -> 
	  iter_polym_env (fun env' -> Selfun.add_no_unif (change_type_format) n) env;
