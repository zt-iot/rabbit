type to_tamarin_error =
	| UnintendedError 
	| NotSupportedYet 

exception Error of to_tamarin_error Location.located

(** [error ~loc err] raises the given runtime error. *)
let error ~loc err = Stdlib.raise (Error (Location.locate ~loc err))

(** Print error description. *)
let print_error err ppf =
  match err with
  | UnintendedError -> Format.fprintf ppf "Unintended Error: contact the developer."
  | NotSupportedYet -> Format.fprintf ppf "This feature is not supported yet."


(* we do not do well-formedness check (at the moment..) *)
type functions = (string * int) list 

type expr = 
  | Var of string
  | Apply of string * expr list
  | String of string

type equations = (expr * expr) list
type signature = functions * equations 

let empty_signature = [] * [] 

type fact = string * expr list
type rule = string * fact list * fact list * fact list

type tamarin = signature * rule list

let add_rule t s = (fst t, s::(snd t))

let empty_tamarin = empty_signature * []

type engine = {
	namespace : string; 
	scope : string; 
	index : int;
	lctx : (string list) list
}

let flat lctx = 
	List.fold_left (fun l vl -> l @ vl) [] lctx

let eng_var_list eng =
	List.map (fun s -> Var s) (flat lctx)

let eng_state eng =
	eng.namespace ^ eng.scope ^ (string_of_int eng.index)

let eng_add_var eng v =
   match eng.lctx with 
   | f::frames -> {eng with lctx=(v::f)::frames}
   | _ -> error ~loc (UnintendedError)

let eng_add_frame eng = {eng with lctx=([]::eng.lctx)}

let eng_pop_frame eng = 
   match eng.lctx with 
   | f::frames -> {eng with lctx=frames}
   | _ -> error ~loc (UnintendedError)

let eng_inc_index eng =
	{eng with index=eng.index+1}      

let eng_lctx_back eng = 
	List.map (fun s -> Var s) (List.hd (List.rev eng.lctx))




let rec translate_expr  {Location.data=e; Location.loc=loc} = 
   let translate_expr' = function
	| Syntax.ExtConst s -> Apply (s, [])
	| Syntax.Const s -> error ~loc UnintendedError
	| Syntax.Variable (v, i,j,k) -> Var v
	| Syntax.Boolean b -> error ~loc UnintendedError
	| Syntax.String s -> error ~loc UnintendedError
	| Syntax.Integer z -> error ~loc UnintendedError
	| Syntax.Float f -> error ~loc UnintendedError
	| Syntax.Apply (o, el) -> Apply (o, List.map translate_expr el)
	| Syntax.Tuple el -> error ~loc UnintendedError
	| Syntax.Channel (c, l) -> error ~loc UnintendedError
	| Syntax.FrVariable v -> error ~loc UnintendedError
  in process_expr' ~fr ctx lctx e


let rec translate_stmt eng t  {Location.data=c; Location.loc=loc} = 
  match c with
  | Syntax.OpStmt a -> translate_atomic_stmt namespace t lctx a
  | Syntax.EventStmt (a, el) -> translate_atomic_stmt namespace t lctx a
  	
and translate_atomic_stmt eng t  {Location.data=c; Location.loc=loc} =
  
  let translate_atomic_stmt' eng t c = 
	  let state_i = eng_state eng in
	  let eng_f = eng_inc_index eng in
	  let state_f = eng_state eng_f in
	match c with
	| Syntax.Skip -> 
		(eng_f, 
			add_rule t (state_i, [(state_i, eng_var_list eng)], [], 
									[(state_f, eng_var_list eng)]))
	
	| Syntax.Let ((v, vi,vj,vk), e) -> 
		(eng_add_var eng_f v,
			add_rule t (state_i, [(state_i, eng_var_list eng)], [], 
									[(state_f, (translate_expr e) :: eng_var_list)]))
	
	| Syntax.Call ((v, vi,vj,vk), f, args) -> 
		let eng_f = eng_add_var eng_f v in 
		let t = add_rule t (state_i^"in", [(state_i, eng_var_list eng)], [], 
										[(state_i^"wait", eng_var_list eng) ; 
										(eng.namespace^f, 
											(* maybe need to be reversed. check! *)
											(List.map (translate_expr) args) @ eng_lctx_back eng)]) in 
		let t = add_rule t (state_i^"out", 
			[(state_i^"wait", eng_var_list eng) ; 
			(eng.namespace^f^"return", [Var v])], [], 
			[(state_f, eng_var_list eng_f)]) in
		(eng_f, t)

	| Syntax.Syscall ((v, vi,vj,vk), f, args) -> 
		let eng_f = eng_add_var eng_f v in 
		let t = add_rule t (state_i^"in", [(state_i, eng_var_list eng)], [], 
										[(state_i^"wait", eng_var_list eng) ; 
										(mk_rule_name f, (String eng.namespace) :: (List.map (translate_expr) args))]) in
		let t = add_rule t (state_i^"out", 
			[(state_i^"wait", eng_var_list eng) ; 
			((mk_rule_name f)^"return", [Var v])], [], 
			[(state_f, eng_var_list eng_f)]) in
		(eng_f, t)

	| Syntax.If (e, c1, c2) -> error ~loc UnintendedError 

	| Syntax.For (v, i, j, c) -> error ~loc UnintendedError
in translate_atomic_stmt' eng t c



(* type process = {
   proc_pid       :  int ; 
   proc_name      :  string ; 
   proc_attack    :  Input.attack_class list ; 
   proc_channel   :  (Name.ident * Name.ident list * Input.attack_class list) list;
   proc_file      :  (Name.ident * Syntax.expr * Name.ident list * Input.attack_class list) list ;
   proc_variable  :  (Name.ident * Syntax.expr) list ; 
   proc_function  :  (Name.ident * Name.ident list * Syntax.stmt list * Syntax.indexed_var ) list ;
   proc_main      :  Syntax.stmt list 
}

type system = {
   sys_ctx : context ; 
   sys_def : definition ;
   sys_pol : access_policy ;
   sys_proc : process list 
} *)

(* def_ext_syscall : (Name.ident * (Name.ident list * Name.ident list) * Name.ident list * (Syntax.fact list * Syntax.fact list ) list * Syntax.expr option) list ; *)

(*   | Fact of Name.ident * expr list
  | LocalFact of Name.ident * Name.ident * expr list
 *)
let translate_syscall t (f, args, taged_args, meta_vars, rules, ret) = 
	let translate_fact f = 
	match f.Location.data with
	| Syntax.Fact (s, el) -> (s, (Var "namespace") :: (List.map  translate_expr el))
	| Syntax.LocalFact (scope, s, el) -> (s, (Var scope) :: (List.map  translate_expr el))
	in
	let namespace = mk_rule_name f in
	let i = 0 in
	let myargs = (Var "namespace") :: (List.map (fun s -> Var s) args) in 
	let t = add_rule t (namespace, [(namespace, myargs)], [], [(namespace^(string_of_int i), myargs)]) in
	let (i, t) = List.fold_left (fun (i, t) (pre, post) -> 
		if i = List.length rules - 1 then
		(i+1, add_rule t (namespace^(string_of_int i), 
			[(namespace^(string_of_int i), myargs) ; (List.map translate_fact pre)], [], 
			[(namespace^"return", 
				match ret with 
				| Some e -> [translate_expr e]
				| None -> [String ""]) ; (List.map translate_fact post)]))
		else 

		(i+1, add_rule t (namespace^(string_of_int i), 
			[(namespace^(string_of_int i), myargs) ; (List.map translate_fact pre)], [], 
			[(namespace^(string_of_int (i + 1)), myargs) ; (List.map translate_fact post)])))
	in t 

let translate_process t {
  Context.proc_pid=k;
  Context.proc_name=s;
  Context.proc_attack=attks;
  Context.proc_channel=chs;
  Context.proc_file=fls;
  Context.proc_variable=vars;
  Context.proc_function=fns;
  Context.proc_main=m
} =
	let namespace = String.capitalize_ascii (s ^ (string_of_int k)) in (* this must be unique *)
	let eng = {namespace=namespace ; scope="init" ; index=0; lctx=[[]]} in

	let t = add_rule t (namespace^"_init", [], [(namespace^"_init", [])], [(eng_state eng, [])]) in

	(* initialize memory *)
	let (eng, t) = List.fold_left
		(fun (eng, t) (x, e) -> 
		let state_i = eng_state eng in
		let eng_f = eng_inc_index eng in 
		let eng_f = eng_add_var eng_f x in 
		let state_f = eng_state eng_f in

		let t = add_rule t (state_i, [(state_i, eng_var_list eng)], 
									[], 
									[(state_f, eng_state eng_f)]) in
		(eng_f, t)) (eng, t) vars in 

	let translate_function eng t (f, args, stmts, (v, vi, vj, vk)) = 
		let eng = eng_set_scope eng f in 
		let eng = eng_add_frame eng in 
		let eng = List.fold_left (fun eng v -> eng_add_var eng v) eng args in 
		let t = add_rule t (eng.namespace^f, [(eng.namespace^f, eng_var_list eng)], [], [(eng_state eng, eng_var_list eng)]) in
		let eng, t = List.fold_left (fun (eng, t) stmt -> translate_atomic_stmt eng t stmt) (eng, t) stmts in
		let t = add_rule t (eng.namespace^f^"return", [(eng_state eng, eng_var_list eng)] [] [(eng.namespace^f^"return", [Var v])]) in 
		t in 

	let t = List.fold_left (fun t f -> translate_function eng t f) t fns in

	let eng_main = eng_set_scope eng "main" in 
	let t = add_rule t (namespace^"_main", [(eng_state eng, eng_var_list eng)], [], [(eng_state eng, eng_var_list eng)]) in 

	let eng = eng_add_frame eng_main in 
	let eng, t = List.fold_left (fun (eng, t) stmt -> translate_atomic_stmt eng t stmt) (eng, t) m in
	t



