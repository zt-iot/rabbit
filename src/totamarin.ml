(* 
	For translating to and printing Tamarin models.

	* 'Rabbit' is a string value palceholder for void output of system calls and functions.
	* GlobalFact is fact that does not bound to any process or channel. Currently 
		it only contains reserved facts.


 *)


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


let mk_fact_name s = 
	String.capitalize_ascii s

let contains s1 s2 =
    let re = Str.regexp_string s2
    in
        try ignore (Str.search_forward re s1 0); true
        with Not_found -> false


(* we do not do well-formedness check (at the moment..) *)
type functions = (string * int) list 

type expr = 
  | Var of string
  | Apply of string * expr list
  | String of string
  | List of expr list

type equations = (expr * expr) list
type signature = functions * equations 

let empty_signature = ([], [])

type fact = string * expr list
type rule = string * fact list * fact list * fact list

type tamarin = signature * rule list

let add_rule t s = (fst t, s::(snd t))

let add_fun ((fns,eqns), rules) f = ((f::fns, eqns), rules)
let add_const ((fns,eqns), rules) c = (((c,0)::fns, eqns), rules)
let add_eqn ((fns,eqns), rules) eq = ((fns, eq::eqns), rules)


let empty_tamarin = empty_signature , []

let mult_list_with_concat l sep = 
	match l with
	| h :: t -> h ^ (List.fold_left (fun r s-> r ^ sep ^ s) "" t) 
	| [] -> ""

let rec print_expr e = 
	match e with
	| Var s -> s 
	| Apply (s, el) -> s ^ "(" ^ (mult_list_with_concat (List.map print_expr el) ", ") ^ ")"
	| String s -> "\'"^s^"\'"
	| List el -> 
		match el with
		| [] -> "\'sewon\'"
		| [e] -> print_expr e 
		| _ -> 	"<" ^ (mult_list_with_concat (List.map print_expr el) ", ") ^ ">"

let print_signature (fns, eqns) = 
	let print_functions fns = 
	"functions: "^(mult_list_with_concat (List.map (fun (f, ar) -> f ^"/"^(string_of_int ar)) fns) ", ") ^"\n" in 
	let print_equations eqns = 
	"equations: "^(mult_list_with_concat (List.map (fun (e1, e2) -> (print_expr e1)^"="^(print_expr e2)) eqns) ", ") ^"\n" in 
	(print_functions fns) ^ (print_equations eqns)

let print_rule (f, pre, label, post) = 
	let print_fact (f, el) = f^"(" ^ (mult_list_with_concat (List.map print_expr el) ", ") ^ ")" in 
	"rule "^f ^" : "^ 
	"["^(mult_list_with_concat (List.map print_fact pre) ", ") ^ "]" ^
	(match label with 
		| [] -> "-->" 
		| _ -> 	"--[" ^ (mult_list_with_concat (List.map print_fact label) ", ") ^ "]->")^

	"["^(mult_list_with_concat (List.map print_fact post) ", ") ^ "] \n"	

let print_tamarin ((sign, rules), init_list, lem) = 
	"theory rabbit\n\nbegin\n"^
	print_signature sign ^
	(mult_list_with_concat (List.map print_rule (List.rev rules)) "")^
	
	List.fold_left (fun l s -> l^"\nrestriction "^s^" : \" All #i #j . "^s^"() @ #i & "^s^"() @ #j ==> #i = #j \"") "" init_list ^

	List.fold_left (fun l (lem, prop) -> l^"\nlemma "^lem^" : "^prop) "" lem ^"\nend\n"

(* 

restriction Client0_init : 
  " All #i #j . Client0_init() @ #i & Client0_init() @ #j ==> #i = #j "

restriction Server1_init : 
  " All #i #j . Server1_init() @ #i & Server1_init() @ #j ==> #i = #j "

lemma Finish :
  exists-trace
  "Ex #j  . Querying() @ #j"
end
 *)
type engine = {
	namespace : string; 
	scope : string; 
	index : int;
	lctx : (string list) list;
	sep : string;
	mode : string;
	fresh_ident : string; 
	fresh_string : string;
}

let empty_engine = {namespace = ""; scope = ""; index = 0; lctx = [[]]; sep = ""; mode = ""; fresh_ident = ""; fresh_string = ""}

let eng_set_fresh_string eng s = {eng with fresh_string=s}
let eng_set_fresh_ident eng s = {eng with fresh_ident=s}

let eng_get_fresh_string eng = eng.fresh_string
let eng_get_fresh_ident eng = eng.fresh_ident

let flat lctx = 
	List.fold_left (fun l vl -> l @ vl) [] lctx

let eng_set_mode eng m = 
	{eng with mode=m}

let eng_var_list eng =
	List.map (fun s -> if s = "" then String (eng_get_fresh_string eng) else Var s) (flat eng.lctx)

let eng_state eng =
	eng.namespace ^ (if eng.scope = "" then "" else eng.sep ^ eng.scope) ^ (if eng.index = 0 then "" else eng.sep ^ string_of_int (eng.index - 1))
	^ (if eng.mode = "" then "" else eng.sep ^ eng.mode)

let eng_add_var eng v =
   match eng.lctx with 
   | f::frames -> {eng with lctx=(v::f)::frames}
   | _ -> error ~loc:Location.Nowhere (UnintendedError)

let eng_add_frame eng = {eng with lctx=([]::eng.lctx)}

let eng_pop_frame eng = 
   match eng.lctx with 
   | f::frames -> {eng with lctx=frames}
   | _ -> error ~loc:Location.Nowhere (UnintendedError)

let eng_inc_index eng =
	{eng with index=eng.index+1}      

let eng_lctx_back eng = 
	List.map (fun s -> if s = "" then String (eng_get_fresh_string eng) else Var s) (List.hd (List.rev eng.lctx))

let eng_set_scope eng s =
	{eng with scope=s ; index = 0}

let eng_set_namespace eng n = 
	{eng with namespace=mk_fact_name n ; scope = "" ; index = 0 ; lctx = [[]]}

let eng_set_sep eng sep = 
	{eng with sep=sep}

let eng_set_lctx eng lctx = 
	{eng with lctx=lctx}


let eng_suffix eng s v = 
	s ^ eng.sep ^ v


let rec translate_expr ?(ch=false) {Location.data=e; Location.loc=loc} = 
   let translate_expr' = function
	| Syntax.ExtConst s -> Apply (s, [])
	| Syntax.Const s -> error ~loc UnintendedError
	| Syntax.Variable (v, i,j,k) -> Var v
	| Syntax.Boolean b -> error ~loc UnintendedError
	| Syntax.String s -> String s
	| Syntax.Integer z -> error ~loc UnintendedError
	| Syntax.Float f -> error ~loc UnintendedError
	| Syntax.Apply (o, el) -> Apply (o, List.map (translate_expr ~ch:ch) el)
	| Syntax.Tuple el -> error ~loc UnintendedError
	| Syntax.Channel (c, l) -> if ch then Var c else String c
	| Syntax.FrVariable v -> error ~loc UnintendedError
  in translate_expr' e


let rec translate_stmt eng t  {Location.data=c; Location.loc=loc} = 
  match c with
  | Syntax.OpStmt a -> translate_atomic_stmt eng t a
  | Syntax.EventStmt (a, el) -> 
  	let eng, (sign, rules) = translate_atomic_stmt eng t a in 
  	match rules with
  	| (n, pre, label, post) :: rules -> (eng, (sign, (n, pre, 
  		List.map (fun ev -> match ev.Location.data with Syntax.Event(id, el) -> (mk_fact_name id, List.map translate_expr el)) el 
  		, post) :: rules))
  	| [] -> error ~loc UnintendedError 
  	
and translate_atomic_stmt eng t  {Location.data=c; Location.loc=loc} =
  
  let translate_atomic_stmt' eng t c = 
	  let state_i = eng_state eng in
	  let eng_f = eng_inc_index eng in
	  let state_f = eng_state eng_f in
	match c with
	| Syntax.Skip -> 
		(eng_f, 
			add_rule t (state_i, 
									[(eng.namespace, [String state_i ; (List (eng_var_list eng))])], 
									[], 
									[(eng.namespace, [String state_f ; (List (eng_var_list eng))])]
			))
	
	| Syntax.Let ((v, vi,vj,vk), e) -> 
		(eng_add_var eng_f v,
			add_rule t (state_i, 
									[(eng.namespace, [String state_i ; (List (eng_var_list eng))])], 
									[], 
									[(eng.namespace, [String state_f ; (List ((translate_expr e) :: eng_var_list eng))])]
			))
	
	| Syntax.Call ((v, vi,vj,vk), f, args) -> 
		let eng_f = eng_add_var eng_f v in 
		let t = add_rule t (eng_state (eng_set_mode eng "in"), 
											[(eng.namespace, [String state_i ; (List (eng_var_list eng))])], 
											[], 
											[
												(eng_state (eng_set_mode eng "wait"), eng_var_list eng) ; 
										 		(eng.namespace, [String (eng_state (eng_set_scope eng f)) ; (List ((List.map (translate_expr) args) @ eng_lctx_back eng))])
											(* maybe need to be reversed. check! *)
											]) in 
		let t = add_rule t (eng_state (eng_set_mode eng "out"), 
			[(eng_state (eng_set_mode eng "wait"), eng_var_list eng) ; 
			(eng_state (eng_set_mode (eng_set_scope eng f) "return"), [(match v with |"" -> Var (eng_get_fresh_ident eng) |_->Var v)])], [], 
			[(eng.namespace, [String state_f ; (List (eng_var_list eng_f))])]) in
		(eng_f, t)

	| Syntax.Syscall ((v, vi,vj,vk), f, args) -> 
		let eng_f = eng_add_var eng_f v in 
		

		let t = add_rule t (eng_state (eng_set_mode eng "in"), 
										[(eng.namespace, [String state_i ; (List (eng_var_list eng))])], 
										[], 
										[(eng_state (eng_set_mode eng "wait"), eng_var_list eng) ; 
										(mk_fact_name f, (String eng.namespace) :: (List.map (translate_expr) args))]) in


		let t = add_rule t (eng_state (eng_set_mode eng "out"), 
			[(eng_state (eng_set_mode eng "wait"), eng_var_list eng) ; 
			(eng_state (eng_set_mode (eng_set_namespace eng f) "return"), [(String eng.namespace) ; (match v with |"" -> Var (eng_get_fresh_ident eng) |_->Var v) ])], [], 
			[(eng.namespace, [String state_f ; (List (eng_var_list eng_f))])]) in
		(eng_f, t)

	| Syntax.If (e, c1, c2) -> error ~loc UnintendedError 

	| Syntax.For (v, i, j, c) -> error ~loc UnintendedError
in translate_atomic_stmt' eng t c

let translate_syscall eng t (f, args, taged_args, meta_vars, rules, ret) = 
	
	let namespace_string = 
		(let rec f s = if List.exists (fun u -> u = s) (args @ meta_vars) then f (s ^ "_") else s in f "proc") in                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      

	let namespace_id = (Var namespace_string) in
	let eng = eng_set_namespace eng f in 
	let eng = eng_set_lctx eng [args] in 
	let eng = eng_add_var eng namespace_string in

	let translate_fact f = 
	match f.Location.data with
	| Syntax.GlobalFact (s, el) -> (s, (List.map  (translate_expr ~ch:true) el))
	| Syntax.Fact (s, el) -> (mk_fact_name s, namespace_id :: (List.map  (translate_expr ~ch:true) el))
	| Syntax.LocalFact (scope, s, el) -> (mk_fact_name s, (Var scope) :: (List.map  (translate_expr ~ch:true) el))
	in
	let (_, _, t) = List.fold_left (fun (eng, i, t) (pre, post) -> 
		if i = List.length rules - 1 then
		(eng, i+1, add_rule t (eng_state eng, 
			(eng_state eng, eng_var_list eng) :: (List.map translate_fact pre), [], 
			(eng_suffix eng eng.namespace "return", [namespace_id ;
				match ret with 
				| Some e -> translate_expr ~ch:true e
				| None -> String (eng_get_fresh_string eng)]) :: (List.map translate_fact post)))
		else 
		(eng_inc_index eng, i+1, add_rule t (eng_state eng, 
			(eng_state eng, eng_var_list eng) :: (List.map translate_fact pre), [], 
			(eng_state (eng_inc_index eng), eng_var_list eng) :: (List.map translate_fact post)))) (eng, 0, t) (List.rev rules)
	in t 

let translate_process eng t {
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
	let eng = eng_set_namespace eng namespace in 
	let eng = eng_set_scope eng "init" in 

	let t = add_rule t (eng_state eng, [], [(namespace^eng.sep^"init", [])], [(namespace, [String (eng_state eng) ; List []])]) in

	(* initialize memory *)
	let (eng, t) = List.fold_left
		(fun (eng, t) (x, e) -> 
		let state_i = eng_state eng in
		let eng_f = eng_inc_index eng in 
		let eng_f = eng_add_var eng_f x in 
		let state_f = eng_state eng_f in

		let t = add_rule t (state_f, 
									[(namespace, [String state_i; List (eng_var_list eng)])], 
									[], 
									[(namespace, [String state_f ; List (translate_expr e :: eng_var_list eng)])]) in
		(eng_f, t)) (eng, t) vars in 

	let translate_function eng t (f, args, stmts, (v, vi, vj, vk)) = 
		let eng = eng_set_scope eng f in 
		let eng = eng_add_frame eng in 
		let eng = List.fold_left (fun eng v -> eng_add_var eng v) eng args in 
		(* let t = add_rule t (eng.namespace^f, [(eng.namespace^f, eng_var_list eng)], [], [(eng_state eng, eng_var_list eng)]) in *)
		let eng, t = List.fold_left (fun (eng, t) stmt -> translate_stmt eng t stmt) (eng, t) stmts in
		let eng_return = eng_set_mode (eng_set_scope eng f) "return" in 

		let t = add_rule t (eng_state eng_return, [(namespace, [String (eng_state eng); List (eng_var_list eng)])], [], [(eng_state eng_return, [Var v])]) in 
		t in 

	let t = List.fold_left (fun t f -> translate_function eng t f) t fns in

	let eng_main = eng_set_scope eng "main" in 
	let t = add_rule t (eng_state eng_main, [(namespace, [String (eng_state eng); List (eng_var_list eng)])], [], 
																					[(namespace, [String (eng_state eng_main); List (eng_var_list eng_main)])]) in 

	let eng = eng_add_frame eng_main in 
	let eng, t = List.fold_left (fun (eng, t) stmt -> translate_stmt eng t stmt) (eng, t) m in
	t



let get_fact_names ctx = 
	(List.map (fun (a,_,_) -> a) ctx.Context.ctx_fact) @ 
	(List.map fst ctx.Context.ctx_event) @ 
	(List.map fst ctx.Context.ctx_ext_syscall) @ 
	(List.fold_left (fun l proc -> 
		[proc.Context.ctx_proctmpl_id] @
		List.map fst proc.Context.ctx_proctmpl_func @
		l) [] ctx.Context.ctx_proctmpl)


let translate_sys {
   Context.sys_ctx = ctx ; 
   Context.sys_def = def;
   Context.sys_pol = pol;
   Context.sys_proc = proc ;
   Context.sys_lemma = lem
} (used_idents, used_string) = 
	let t = empty_tamarin in
	let eng = empty_engine in
	let eng = eng_set_sep eng 
	(let names = get_fact_names ctx in 
		let rec f s = if List.exists (fun u -> contains u s) names then f (s ^"_") else s in 
		f "_") in
	let eng = eng_set_fresh_ident eng 
	(
		let rec f s = if List.exists (fun u -> u = s) used_idents then f (s^"_") else s in 
		f "rabbit"
	) in 

	let eng = eng_set_fresh_string eng 
	(
		let rec f s = if List.exists (fun u -> u = s) used_string then f (s^"_") else s in 
		f "rabbit"
	) in 
	

	(* process what has been defined first! *)
	let t = List.fold_left (fun t (f, k) -> add_fun t (f, k)) t (List.rev ctx.Context.ctx_ext_func) in
	
	let t = List.fold_left (fun t c -> add_const t c) t (List.rev ctx.Context.ctx_ext_const) in
	
	let t = List.fold_left (fun t (_, e1, e2) -> add_eqn t (translate_expr e1, translate_expr e2)) t (List.rev def.Context.def_ext_eq) in

	let t = List.fold_left (fun t r -> translate_syscall eng t r) t (List.rev def.Context.def_ext_syscall) in

	let t = List.fold_left (fun t p -> translate_process eng t p) t (List.rev proc) in

	let init_list = List.map (fun p -> String.capitalize_ascii (p.Context.proc_name ^ (string_of_int p.Context.proc_pid)) ^ eng.sep^"init") proc in 

	(t, init_list, lem)


