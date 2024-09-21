(* 
	For translating to and printing Tamarin models.
	* 'Rabbit' is a string value palceholder for void output of system calls and functions.
	* GlobalFact is fact that does not bound to any process or channel. Currently 
		it only contains reserved facts.
 *)

type to_tamarin_error =
	| UnintendedError of string
	| NotSupportedYet 

exception Error of to_tamarin_error Location.located

(** [error ~loc err] raises the given runtime error. *)
let error ~loc err = Stdlib.raise (Error (Location.locate ~loc err))

(** Print error description. *)
let print_error err ppf =
  match err with
  | UnintendedError s -> Format.fprintf ppf "Unintended Error: contact the developer. [Hint: %s]" s
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
  | Integer of int
  | List of expr list

type equations = (expr * expr) list
type signature = functions * equations 

let empty_signature = ([], [])

type rule_config = {is_persist : bool ; is_delayed : bool}

let config_linear = {is_persist=false; is_delayed=false}
let config_persist = {is_persist=true; is_delayed=false}
let config_linear_delayed = {is_persist=false; is_delayed=true}
let config_persist_delayed = {is_persist=true; is_delayed=true}


type fact = string * expr list * rule_config 
(* true is persistent fact *)
type rule = 
	| Rule of string * string * fact list * fact list * fact list
	| Comment of string

type tamarin = signature * rule list

let add_rule t (a, b, c, d, e) = (fst t, (Rule (a, b, c, d, e)) :: ( (snd t)))
let add_comment t s = (fst t, (Comment s):: ( (snd t)))

let add_fun ((fns,eqns), rules) f = ((f::fns, eqns), rules)
let add_const ((fns,eqns), rules) c = (((c,0)::fns, eqns), rules)
let add_eqn ((fns,eqns), rules) eq = ((fns, eq::eqns), rules)


let empty_tamarin = empty_signature , []

let mult_list_with_concat l sep = 
	match l with
	| h :: t -> h ^ (List.fold_left (fun r s-> r ^ sep ^ s) "" t) 
	| [] -> ""

type printer = {prt_sep:string}
let replace_string s t str = 
	String.concat t (String.split_on_char s str)

let rec print_expr prt e = 
	match e with
	| Var s -> s 
	| Apply (s, el) -> s ^ "(" ^ (mult_list_with_concat (List.map (print_expr prt) el) ", ") ^ ")"
	| String s -> "\'rabbit" ^ prt.prt_sep ^ (replace_string '/' prt.prt_sep s)^"\'"
	| Integer i -> "\'"^string_of_int i^"\'"
	| List el -> 
		match el with
		| [] -> "\'rabbit"^prt.prt_sep^"\'"
		| [e] -> print_expr prt e 
		| _ -> 	"<" ^ (mult_list_with_concat (List.map (print_expr prt) el) ", ") ^ ">"

let print_signature prt (fns, eqns) = 
	let print_functions fns = 
	(if List.length fns = 0 then "" else "functions: ")^(mult_list_with_concat (List.map (fun (f, ar) -> f ^"/"^(string_of_int ar)) fns) ", ") ^"\n" in 
	let print_equations eqns = 
	(if List.length eqns = 0 then "" else "equations: ")^(mult_list_with_concat (List.map (fun (e1, e2) -> (print_expr prt e1)^"="^(print_expr prt e2)) eqns) ", ") ^"\n" in 
	(print_functions fns) ^ (print_equations eqns)

let print_rule2 prt (f, act, pre, label, post) dev = 
	let print_fact (f, el, b) = 
	(if b.is_persist then "!" else "") ^f^"(" ^ (mult_list_with_concat (List.map (print_expr prt) el) ", ") ^ ")" 
	^ (if b.is_delayed then "[-,no_precomp]" else "") 
	in 
	let print_fact2 (f, el, b) = 
	(if b.is_persist then "!" else "") ^f^"(" ^ (mult_list_with_concat (List.map (print_expr prt) el) ", ") ^ ")" in 
	"rule "^f ^
	(if act = "" || not dev then "" else "[role=\"" ^act^ "\"]") ^
	" : "^ 
	"["^(mult_list_with_concat (List.map print_fact pre) ", ") ^ "]" ^
	(match label with 
		| [] -> "-->" 
		| _ -> 	"--[" ^ (mult_list_with_concat (List.map print_fact2 label) ", ") ^ "]->")^

	"["^(mult_list_with_concat (List.map print_fact2 post) ", ") ^ "] \n"	

let print_comment s = "\n// "^s^"\n\n" 

let print_rule prt r dev = match r with | Rule (a, b, c, d, e) -> print_rule2 prt (a, b, c, d, e) dev | Comment s ->print_comment s 

let print_tamarin prt ((sign, rules), init_list, lem) dev = 
	"theory rabbit\n\nbegin\n"^
	print_signature prt sign ^
	(mult_list_with_concat (List.map (fun r -> print_rule prt r dev) (List.rev rules)) "")^
	
	List.fold_left (fun l s -> l^"\nrestriction "^s^" : \" All #i #j . "^s^"() @ #i & "^s^"() @ #j ==> #i = #j \"") "" init_list ^ "\n" ^

	(* if then else restriction *)

	(* "\nrestriction OnlyOnce : \" All x #i #j . OnlyOnce(x) @ #i & OnlyOnce(x) @ #j ==> #i = #j \"\n" ^ *)

	"restriction Equality: \" All x y #i. Eq(x,y) @ #i ==> x = y\"\n" ^

	"restriction Inequality: \"All x #i. Neq(x,x) @ #i ==> F\"\n" ^

	"rule Equality_gen: [] --> [!Eq"^prt.prt_sep^"(x,x)]\n" ^

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
	mode : string list;
	fresh_ident : string; 
	fresh_string : string;
	filesys : string;
	role : string;
	func : string; 
}

let empty_engine = {namespace = ""; scope = ""; func = ""; index = 0; lctx = [[]]; sep = ""; mode = []; fresh_ident = ""; fresh_string = ""; filesys = ""; role = ""}

let eng_set_role eng s = {eng with role=s}
let eng_get_role eng = eng.role 
let eng_set_fresh_string eng s = {eng with fresh_string=s}
let eng_set_fresh_ident eng s = {eng with fresh_ident=s}
let eng_set_func eng s = {eng with func=s}
let eng_get_frame_title eng = 
	"Frame"^eng.sep^eng.namespace ^ (if eng.func = "" then "" else eng.sep ^ eng.func) 

let eng_get_fresh_string eng = eng.fresh_string
let eng_get_fresh_ident eng = eng.fresh_ident

let eng_set_filesys eng s = {eng with filesys=s}
let eng_get_filesys eng = eng.filesys
let flat lctx = 
	List.fold_left (fun l vl -> l @ vl) [] lctx

let eng_set_mode eng m = 
	{eng with mode=m :: eng.mode}

let eng_var_list eng =
	List.map (fun s -> if s = "" then String (eng_get_fresh_string eng) else Var s) (flat eng.lctx)

let eng_var_list_loc eng = 
	match List.rev eng.lctx with
	| t :: l -> List.map (fun s -> if s = "" then String (eng_get_fresh_string eng) else Var s) (flat (List.rev l))
	| [] -> error ~loc:Location.Nowhere (UnintendedError "lctx is empty")

let eng_var_list_top eng = 
	match List.rev eng.lctx with
	| t :: l -> List.map (fun s -> if s = "" then String (eng_get_fresh_string eng) else Var s) (flat (List.rev [t]))
	| [] -> error ~loc:Location.Nowhere (UnintendedError "lctx is empty")


let eng_state eng =
	eng.namespace ^ 
	(if eng.scope = "" then "" else eng.sep ^ eng.scope) ^ 
	(if eng.index = 0 then "" else eng.sep ^ string_of_int (eng.index - 1)) ^ 
	if List.length eng.mode = 0 then "" else eng.sep ^
	mult_list_with_concat (List.rev eng.mode) eng.sep

let eng_add_var eng v =
   match eng.lctx with 
   | f::frames -> {eng with lctx=(v::f)::frames}
   | _ -> error ~loc:Location.Nowhere (UnintendedError "adding var to translation engine")

let eng_add_frame eng = {eng with lctx=([]::eng.lctx)}

let eng_pop_frame eng = 
   match eng.lctx with 
   | f::frames -> {eng with lctx=frames}
   | _ -> error ~loc:Location.Nowhere (UnintendedError "popping a frame")

let eng_inc_index eng =
	{eng with index=eng.index+1}      

let eng_set_index eng n =
	{eng with index=n}      


let eng_lctx_back eng = 
	List.map (fun s -> if s = "" then String (eng_get_fresh_string eng) else Var s) (List.hd (List.rev eng.lctx))

let eng_set_scope eng s =
	{eng with scope=s ; index = 0}

let eng_set_namespace eng n = 
	{eng with namespace=mk_fact_name n ; scope = "" ; index = 0 ; lctx = [[]] ; mode=[]}

let eng_set_sep eng sep = 
	{eng with sep=sep}

let eng_set_lctx eng lctx = 
	{eng with lctx=lctx}

let eng_suffix eng s v = 
	s ^ eng.sep ^ v


let rec translate_expr ?(ch=false) {Location.data=e; Location.loc=loc} = 
   let translate_expr' = function
	| Syntax.ExtConst s -> Apply (s, [])
	| Syntax.Const s -> error ~loc (UnintendedError ("translating constant " ^ s))
	| Syntax.Variable (v, i,j,k) -> Var v
	| Syntax.Boolean b -> error ~loc (UnintendedError "translating boolean")
	| Syntax.String s -> String s
	| Syntax.Integer z -> error ~loc (UnintendedError "translating Integer")
	| Syntax.Float f -> error ~loc (UnintendedError "translating float")
	| Syntax.Apply (o, el) -> Apply (o, List.map (translate_expr ~ch:ch) el)
	| Syntax.Tuple el -> 
		List (List.map (translate_expr ~ch:ch) el)

	| Syntax.Channel (c, l) -> if ch then Var c else String c
	| Syntax.Process v -> Var v
	| Syntax.Path v -> Var v
	| Syntax.FrVariable v -> error ~loc (UnintendedError "translating free var")
	
  in translate_expr' e

let rec translate_expr2 ?(ch=false) {Location.data=e; Location.loc=loc} = 
   let translate_expr2' = function
	| Syntax.ExtConst s -> Apply (s, []), []
	| Syntax.Const s -> Var s, [s]
	| Syntax.Variable (v, i,j,k) -> Var v, []
	| Syntax.Boolean b -> error ~loc (UnintendedError "translating boolean")
	| Syntax.String s -> String s, []
	| Syntax.Integer z -> Integer z, []
	| Syntax.Float f -> error ~loc (UnintendedError "translating float")
	| Syntax.Apply (o, el) -> 
		let (el, sl) = List.fold_left (fun (el, sl) e -> 
			let e, s = translate_expr2 ~ch:ch e in 
				(el @ [e], sl @ s)) ([], []) el in 
		Apply (o, el), sl
	| Syntax.Tuple el -> 
			let (el, sl) = List.fold_left (fun (el, sl) e -> 
			let e, s = translate_expr2 ~ch:ch e in 
				(el @ [e], sl @ s)) ([], []) el in 
		List el, sl

	| Syntax.Channel (c, l) -> if ch then Var c, [] else String c, []
	| Syntax.Process v -> Var v, []
	| Syntax.Path v -> Var v, []
	| Syntax.FrVariable v -> error ~loc (UnintendedError "translating free var")
  in translate_expr2' e


let rec translate_stmt eng (t : tamarin) {Location.data=c; Location.loc=loc} syscalls = 
  match c with
  | Syntax.OpStmt a -> translate_atomic_stmt eng t a syscalls
  | Syntax.EventStmt (a, el) -> 
 
	  	let eng, (sign, rules) = translate_atomic_stmt eng t a syscalls in 
	  	match rules with
	  	| Rule (n, act, pre, label, post) :: rules -> 
	  		(eng, (sign, Rule (n, act, pre, 
	  			List.map (fun ev -> match ev.Location.data with Syntax.Event(id, el) -> (mk_fact_name id, List.map translate_expr el, config_linear)) el 
	  		, post) :: rules))
	  	| [] -> error ~loc (UnintendedError  "empty rule")
  	
and translate_atomic_stmt (eng : engine) (t: tamarin)  {Location.data=c; Location.loc=loc} syscalls =
  let translate_atomic_stmt' (eng : engine) (t : tamarin) c syscalls = 
  	let namespace =  eng.namespace in 
  	let role = eng_get_role eng in 
	  let state_i = eng_state eng in
	  let eng_f = eng_inc_index eng in
	  let state_f = eng_state eng_f in
	match c with
 	| Syntax.Skip -> 
		(eng_f, 
			add_rule t (state_i, role,
									[(eng_get_frame_title eng, [String state_i ; (List (eng_var_list_loc eng)) ; (List (eng_var_list_top eng))], config_linear)], 
									[], 
									[(eng_get_frame_title eng, [String state_f ; (List (eng_var_list_loc eng)) ; (List (eng_var_list_top eng))], config_linear)]
			)
		)
	| Syntax.Let ((v, vi,vj,vk), e) -> 
		let e, gv = translate_expr2 e in  
		let gv = List.map (fun s -> ("Const"^eng.sep, [String s ; Var s], config_persist)) gv in 
		(eng_add_var eng_f v,
			add_rule t (state_i, role,
									[(eng_get_frame_title eng, [String state_i ; (List (eng_var_list_loc eng)) ; (List (eng_var_list_top eng))], config_linear)]  @ gv , 
									[], 
									[(eng_get_frame_title eng, [String state_f ; (List (e:: eng_var_list_loc eng)) ; (List (eng_var_list_top eng))], config_linear)]
			))
	
	| Syntax.Call ((v, vi,vj,vk), f, args) -> 
		error ~loc:Nowhere (UnintendedError "function call")

(* 		let (el, gv) = List.fold_left (fun (el, sl) e -> 
			let e, s = translate_expr2 e in 
				(el @ [e], sl @ s)) ([], []) args in 
		let gv = List.map (fun s -> ("Const"^eng.sep, [String s ; Var s], config_persist)) gv in 


		let eng_f = eng_add_var eng_f v in 
		let t = add_rule t (eng_state (eng_set_mode eng "in"), namespace,
											[("Frame"^eng.sep^namespace, [String state_i ; (List (eng_var_list_loc eng)) ; (List (eng_var_list_top eng))], config_linear)]  @ gv, 
											[], 
											[
												(eng_state (eng_set_mode eng "wait"), eng_var_list eng, config_linear) ; 
										 		("Frame"^eng.sep^namespace, [String (eng_state (eng_set_scope eng f)) ; (List (el @ eng_lctx_back eng))], config_linear)
											(* maybe need to be reversed. check! *)
											]) in 
		let t = add_rule t (eng_state (eng_set_mode eng "out"), namespace,
			[(eng_state (eng_set_mode eng "wait"), eng_var_list eng, config_linear) ; 
			(eng_state (eng_set_mode (eng_set_scope eng f) "return"), [(match v with |"" -> Var (eng_get_fresh_ident eng) |_->Var v)], config_linear_delayed)], [], 
			[("Frame"^eng.sep^namespace, [String state_f ; (List (eng_var_list_loc eng_f)) ; (List (eng_var_list_top eng))], config_linear)]) in
		(eng_f, t)
 *)
	| Syntax.Syscall ((v, vi,vj,vk), f, args) -> 
		begin
		let (el, gv) = List.fold_left (fun (el, sl) (e, ty) -> 
			let e, s = translate_expr2 e in 
				(el @ [ match ty with |Input.TyPath -> List [String (eng_get_filesys eng) ; e]|_ ->  e ], sl @ s)) ([], []) args in 
		let gv = List.map (fun s -> ("Const"^eng.sep, [String s ; Var s], config_persist)) gv in 

	(* finding syscall  *)
	(*****************************)
	(*****************************)
	(*****************************)
		match List.find_opt (fun (f', ty_args, (ch_vars, path_vars), meta_vars, substs, crule, ret) -> f = f') syscalls with
		| None -> error ~loc:Nowhere (UnintendedError "undefined syscall")
		| Some (f, ty_args, (ch_vars, path_vars), meta_vars, substs, crule, ret) -> 
			let f = mk_fact_name f in 
			let processed_args = List.map2 (fun a b -> (a, b)) (List.map snd ty_args) el in

			let rec translate_and_subst_expr processed_args {Location.data=e; Location.loc=loc}  = 
			   let translate_and_subst_expr' processed_args = function
					| Syntax.ExtConst s -> Apply (s, [])
					| Syntax.Const s -> error ~loc (UnintendedError "global constant in fact")
					| Syntax.Variable (v, i,j,k) -> 
						begin match List.find_opt (fun (a, b) -> a = v) processed_args with
						| Some (a, b) -> b
						| None -> if List.exists (fun s -> s = v) meta_vars then Var (v ^ eng.sep) else Var v end
					| Syntax.Boolean b -> error ~loc (UnintendedError "translating boolean")
					| Syntax.String s -> String s
					| Syntax.Integer z -> Integer z
					| Syntax.Float f -> error ~loc (UnintendedError "translating float")
					| Syntax.Apply (o, el) -> Apply (o, List.map (translate_and_subst_expr processed_args) el )
					| Syntax.Tuple el ->  List (List.map (translate_and_subst_expr processed_args) el)
					
					| Syntax.Channel (v, l) -> 
							begin match List.find_opt (fun (a, b) -> a = v) processed_args with
						| Some (a, b) -> b
						| None -> if List.exists (fun s -> s = v) meta_vars then Var (v ^ eng.sep) else Var v end

					| Syntax.Process v -> 
											begin match List.find_opt (fun (a, b) -> a = v) processed_args with
						| Some (a, b) -> b
						| None -> if List.exists (fun s -> s = v) meta_vars then Var (v ^ eng.sep) else Var v end

					| Syntax.Path v -> 
											begin match List.find_opt (fun (a, b) -> a = v) processed_args with
						| Some (a, b) -> b
						| None -> if List.exists (fun s -> s = v) meta_vars then Var (v ^ eng.sep) else Var v end

					
					| Syntax.FrVariable v -> error ~loc (UnintendedError "translating free var")
				  
				  in translate_and_subst_expr' processed_args e
			in

			let subst_facts =
			List.map (fun (y, e) ->
				("!Eq"^eng.sep, [Var y; translate_and_subst_expr processed_args e], config_linear)) substs in 

			let acp_facts = 
			List.map (fun v -> (f ^ eng.sep ^"Allowed", [String eng.namespace ; translate_and_subst_expr processed_args (Location.locate ~loc:Nowhere (Syntax.Variable (v, 0,0,0)))], config_persist)) ch_vars 
			@ List.map (fun v -> (f ^ eng.sep ^"Allowed", [String eng.namespace ; translate_and_subst_expr processed_args (Location.locate ~loc:Nowhere (Syntax.Variable (v, 0,0,0)))], config_persist)) path_vars
			@ begin match ch_vars @ path_vars with | [] -> [(f ^ eng.sep ^"Allowed", [String eng.namespace], config_persist)] | _ -> [] end
			in 

			let translate_fact f = 
				begin
				match f.Location.data with
				| Syntax.GlobalFact (s, el) -> (s, (List.map  (translate_and_subst_expr processed_args) el), config_linear)
				| Syntax.Fact (s, el) -> 
				(* reserved facts: *)
				let namespace_id = (String namespace) in

						(mk_fact_name s, namespace_id :: (List.map  (translate_and_subst_expr processed_args) el), config_linear_delayed)

				| Syntax.ChannelFact (scope, s, el) -> 
						(mk_fact_name s, (translate_and_subst_expr processed_args (Location.locate ~loc:Nowhere (Syntax.Variable (scope, 0,0,0)))) :: (List.map  (translate_and_subst_expr processed_args) el), config_linear_delayed)
				| Syntax.PathFact (scope, s, el) -> 
						(mk_fact_name s, String (eng_get_filesys eng) :: (translate_and_subst_expr processed_args (Location.locate ~loc:Nowhere (Syntax.Variable (scope, 0,0,0)))) :: (List.map  (translate_and_subst_expr processed_args) el), config_linear_delayed)
				| _ -> error ~loc:Nowhere (UnintendedError "unexpected fact in syscall")
			end
			in	

			let rec translate_crule eng init_state final_state  {Location.data=crule; Location.loc=loc}  =
				begin
				match crule with
				| Syntax.CRule (pre, post) -> 
					let rname = 
						match init_state with
						| None -> eng_state eng 
						| Some ((_, (String s) :: l, _)::l') -> s
					in 
					let eng_f = eng_inc_index eng in 
					(eng_f, [(rname, role,
									(match init_state with | None -> [(eng_get_frame_title eng, [String (eng_state eng) ; (List (eng_var_list_loc eng)) ; (List (eng_var_list_top eng))], config_linear) ] | Some x -> x) 
									@ (List.map translate_fact pre),
									[],
									(match final_state with | None -> [(eng_get_frame_title eng, [String (eng_state eng_f) ; (List (eng_var_list_loc eng_f)) ; (List (eng_var_list_top eng_f))], config_linear) ] | Some x -> x) 
									@ (List.map translate_fact post))])
				

				| Syntax.CRuleStmt (pre, stmts, post) -> 
				begin match stmts with
				| [{Location.data=Syntax.OpStmt {Location.data=Syntax.Call((y, _, _, _), f, args) ; Location.loc=_} ; Location.loc=_}] -> 
						let rname = 
						match init_state with
						| None -> eng_state eng 
						| Some ((_, (String s) :: l, _)::l') -> s
						in 
						let eng_int = eng_set_mode eng f in 
						let eng_f = eng_inc_index eng in 
						let rule_call = (rname, role,
									(match init_state with | None -> [(eng_get_frame_title eng, [String (eng_state eng) ; (List (eng_var_list_loc eng)) ; (List (eng_var_list_top eng))], config_linear) ] | Some x -> x) 
									@ (List.map translate_fact pre),
									[],
									[(eng_get_frame_title eng, [String (eng_state eng_int) ; (List (eng_var_list_loc eng)) ; (List (eng_var_list_top eng))], config_linear) ;
										("Run"^eng.sep, [String namespace; 
																		(translate_and_subst_expr processed_args (Location.locate ~loc:Nowhere (Syntax.Variable (f, 0,0,0)))); 
																		List (List.map  (translate_and_subst_expr processed_args) args);
																		List (eng_var_list_top eng)], config_linear)]) in 

						let rule_return = (rname^eng.sep, role, 
										[(eng_get_frame_title eng, [String (eng_state eng_int) ; (List (eng_var_list_loc eng)) ; (List (eng_var_list_top eng))], config_linear) ;
										("Return"^eng.sep, [String namespace; 
																		(translate_and_subst_expr processed_args (Location.locate ~loc:Nowhere (Syntax.Variable (f, 0,0,0)))); 
																		Var y;
																		Var ("top_frame" ^eng.sep)], config_linear)],
										[],
										(match final_state with | None -> [(eng_get_frame_title eng, [String (eng_state eng_f) ; (List (eng_var_list_loc eng_f)) ; (List (eng_var_list_top eng_f))], config_linear) ] | Some x -> x) 
										@ (List.map translate_fact post)) in 
						(eng_f, [rule_call; rule_return])



				| _ -> error ~loc:Nowhere NotSupportedYet
				end

				| Syntax.CRuleSeq (r1, r2) ->
					let (eng, r1) = translate_crule eng init_state None r1 in 
					let (eng, r2) = translate_crule eng (Some [(eng_get_frame_title eng, [String (eng_state eng) ; (List (eng_var_list_loc eng)) ; (List (eng_var_list_top eng))], config_linear) ]) final_state r2 in 
					(eng, r1 @ r2)

				| Syntax.CRulePar (r1, r2) ->
					let eng1 = eng_set_mode eng "p1" in 
					let eng2 = eng_set_mode eng "p2" in 
					let (eng1', r1) = translate_crule eng1 init_state final_state r1 in
					let (eng2', r2) = translate_crule eng2 init_state final_state r2 in
					(eng, r1 @ r2)

				| Syntax.CRuleRep r -> 
					let eng, r = translate_crule eng init_state init_state r in 
					(eng, r)
				end
				in 

			let init_state = (eng_get_frame_title eng, [String state_i ; (List (eng_var_list_loc eng)) ; (List (eng_var_list_top eng))], config_linear) :: acp_facts @ subst_facts in 
			let final_state = (eng_get_frame_title eng, 
				[String state_f ; 
					(List ( begin match ret with 
									| Some e -> translate_and_subst_expr processed_args e
									| None -> String (eng_get_fresh_string eng) end :: eng_var_list_loc eng)) ; 
					(List (eng_var_list_top eng))], config_linear) in 

			let (_, r) = translate_crule (eng_set_mode eng f) (Some init_state) (Some [final_state]) crule in 

			(eng_add_var eng_f v, List.fold_left (fun t r -> add_rule t r) t r)
		end
(*****************************)
(*****************************)
(*****************************)
(* end *)


	| Syntax.If (e1, e2, c1, c2) -> 
		let e1, gv1 = translate_expr2 e1 in  
		let gv1 = List.map (fun s -> ("Const"^eng.sep, [String s ; Var s], config_persist)) gv1 in 

		let e2, gv2 = translate_expr2 e2 in  
		let gv2 = List.map (fun s -> ("Const"^eng.sep, [String s ; Var s], config_persist)) gv2 in 

		let eng_then = eng_set_mode eng "then" in
		let eng_else = eng_set_mode eng "else" in
		
		let t = add_rule t (state_i ^eng.sep^"in" ^eng.sep^"then", role,
									[(eng_get_frame_title eng, [String state_i ; (List (eng_var_list_loc eng)) ; (List (eng_var_list_top eng))], config_linear)]  @ gv1 @ gv2, 
									
									[("Eq", [e1; e2], config_linear)], 

									[(eng_get_frame_title eng, [String (eng_state eng_then) ; (List (eng_var_list_loc eng)) ; (List (eng_var_list_top eng))], config_linear)]) in 
		
		let t = add_rule t (state_i ^eng.sep^"in" ^eng.sep^"else", role,
									[(eng_get_frame_title eng, [String state_i ; (List (eng_var_list_loc eng)) ; (List (eng_var_list_top eng))], config_linear)]  @ gv1 @ gv2, 
									[("Neq", [e1; e2], config_linear)], 
									[(eng_get_frame_title eng, [String (eng_state eng_else) ; (List (eng_var_list_loc eng)) ; (List (eng_var_list_top eng))], config_linear)]) in 

		let eng_then, t =  (List.fold_left (fun (eng, t) c -> translate_stmt eng t c syscalls ) (eng_then, t) c1) in 


		let t = add_rule t (state_i ^eng.sep^ "out"^eng.sep^ "then", role,
									[(eng_get_frame_title eng, [String (eng_state eng_then) ; (List (eng_var_list_loc eng_then)) ; (List (eng_var_list_top eng_then))], config_linear)], 
									[], 
									[(eng_get_frame_title eng, [String state_f ; (List (eng_var_list_loc eng_f)) ; (List (eng_var_list_top eng_f))], config_linear)]) in 

		let eng_else, t =  (List.fold_left (fun (eng, t) c -> translate_stmt eng t c syscalls ) (eng_else, t) c2) in 


		let t = add_rule t (state_i ^eng.sep^ "out"^eng.sep^ "else", role,
									[(eng_get_frame_title eng, [String (eng_state eng_else) ; (List (eng_var_list_loc eng_else)) ; (List (eng_var_list_top eng_else))], config_linear)], 
									[], 
									[(eng_get_frame_title eng, [String state_f ; (List (eng_var_list_top eng_f)) ; (List (eng_var_list_top eng_f))], config_linear)]) in 

		(eng_f,  t)
	| Syntax.For ((v, _, _, _), i, j, c) -> 
		let eng_ith i = eng_set_mode (eng_set_mode (eng_add_var (eng_add_frame eng) v) "for") (string_of_int i) in
(* 		let t = add_rule t (state_i ^eng.sep^"in" ^eng.sep^"for", 
									[("Frame", [String namespace; String state_i ; (List (eng_var_list eng))], false)], 
									
									[], 

									[("Frame", [String namespace; String (eng_state (eng_ith i)) ; (List (Integer i :: eng_var_list eng))], false)]) in 
 *)		
 			let eng_origin = eng in 
			let eng_for, t = List.fold_left (fun (eng, t) k -> 

				let t = add_rule t (eng_state (eng_ith k) ^eng.sep ^"start", role,
									[(eng_get_frame_title eng, [String (eng_state eng) ; (List (eng_var_list_loc eng)) ; (List (eng_var_list_top eng))], config_linear)], 
									[],
									[(eng_get_frame_title eng, [String (eng_state (eng_ith k)) ; (List (Integer k :: eng_var_list_loc (eng_origin))) ; (List (eng_var_list_top eng))], config_linear)]) in 

				let eng, t = (List.fold_left (fun (eng, t) c -> translate_stmt eng t c syscalls ) (eng_ith k, t) c)  

				in (eng, t)) (eng, t) (let rec range i j = if i < j then i :: range (i + 1) j else [] in range i j) in 

			let t = add_rule t (state_i, role,
									[(eng_get_frame_title eng, [String (eng_state eng_for) ; (List (eng_var_list_loc eng_for)) ; (List (eng_var_list_top eng_for))], config_linear)], 
									[], 
									[(eng_get_frame_title eng, [String state_f ; (List (eng_var_list_loc eng_f)) ; (List (eng_var_list_top eng_f))], config_linear)]) in 
			(eng_f, t)		




	(* | _ -> error ~loc UnintendedError *)
in translate_atomic_stmt' eng t c syscalls

(* let translate_syscall eng t (f, ty_args, (ch_vars, path_vars), meta_vars, crule, ret) = 
	let args = List.map snd ty_args in 
	let namespace_string = 
		(let rec f s = if List.exists (fun u -> u = s) (args @ meta_vars) then f (s ^ "_") else s in f "proc") in                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      

	let namespace_id = (Var namespace_string) in
	let eng = eng_set_namespace eng f in 
	let eng = eng_set_lctx eng [args] in 
	let eng = eng_add_var eng namespace_string in

	let acp_facts = 
	List.map (fun v -> (eng.namespace ^ eng.sep ^"Allowed", [namespace_id ; Var v], config_persist)) ch_vars 
	@ List.map (fun v -> (eng.namespace ^ eng.sep ^"Allowed", [namespace_id ; Var v], config_persist)) path_vars
	@ begin match ch_vars @ path_vars with | [] -> [(eng.namespace ^ eng.sep ^"Allowed", [namespace_id], config_persist)] | _ -> [] end
	in 

	let translate_fact f = 
	match f.Location.data with
	| Syntax.GlobalFact (s, el) -> (s, (List.map  (translate_expr ~ch:true) el), config_linear)
	| Syntax.Fact (s, el) -> 
	(* reserved facts: *)
	if s = "run" then
			match el with
			| f :: args ->
				("Run"^eng.sep, [namespace_id ; (translate_expr ~ch:true f) ; List (List.map (translate_expr ~ch:true) args)], config_linear_delayed)
			| _ ->				(mk_fact_name s, namespace_id :: (List.map  (translate_expr ~ch:true) el), config_linear_delayed)
	else if s = "returned" then
			match el with
			| f :: args ->
				("Return"^eng.sep, [namespace_id ; (translate_expr ~ch:true f) ; List (List.map (translate_expr ~ch:true) args)], config_linear_delayed)
			| _ ->				(mk_fact_name s, namespace_id :: (List.map  (translate_expr ~ch:true) el), config_linear_delayed)
		else
			(mk_fact_name s, namespace_id :: (List.map  (translate_expr ~ch:true) el), config_linear_delayed)

	| Syntax.ChannelFact (scope, s, el) -> 
			(mk_fact_name s, (Var scope) :: (List.map  (translate_expr ~ch:true) el), config_linear_delayed)
	| Syntax.PathFact (scope, s, el) -> 
			(mk_fact_name s, (Var scope) :: (List.map  (translate_expr ~ch:true) el), config_linear_delayed)
	| _ -> error ~loc:Nowhere (UnintendedError "unexpected fact in syscall")
	in

	let rec translate_crule eng init_state final_state  {Location.data=crule; Location.loc=loc}  =
		match crule with
		| Syntax.CRule (pre, post) -> 
			let eng_f = eng_inc_index eng in 
			(eng_f, [(eng_state eng, "",
							(match init_state with | None -> [(eng_state eng, eng_var_list eng, config_linear)] | Some x -> x) 
							@ (List.map translate_fact pre),
							[],
							(match final_state with | None -> [(eng_state eng_f, eng_var_list eng, config_linear)] | Some x -> x) 
							@ (List.map translate_fact post))])
		
		| Syntax.CRuleSeq (r1, r2) ->
			let (eng, r1) = translate_crule eng init_state None r1 in 
			let (eng, r2) = translate_crule eng (Some [(eng_state eng, eng_var_list eng, config_linear)]) final_state r2 in 
			(eng, r1 @ r2)

		| Syntax.CRulePar (r1, r2) ->
			let eng1 = eng_set_mode eng "p1" in 
			let eng2 = eng_set_mode eng "p2" in 
			let (eng1', r1) = translate_crule eng1 init_state final_state r1 in
			let (eng2', r2) = translate_crule eng2 init_state final_state r2 in
			(eng, r1 @ r2)

		| Syntax.CRuleRep r -> 
			let eng, r = translate_crule eng init_state init_state r in 
			(eng, r)
		in 

	let init_state = (eng_state eng, eng_var_list eng, config_linear_delayed) :: acp_facts in 
	let final_state = (eng_suffix eng eng.namespace "return", [namespace_id ;
				match ret with 
				| Some e -> translate_expr ~ch:true e
				| None -> String (eng_get_fresh_string eng)], config_linear_delayed) in 

	let (eng, r) = translate_crule eng (Some init_state) (Some [final_state]) crule in 

	List.fold_left (fun t r -> add_rule t r) t r 
 *)

let translate_attack eng t (f, (ch_vars, path_vars, process_vars), (pre, post)) = 
	
(* 	let namespace_string = 
		(let rec f s = if List.exists (fun u -> u = s) ([arg]) then f (s ^ "_") else s in f "proc") in                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      

	let namespace_id = (Var namespace_string) in
 *)	
 	let eng = eng_set_namespace eng f in 
	let eng = eng_set_lctx eng [ch_vars@ path_vars@ process_vars] in 
	(* let eng = eng_add_var eng namespace_string in *)
	
	let acp_facts = 
	List.map (fun v -> (eng.namespace ^ eng.sep ^"Allowed", [Var v], config_persist)) ch_vars 
	@ List.map (fun v -> (eng.namespace ^ eng.sep ^"Allowed", [Var v], config_persist)) path_vars  
	@ List.map (fun v -> (eng.namespace ^ eng.sep ^"Allowed", [Var v], config_persist)) process_vars in 

	let translate_fact f = 
	match f.Location.data with
	| Syntax.GlobalFact (s, el) -> (s, (List.map  (translate_expr ~ch:true) el), config_linear_delayed)
	| Syntax.Fact (s, el) -> (mk_fact_name s, (List.map  (translate_expr ~ch:true) el), config_linear_delayed)
	| Syntax.ChannelFact (scope, s, el) -> 
			(mk_fact_name s, (Var scope) :: (List.map  (translate_expr ~ch:true) el), config_linear_delayed)
	| Syntax.PathFact (scope, s, el) -> 
			(mk_fact_name s, (Var scope) :: (List.map  (translate_expr ~ch:true) el), config_linear_delayed)
	| Syntax.ProcessFact (scope, s, el) -> 
			(* reserved facts *)
(* 			if s = "Frame" then
				(mk_fact_name s, (Var scope) :: (List.map  (translate_expr ~ch:true) el), false)
			else
 *)				(mk_fact_name s, (Var scope) :: (List.map  (translate_expr ~ch:true) el), config_linear_delayed)
(* 		match ty with 
		| TyChannel ->
		| TyPath -> 	
 *)(* 		| TyProcess -> 	
			(mk_fact_name s, (Var scope) :: (List.map  (translate_expr ~ch:true) el), false)
 *)		| _ -> error ~loc:Nowhere (UnintendedError "unexpected fact in attack")
	in

	add_rule t (mk_fact_name f, "", acp_facts @ (List.map translate_fact pre), [],  (List.map translate_fact post))



let translate_process eng t {
  Context.proc_pid=k;
  Context.proc_name=s;
  Context.proc_attack=attks;
  Context.proc_channel=chs;
  Context.proc_file=fls;
  Context.proc_filesys=fsys;
  Context.proc_variable=vars;
  Context.proc_function=fns;
  Context.proc_main=m
} syscalls =
	let namespace = String.capitalize_ascii (s ^ (if k = 0 then "" else string_of_int k)) in (* this must be unique *)
	let eng = eng_set_namespace eng namespace in 
	let eng = eng_set_role eng namespace in

	let eng = eng_set_scope eng "init" in 

	let eng = eng_set_filesys eng fsys in
	let t = add_comment t ("- Process name: " ^ namespace) in 
	let t = add_comment t ("-- initialization rules") in 
	let t = add_rule t (eng_state eng, namespace, [], [(namespace^eng.sep^"init", [], config_linear)], 
				(eng_get_frame_title eng, [String (eng_state eng) ; List []; List []], config_linear)
				:: 
				
				(List.map (fun attk -> (mk_fact_name attk ^ eng.sep ^"Allowed", [String namespace], config_persist)) attks)
				

			) in

	(* initialize memory *)
	let (eng, t) = List.fold_left
		(fun (eng, t) (x, e) -> 
		let state_i = eng_state eng in
		let eng_f = eng_inc_index eng in 
		let eng_f = eng_add_var eng_f x in 
		let state_f = eng_state eng_f in

		let e, gv = translate_expr2 e in  
		let gv = List.map (fun s -> ("Const"^eng.sep, [String s ; Var s], config_persist)) gv in 
		let t = add_rule t (state_f, namespace,
									[(eng_get_frame_title eng, [String state_i;  List [] ; List (eng_var_list_top eng)], config_linear)] @ gv, 
									[], 
									[(eng_get_frame_title eng, [String state_f ; List []; List (e :: eng_var_list_top eng)], config_linear)]) in
		(eng_f, t)) (eng, t) vars in 

	let translate_function eng (t : tamarin) (f, args, stmts, (v, vi, vj, vk)) = 
		let t = add_comment t ("-- member function "^f) in 

		let eng = eng_set_scope eng f in
		let eng = eng_set_role eng (namespace ^ eng.sep ^ f) in  
		let eng_start = eng_add_frame (eng_pop_frame (eng_set_mode eng "run")) in
		let eng_start = List.fold_left (fun eng v -> eng_add_var eng v) eng args in 
		let eng_start = eng_set_mode eng_start "run" in 
		let eng = eng_add_frame eng in 
		let eng = eng_set_func eng f in 

		let t = add_rule t (eng_state eng_start, eng_get_role eng,
													[("Run"^eng.sep, [String namespace; String f; List (List.map (fun s -> Var s) args); Var ("top_frame"^eng.sep)], config_linear_delayed)], 
													[],
													[(eng_get_frame_title eng, [String (eng_state eng); List (List.map (fun s -> Var s) (List.rev args)) ; Var ("top_frame"^eng.sep)], config_linear)]) in

		let eng = List.fold_left (fun eng v -> eng_add_var eng v) eng args in 
		(* let t = add_rule t (eng.namespace^f, [(eng.namespace^f, eng_var_list eng)], [], [(eng_state eng, eng_var_list eng)]) in *)
		let eng, t = List.fold_left (fun (eng, t) stmt -> translate_stmt eng t stmt syscalls ) (eng, t) stmts in
		let eng_return = eng_set_mode (eng_set_scope eng f) "return" in 

		let t = add_rule t (eng_state eng_return, eng_get_role eng,
			[(eng_get_frame_title eng, [String (eng_state eng); List (eng_var_list_loc eng) ; List (eng_var_list_top eng)], config_linear)],
			[], 
			[("Return"^eng.sep, [String namespace ; String f; Var v; List (eng_var_list_top eng)], config_linear)])
		in t in  





	let t = List.fold_left (fun t f -> translate_function eng t f) t fns in

	let t = add_comment t ("-- main function ") in 	
	let eng_main = eng_set_scope eng "main" in 
	let t = add_rule t (eng_state (eng_set_mode eng_main "start"), namespace, [(eng_get_frame_title eng, [String (eng_state eng); List (eng_var_list_loc eng) ; (List (eng_var_list_top eng))], config_linear)], [], 
																					[(eng_get_frame_title eng, [String (eng_state eng_main); List (eng_var_list_loc eng_main) ; (List (eng_var_list_top eng))], config_linear)]) in 

	let eng = eng_add_frame eng_main in 
	let eng, t = List.fold_left (fun (eng, t) stmt -> translate_stmt eng t stmt syscalls ) (eng, t) m in
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

	(* let t = add_comment t "external system calls:" in
	let t = List.fold_left (fun t r -> translate_syscall eng t r) t (List.rev def.Context.def_ext_syscall) in
 *)
	let t = add_comment t "External attacks:" in
	let t = List.fold_left (fun t r -> translate_attack eng t r) t (List.rev def.Context.def_ext_attack) in

	(* load global variables *)
	let t = add_comment t "Global constants:" in
	let t = List.fold_left (fun t (v, e) -> 
		match e with
		| None -> (* when v is fresh *) add_rule t ("Const"^eng.sep^v, "", [("Fr", [Var v], config_linear)], [], [("Const"^eng.sep, [String v ; Var v], config_persist)])
		| Some e -> (* when v is defined *) 
			let e, gv = translate_expr2 e in  
			let gv = List.map (fun s -> ("Const"^eng.sep, [String s ; Var s], config_persist)) gv in 
			add_rule t ("Const"^eng.sep^v, "", gv, [], [("Const"^eng.sep, [String v ; e], config_persist)])) t (List.rev def.Context.def_const) in

(* initialize files *)
	   (* def_fsys    :  (Name.ident * Name.ident * Syntax.expr) list ; *)
	let t = add_comment t "Initial file system:" in
	let t, il = List.fold_left (fun (t, il) (fsys, path, e) ->
		(* let path = (mk_dir eng fsys path) in *)
		let e, gv = translate_expr2 e in  
		let gv = List.map (fun s -> ("Const"^eng.sep, [String s ; Var s], config_persist)) gv in 
		let name = mk_fact_name  fsys^ replace_string '/' eng.sep path ^ eng.sep ^"init" in 
		add_rule t (name, "",
									gv,
									[(name, [], config_linear)],
									[("File", [String fsys; List [String fsys; String path] ; e], config_linear)]), name::il) (t, []) def.Context.def_fsys in 

let t = add_comment t "Access control:" in
(* access control *)
	   (* pol_access : (Name.ident * Name.ident list * Name.ident) list ; *)
	let t, il = List.fold_left (fun (t, il) p ->
		let procname = String.capitalize_ascii (p.Context.proc_name ^ (if p.Context.proc_pid = 0 then "" else string_of_int p.Context.proc_pid)) in 
		let t, il = List.fold_left (fun (t, il) (c, ty) -> 
			match List.find_all (fun (a, b, sys) -> a = p.Context.proc_type && List.exists (fun b -> b = ty) b) pol.Context.pol_access with
			| [] -> (t, il) 
			| scall -> 
					List.fold_left (fun (t, il) (_, _, sys) ->
					 let name = procname ^ eng.sep ^ c^eng.sep ^ sys in 
						add_rule t 
							(name, "",
								[], 
								[(name, [], config_linear)], 
								[(mk_fact_name sys ^eng.sep ^"Allowed", [String procname; String c], config_persist)])
								, name::il) (t, il) scall) 
		(t, il) ctx.Context.ctx_ch in 

		let t, il = 
			match List.find_all (fun (a, b, sys) -> a = p.Context.proc_type && (match b with | [] -> true | _ -> false)) pol.Context.pol_access with
			| [] -> (t, il) 
			| scall -> 
					List.fold_left (fun (t, il) (_, _, sys) ->
					 let name = procname ^ eng.sep ^ sys in 
						add_rule t 
							(name, "",
								[], 
								[(name, [], config_linear)], 
								[(mk_fact_name sys ^eng.sep ^"Allowed", [String procname], config_persist)])
								, name::il) (t, il) scall 

		in 

		let t, il = List.fold_left (fun (t, il) (dir, path, ty) -> 
			if p.Context.proc_filesys <> dir then (t, il) else
			match List.find_all (fun (a, b, sys) -> a = p.Context.proc_type && List.exists (fun b -> b = ty) b) pol.Context.pol_access with
			| [] -> (t, il)
			| scall ->				
					List.fold_left (fun (t, il) (_, _, sys) ->
					let name = procname ^ eng.sep ^ dir ^ eng.sep ^replace_string '/' eng.sep path^eng.sep^ sys in 
						add_rule t 
						(name, "",
							[], 
							[(name, [], config_linear)], 
							[(mk_fact_name sys ^eng.sep ^"Allowed", [String procname; List [String dir ; String path]], config_persist)])
				, name::il) (t, il) scall
		) (t, il) ctx.Context.ctx_fsys in 
		(t, il)) (t, il) proc in
		

(* initialize attacks on channels!!! *)
let t = add_comment t "Attacker policy:" in

	let t, il = List.fold_left (fun (t, il) (c, ty) -> 
		match Context.pol_get_attack_opt pol ty with 
		| Some attk -> add_rule t (mk_fact_name c ^ eng.sep ^ attk, "",
			[], 
			[(mk_fact_name c ^ eng.sep ^ attk ^ eng.sep ^ "init", [], config_linear)], 
			[(mk_fact_name attk ^ eng.sep ^"Allowed", [String c], config_linear)]
		), (mk_fact_name c ^ eng.sep ^ attk ^ eng.sep ^ "init"):: il
		| None -> t, il) (t, il) ctx.Context.ctx_ch in 
	


	let t = add_comment t "Processes:" in
	let t = List.fold_left (fun t p -> translate_process eng t p (List.rev def.Context.def_ext_syscall)) t (List.rev proc) in


	let init_list = List.map (fun p -> String.capitalize_ascii (p.Context.proc_name ^ 
		(if p.Context.proc_pid = 0 then "" else string_of_int p.Context.proc_pid )
	) ^ eng.sep^"init") proc in 

	let init_list = init_list @ il in 

	(t, init_list, lem), {prt_sep=eng.sep;}


