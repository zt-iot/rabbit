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
  | Integer of int
  | List of expr list

type equations = (expr * expr) list
type signature = functions * equations 

let empty_signature = ([], [])

type fact = string * expr list * bool 
(* true is persistent fact *)
type rule = 
	| Rule of string * fact list * fact list * fact list
	| Comment of string

type tamarin = signature * rule list

let add_rule t (a, b, c, d) = (fst t, (Rule (a, b, c, d)) :: ( (snd t)))
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
	| String s -> "\'"^(replace_string '/' prt.prt_sep s)^"\'"
	| Integer i -> string_of_int i
	| List el -> 
		match el with
		| [] -> "\'rabbit"^prt.prt_sep^"\'"
		| [e] -> print_expr prt e 
		| _ -> 	"<" ^ (mult_list_with_concat (List.map (print_expr prt) el) ", ") ^ ">"

let print_signature prt (fns, eqns) = 
	let print_functions fns = 
	"functions: "^(mult_list_with_concat (List.map (fun (f, ar) -> f ^"/"^(string_of_int ar)) fns) ", ") ^"\n" in 
	let print_equations eqns = 
	"equations: "^(mult_list_with_concat (List.map (fun (e1, e2) -> (print_expr prt e1)^"="^(print_expr prt e2)) eqns) ", ") ^"\n" in 
	(print_functions fns) ^ (print_equations eqns)

let print_rule2 prt (f, pre, label, post) = 
	let print_fact (f, el, b) = 
	(if b then "!" else "") ^f^"(" ^ (mult_list_with_concat (List.map (print_expr prt) el) ", ") ^ ")" in 
	"rule "^f ^" : "^ 
	"["^(mult_list_with_concat (List.map print_fact pre) ", ") ^ "]" ^
	(match label with 
		| [] -> "-->" 
		| _ -> 	"--[" ^ (mult_list_with_concat (List.map print_fact label) ", ") ^ "]->")^

	"["^(mult_list_with_concat (List.map print_fact post) ", ") ^ "] \n"	

let print_comment s = "\n// "^s^"\n\n" 

let print_rule prt r = match r with | Rule (a, b, c, d) -> print_rule2 prt (a, b, c, d) | Comment s ->print_comment s 

let print_tamarin prt ((sign, rules), init_list, lem) = 
	"theory rabbit\n\nbegin\n"^
	print_signature prt sign ^
	(mult_list_with_concat (List.map (print_rule prt) (List.rev rules)) "")^
	
	List.fold_left (fun l s -> l^"\nrestriction "^s^" : \" All #i #j . "^s^"() @ #i & "^s^"() @ #j ==> #i = #j \"") "" init_list ^ "\n" ^

	(* if then else restriction *)

	(* "\nrestriction OnlyOnce : \" All x #i #j . OnlyOnce(x) @ #i & OnlyOnce(x) @ #j ==> #i = #j \"\n" ^ *)

	"restriction Equality: \" All x y #i. Eq(x,y) @ #i ==> x = y\"\n" ^

	"restriction Inequality: \"All x #i. Neq(x,x) @ #i ==> F\"\n" ^

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
}

let empty_engine = {namespace = ""; scope = ""; index = 0; lctx = [[]]; sep = ""; mode = []; fresh_ident = ""; fresh_string = ""; filesys = ""}

let eng_set_fresh_string eng s = {eng with fresh_string=s}
let eng_set_fresh_ident eng s = {eng with fresh_ident=s}

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

let eng_state eng =
	eng.namespace ^ 
	(if eng.scope = "" then "" else eng.sep ^ eng.scope) ^ 
	(if eng.index = 0 then "" else eng.sep ^ string_of_int (eng.index - 1)) ^ 
	if List.length eng.mode = 0 then "" else eng.sep ^mult_list_with_concat (List.rev eng.mode) eng.sep

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
	| Syntax.Process v -> Var v
	| Syntax.Path v -> Var v
	| Syntax.FrVariable v -> error ~loc UnintendedError
  in translate_expr' e

let rec translate_expr2 ?(ch=false) {Location.data=e; Location.loc=loc} = 
   let translate_expr2' = function
	| Syntax.ExtConst s -> Apply (s, []), []
	| Syntax.Const s -> Var s, [s]
	| Syntax.Variable (v, i,j,k) -> Var v, []
	| Syntax.Boolean b -> error ~loc UnintendedError
	| Syntax.String s -> String s, []
	| Syntax.Integer z -> Integer z, []
	| Syntax.Float f -> error ~loc UnintendedError
	| Syntax.Apply (o, el) -> 
		let (el, sl) = List.fold_left (fun (el, sl) e -> 
			let e, s = translate_expr2 ~ch:ch e in 
				(el @ [e], sl @ s)) ([], []) el in 
		Apply (o, el), sl
	| Syntax.Tuple el -> error ~loc UnintendedError
	| Syntax.Channel (c, l) -> if ch then Var c, [] else String c, []
	| Syntax.Process v -> Var v, []
	| Syntax.Path v -> Var v, []
	| Syntax.FrVariable v -> error ~loc UnintendedError
  in translate_expr2' e


let rec translate_stmt eng (t : tamarin)  {Location.data=c; Location.loc=loc} = 
  match c with
  | Syntax.OpStmt a -> translate_atomic_stmt eng t a
  | Syntax.EventStmt (a, el) -> 
  	let eng, (sign, rules) = translate_atomic_stmt eng t a in 
  	match rules with
  	| Rule (n, pre, label, post) :: rules -> 
  		(eng, (sign, Rule (n, pre, 
  			List.map (fun ev -> match ev.Location.data with Syntax.Event(id, el) -> (mk_fact_name id, List.map translate_expr el, false)) el 
  		, post) :: rules))
  	| [] -> error ~loc UnintendedError 
  	
and translate_atomic_stmt (eng : engine) (t: tamarin)  {Location.data=c; Location.loc=loc} =
  let translate_atomic_stmt' (eng : engine) (t : tamarin) c = 
  	let namespace =  eng.namespace in 
	  let state_i = eng_state eng in
	  let eng_f = eng_inc_index eng in
	  let state_f = eng_state eng_f in
	match c with
 	| Syntax.Skip -> 
		(eng_f, 
			add_rule t (state_i, 
									[("Frame", [String namespace; String state_i ; (List (eng_var_list eng))], false)], 
									[], 
									[("Frame", [String namespace; String state_f ; (List (eng_var_list eng))], false)]
			)
		)
	| Syntax.Let ((v, vi,vj,vk), e) -> 
		let e, gv = translate_expr2 e in  
		let gv = List.map (fun s -> ("Cosnt"^eng.sep, [String s ; Var s], true)) gv in 
		(eng_add_var eng_f v,
			add_rule t (state_i, 
									[("Frame", [String namespace; String state_i ; (List (eng_var_list eng))], false)]  @ gv , 
									[], 
									[("Frame", [String namespace; String state_f ; (List (e:: eng_var_list eng))], false)]
			))
	
	| Syntax.Call ((v, vi,vj,vk), f, args) -> 
		let (el, gv) = List.fold_left (fun (el, sl) e -> 
			let e, s = translate_expr2 e in 
				(el @ [e], sl @ s)) ([], []) args in 
		let gv = List.map (fun s -> ("Cosnt"^eng.sep, [String s ; Var s], true)) gv in 


		let eng_f = eng_add_var eng_f v in 
		let t = add_rule t (eng_state (eng_set_mode eng "in"), 
											[("Frame", [String namespace; String state_i ; (List (eng_var_list eng))], false)]  @ gv, 
											[], 
											[
												(eng_state (eng_set_mode eng "wait"), eng_var_list eng, false) ; 
										 		("Frame", [String namespace; String (eng_state (eng_set_scope eng f)) ; (List (el @ eng_lctx_back eng))], false)
											(* maybe need to be reversed. check! *)
											]) in 
		let t = add_rule t (eng_state (eng_set_mode eng "out"), 
			[(eng_state (eng_set_mode eng "wait"), eng_var_list eng, false) ; 
			(eng_state (eng_set_mode (eng_set_scope eng f) "return"), [(match v with |"" -> Var (eng_get_fresh_ident eng) |_->Var v)], false)], [], 
			[("Frame", [String namespace; String state_f ; (List (eng_var_list eng_f))], false)]) in
		(eng_f, t)

	| Syntax.Syscall ((v, vi,vj,vk), f, args) -> 

		let (el, gv) = List.fold_left (fun (el, sl) (e, ty) -> 
			let e, s = translate_expr2 e in 
				(el @ [ match ty with |Input.TyPath -> List [String (eng_get_filesys eng) ; e]|_ ->  e ], sl @ s)) ([], []) args in 
		let gv = List.map (fun s -> ("Cosnt"^eng.sep, [String s ; Var s], true)) gv in 


		let eng_f = eng_add_var eng_f v in 
		let t = add_rule t (eng_state (eng_set_mode eng "in"), 
										[("Frame", [String namespace; String state_i ; (List (eng_var_list eng))], false)]  @ gv, 
										[], 
										[(eng_state (eng_set_mode eng "wait"), eng_var_list eng, false) ; 
										(mk_fact_name f, (String eng.namespace) :: el, false)]) in


		let t = add_rule t (eng_state (eng_set_mode eng "out"), 
			[(eng_state (eng_set_mode eng "wait"), eng_var_list eng, false) ; 
			(eng_state (eng_set_mode (eng_set_namespace eng f) "return"), [(String eng.namespace) ; (match v with |"" -> Var (eng_get_fresh_ident eng) |_->Var v) ], false)], [], 
			[("Frame", [String namespace; String state_f ; (List (eng_var_list eng_f))], false)]) in
		(eng_f, t)

	| Syntax.If (e1, e2, c1, c2) -> 
		let e1, gv1 = translate_expr2 e1 in  
		let gv1 = List.map (fun s -> ("Cosnt"^eng.sep, [String s ; Var s], true)) gv1 in 

		let e2, gv2 = translate_expr2 e2 in  
		let gv2 = List.map (fun s -> ("Cosnt"^eng.sep, [String s ; Var s], true)) gv2 in 

		let eng_then = eng_set_mode eng "then" in
		let eng_else = eng_set_mode eng "else" in
		
		let t = add_rule t (state_i ^eng.sep^"in" ^eng.sep^"then", 
									[("Frame", [String namespace; String state_i ; (List (eng_var_list eng))], false)]  @ gv1 @ gv2, 
									
									[("Eq", [e1; e2], false)], 

									[("Frame", [String namespace; String (eng_state eng_then) ; (List (eng_var_list eng))], false)]) in 
		
		let t = add_rule t (state_i ^eng.sep^"in" ^eng.sep^"else", 
									[("Frame", [String namespace; String state_i ; (List (eng_var_list eng))], false)]  @ gv1 @ gv2, 
									[("Neq", [e1; e2], false)], 
									[("Frame", [String namespace; String (eng_state eng_else) ; (List (eng_var_list eng))], false)]) in 

		let eng_then, t =  (List.fold_left (fun (eng, t) c -> translate_stmt eng t c) (eng_then, t) c1) in 


		let t = add_rule t (state_i ^eng.sep^ "out"^eng.sep^ "then", 
									[("Frame", [String namespace; String (eng_state eng_then) ; (List (eng_var_list eng_then))], false)], 
									[], 
									[("Frame", [String namespace; String state_f ; (List (eng_var_list eng_f))], false)]) in 

		let eng_else, t =  (List.fold_left (fun (eng, t) c -> translate_stmt eng t c) (eng_else, t) c2) in 


		let t = add_rule t (state_i ^eng.sep^ "out"^eng.sep^ "else", 
									[("Frame", [String namespace; String (eng_state eng_else) ; (List (eng_var_list eng_else))], false)], 
									[], 
									[("Frame", [String namespace; String state_f ; (List (eng_var_list eng_f))], false)]) in 

		(eng_f,  t)
	| Syntax.For ((v, _, _, _), i, j, c) -> 
		let eng_ith i = eng_set_mode (eng_set_mode (eng_add_var (eng_add_frame eng) v) "for") (string_of_int i) in
(* 		let t = add_rule t (state_i ^eng.sep^"in" ^eng.sep^"for", 
									[("Frame", [String namespace; String state_i ; (List (eng_var_list eng))], false)], 
									
									[], 

									[("Frame", [String namespace; String (eng_state (eng_ith i)) ; (List (Integer i :: eng_var_list eng))], false)]) in 
 *)
			let eng_for, t = List.fold_left (fun (eng, t) k -> 

				let t = add_rule t (eng_state (eng_ith k) ^eng.sep ^"start", 
									[("Frame", [String namespace; String (eng_state eng) ; (List (eng_var_list eng))], false)], 
									[],
									[("Frame", [String namespace; String (eng_state (eng_ith k)) ; (List (Integer k :: eng_var_list eng))], false)]) in 

				let eng, t = (List.fold_left (fun (eng, t) c -> translate_stmt eng t c) (eng_ith k, t) c)  

				in (eng, t)) (eng, t) (let rec range i j = if i < j then i :: range (i + 1) j else [] in range i j) in 

			let t = add_rule t (state_i, 
									[("Frame", [String namespace; String (eng_state eng_for) ; (List (eng_var_list eng_for))], false)], 
									[], 
									[("Frame", [String namespace; String state_f ; (List (eng_var_list eng_f))], false)]) in 
			(eng_f, t)		




	| _ -> error ~loc UnintendedError
in translate_atomic_stmt' eng t c 

let translate_syscall eng t (f, ty_args, (ch_vars, path_vars), meta_vars, rules, ret) = 
	let args = List.map snd ty_args in 
	let namespace_string = 
		(let rec f s = if List.exists (fun u -> u = s) (args @ meta_vars) then f (s ^ "_") else s in f "proc") in                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      

	let namespace_id = (Var namespace_string) in
	let eng = eng_set_namespace eng f in 
	let eng = eng_set_lctx eng [args] in 
	let eng = eng_add_var eng namespace_string in

	let acp_facts = 
	List.map (fun v -> (eng.namespace ^ eng.sep ^"Allowed", [namespace_id ; Var v], true)) ch_vars 
	@ List.map (fun v -> (eng.namespace ^ eng.sep ^"Allowed", [namespace_id ; Var v], true)) path_vars in 

	let translate_fact f = 
	match f.Location.data with
	| Syntax.GlobalFact (s, el) -> (s, (List.map  (translate_expr ~ch:true) el), false )
	| Syntax.Fact (s, el) -> (mk_fact_name s, namespace_id :: (List.map  (translate_expr ~ch:true) el), false)
	| Syntax.ChannelFact (scope, s, el) -> 
			(mk_fact_name s, (Var scope) :: (List.map  (translate_expr ~ch:true) el), false)
	| Syntax.PathFact (scope, s, el) -> 
			(mk_fact_name s, (Var scope) :: (List.map  (translate_expr ~ch:true) el), false)
	| _ -> error ~loc:Nowhere UnintendedError
	in
	let (_, _, t) = List.fold_left (fun (eng, i, t) (pre, post) -> 
		if i = List.length rules - 1 then
		(eng, i+1, add_rule t (eng_state eng, 
			(eng_state eng, eng_var_list eng, false) :: (List.map translate_fact pre)
				@ (if i=0 then acp_facts else [])
			, 
			[], 
			(eng_suffix eng eng.namespace "return", [namespace_id ;
				match ret with 
				| Some e -> translate_expr ~ch:true e
				| None -> String (eng_get_fresh_string eng)], false) :: (List.map translate_fact post)))
		else 
		(eng_inc_index eng, i+1, add_rule t (eng_state eng, 
			(eng_state eng, eng_var_list eng, false) :: (List.map translate_fact pre)
			@ (if i=0 then acp_facts else [])
			, [], 
			(eng_state (eng_inc_index eng), eng_var_list eng, false) :: (List.map translate_fact post)))) (eng, 0, t) (List.rev rules)
	in t 

let translate_attack eng t (f, (ch_vars, path_vars, process_vars), (pre, post)) = 
	
(* 	let namespace_string = 
		(let rec f s = if List.exists (fun u -> u = s) ([arg]) then f (s ^ "_") else s in f "proc") in                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      

	let namespace_id = (Var namespace_string) in
 *)	
 	let eng = eng_set_namespace eng f in 
	let eng = eng_set_lctx eng [ch_vars@ path_vars@ process_vars] in 
	(* let eng = eng_add_var eng namespace_string in *)
	
	let acp_facts = 
	List.map (fun v -> (eng.namespace ^ eng.sep ^"Allowed", [Var v], true)) ch_vars 
	@ List.map (fun v -> (eng.namespace ^ eng.sep ^"Allowed", [Var v], true)) path_vars  
	@ List.map (fun v -> (eng.namespace ^ eng.sep ^"Allowed", [Var v], true)) process_vars in 

	let translate_fact f = 
	match f.Location.data with
	| Syntax.GlobalFact (s, el) -> (s, (List.map  (translate_expr ~ch:true) el), false)
	| Syntax.Fact (s, el) -> (mk_fact_name s, (List.map  (translate_expr ~ch:true) el), false)
	| Syntax.ChannelFact (scope, s, el) -> 
			(mk_fact_name s, (Var scope) :: (List.map  (translate_expr ~ch:true) el), false)
	| Syntax.PathFact (scope, s, el) -> 
			(mk_fact_name s, (Var scope) :: (List.map  (translate_expr ~ch:true) el), false)
	| Syntax.ProcessFact (scope, s, el) -> 
			(* reserved facts *)
(* 			if s = "Frame" then
				(mk_fact_name s, (Var scope) :: (List.map  (translate_expr ~ch:true) el), false)
			else
 *)				(mk_fact_name s, (Var scope) :: (List.map  (translate_expr ~ch:true) el), false)
(* 		match ty with 
		| TyChannel ->
		| TyPath -> 	
 *)(* 		| TyProcess -> 	
			(mk_fact_name s, (Var scope) :: (List.map  (translate_expr ~ch:true) el), false)
 *)		| _ -> error ~loc:Nowhere UnintendedError
	in

	add_rule t (mk_fact_name f, acp_facts @ (List.map translate_fact pre), [],  (List.map translate_fact post))



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
} =
	let namespace = String.capitalize_ascii (s ^ (string_of_int k)) in (* this must be unique *)
	let eng = eng_set_namespace eng namespace in 

	let eng = eng_set_scope eng "init" in 

	let eng = eng_set_filesys eng fsys in

	let t = add_rule t (eng_state eng, [], [(namespace^eng.sep^"init", [], false)], 
				("Frame", [String namespace; String (eng_state eng) ; List []], false)
				:: 
				
				(List.map (fun attk -> (mk_fact_name attk ^ eng.sep ^"Allowed", [String namespace], true)) attks)
				

			) in

	(* initialize memory *)
	let (eng, t) = List.fold_left
		(fun (eng, t) (x, e) -> 
		let state_i = eng_state eng in
		let eng_f = eng_inc_index eng in 
		let eng_f = eng_add_var eng_f x in 
		let state_f = eng_state eng_f in

		let e, gv = translate_expr2 e in  
		let gv = List.map (fun s -> ("Cosnt"^eng.sep, [String s ; Var s], true)) gv in 
		let t = add_rule t (state_f, 
									[("Frame", [String namespace; String state_i; List (eng_var_list eng)], false)] @ gv, 
									[], 
									[("Frame", [String namespace; String state_f ; List (e :: eng_var_list eng)], false)]) in
		(eng_f, t)) (eng, t) vars in 

	let translate_function eng (t : tamarin) (f, args, stmts, (v, vi, vj, vk)) = 
		let eng = eng_set_scope eng f in 
		let eng = eng_add_frame eng in 
		let eng = List.fold_left (fun eng v -> eng_add_var eng v) eng args in 
		(* let t = add_rule t (eng.namespace^f, [(eng.namespace^f, eng_var_list eng)], [], [(eng_state eng, eng_var_list eng)]) in *)
		let eng, t = List.fold_left (fun (eng, t) stmt -> translate_stmt eng t stmt) (eng, t) stmts in
		let eng_return = eng_set_mode (eng_set_scope eng f) "return" in 

		let t = add_rule t (eng_state eng_return, [("Frame", [String namespace; String (eng_state eng); List (eng_var_list eng)], false)], [], 
																							[(eng_state eng_return, [Var v], false)]) in 
		t in 

	let t = List.fold_left (fun t f -> translate_function eng t f) t fns in

	let eng_main = eng_set_scope eng "main" in 
	let t = add_rule t (eng_state (eng_set_mode eng_main "start"), [("Frame", [String namespace; String (eng_state eng); List (eng_var_list eng)], false)], [], 
																					[("Frame", [String namespace; String (eng_state eng_main); List (eng_var_list eng_main)], false)]) in 

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
	let t = add_comment t "external functions:" in
	let t = List.fold_left (fun t (f, k) -> add_fun t (f, k)) t (List.rev ctx.Context.ctx_ext_func) in
	
	let t = add_comment t "external constants:" in
	let t = List.fold_left (fun t c -> add_const t c) t (List.rev ctx.Context.ctx_ext_const) in
	
	let t = add_comment t "external equations:" in
	let t = List.fold_left (fun t (_, e1, e2) -> add_eqn t (translate_expr e1, translate_expr e2)) t (List.rev def.Context.def_ext_eq) in

	let t = add_comment t "external system calls:" in
	let t = List.fold_left (fun t r -> translate_syscall eng t r) t (List.rev def.Context.def_ext_syscall) in

	let t = add_comment t "external attacks:" in
	let t = List.fold_left (fun t r -> translate_attack eng t r) t (List.rev def.Context.def_ext_attack) in

	(* load global variables *)
	let t = add_comment t "global constants:" in
	let t = List.fold_left (fun t (v, e) -> 
		match e with
		| None -> (* when v is fresh *) add_rule t ("Const"^eng.sep^v, [("Fr", [Var v], false)], [], [("Const"^eng.sep, [String v ; Var v], true)])
		| Some e -> (* when v is defined *) 
			let e, gv = translate_expr2 e in  
			let gv = List.map (fun s -> ("Cosnt"^eng.sep, [String s ; Var s], true)) gv in 
			add_rule t ("Const"^eng.sep^v, gv, [], [("Const"^eng.sep, [String v ; e], true)])) t (List.rev def.Context.def_const) in

(* initialize files *)
	   (* def_fsys    :  (Name.ident * Name.ident * Syntax.expr) list ; *)
	let t = add_comment t "initial file system:" in
	let t, il = List.fold_left (fun (t, il) (fsys, path, e) ->
		(* let path = (mk_dir eng fsys path) in *)
		let name = mk_fact_name  fsys^ replace_string '/' eng.sep path ^ eng.sep ^"init" in 
		add_rule t (name, 
									[],
									[(name, [], false)],
									[("File", [List [String fsys; String path] ; translate_expr e], false)]), name::il) (t, []) def.Context.def_fsys in 

let t = add_comment t "access control:" in
(* access control *)
	   (* pol_access : (Name.ident * Name.ident list * Name.ident) list ; *)
	let t, il = List.fold_left (fun (t, il) p ->
		let procname = String.capitalize_ascii (p.Context.proc_name ^ (string_of_int p.Context.proc_pid)) in 
		let t, il = List.fold_left (fun (t, il) (c, ty) -> 
			match List.find_all (fun (a, b, sys) -> a = p.Context.proc_type && List.exists (fun b -> b = ty) b) pol.Context.pol_access with
			| [] -> (t, il) 
			| scall -> 
					List.fold_left (fun (t, il) (_, _, sys) ->
					 let name = procname ^ eng.sep ^ c^eng.sep ^ sys in 
						add_rule t 
							(name, 
								[], 
								[(name, [], false)], 
								[(mk_fact_name sys ^eng.sep ^"Allowed", [String procname; String c], true)])
								, name::il) (t, il) scall) 
		(t, il) ctx.Context.ctx_ch in 

		let t, il = List.fold_left (fun (t, il) (dir, path, ty) -> 
			match List.find_all (fun (a, b, sys) -> a = p.Context.proc_type && List.exists (fun b -> b = ty) b) pol.Context.pol_access with
			| [] -> (t, il)
			| scall ->				
					List.fold_left (fun (t, il) (_, _, sys) ->
					let name = procname ^ eng.sep ^ dir ^ eng.sep ^replace_string '/' eng.sep path^eng.sep^ sys in 
						add_rule t 
						(name, 
							[], 
							[(name, [], false)], 
							[(mk_fact_name sys ^eng.sep ^"Allowed", [String procname; List [String dir ; String path]], true)])
				, name::il) (t, il) scall
		) (t, il) ctx.Context.ctx_fsys in 
		(t, il)) (t, il) proc in
		

(* initialize attacks on channels!!! *)
let t = add_comment t "attacker policy:" in

	let t, il = List.fold_left (fun (t, il) (c, ty) -> 
		match Context.pol_get_attack_opt pol ty with 
		| Some attk -> add_rule t (mk_fact_name c ^ eng.sep ^ attk, 
			[], 
			[(mk_fact_name c ^ eng.sep ^ attk ^ eng.sep ^ "init", [], false)], 
			[(mk_fact_name attk ^ eng.sep ^"Allowed", [String c], true)]
		), (mk_fact_name c ^ eng.sep ^ attk ^ eng.sep ^ "init"):: il
		| None -> t, il) (t, il) ctx.Context.ctx_ch in 
	


	let t = add_comment t "processes:" in
	let t = List.fold_left (fun t p -> translate_process eng t p) t (List.rev proc) in


	let init_list = List.map (fun p -> String.capitalize_ascii (p.Context.proc_name ^ (string_of_int p.Context.proc_pid)) ^ eng.sep^"init") proc in 

	let init_list = init_list @ il in 

	(t, init_list, lem), {prt_sep=eng.sep}


