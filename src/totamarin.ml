(* 
   For translating to and printing Tamarin models.
   * 'Rabbit' is a string value palceholder for void output of system calls and functions.
   * GlobalFact is fact that does not bound to any process or channel. Currently 
   it only contains reserved facts.
 *)

type to_tamarin_error =
  | UnintendedError of string
  | NotSupportedYet
  | MustbeVar of string

exception Error of to_tamarin_error Location.located

(** [error ~loc err] raises the given runtime error. *)
let error ~loc err = Stdlib.raise (Error (Location.locate ~loc err))

(** Print error description. *)
let print_error err ppf =
  match err with
  | UnintendedError s -> Format.fprintf ppf "Unintended Error: contact the developer. [Hint: %s]" s
  | NotSupportedYet -> Format.fprintf ppf "This feature is not supported yet."
  | MustbeVar v -> Format.fprintf ppf "Argument %s must be a variable." v

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

type rule_config = {is_persist : bool ; priority : int}

let config_linear = {is_persist=false; priority = 2}
let config_persist = {is_persist=true; priority = 2}
let config_linear_delayed = {is_persist=false; priority = 0}
let config_persist_delayed = {is_persist=true; priority = 0}
let config_linear_prior = {is_persist=false; priority = 3}
let config_linear_less = {is_persist=false; priority = 1}
let config_persist_less = {is_persist=true; priority = 1}



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

let print_fact_plain prt (f, el) = 
  f^"(" ^ (mult_list_with_concat (List.map (print_expr prt) el) ", ") ^ ")" 


let print_rule2 prt (f, act, pre, label, post) dev = 
  let print_fact (f, el, b) = 
    (if b.is_persist then "!" else "") ^f^"(" ^ (mult_list_with_concat (List.map (print_expr prt) el) ", ") ^ ")" 
    ^ if b.priority = 0 then "[-,no_precomp]" 
      else if b.priority = 1 then "[-]" 
      else if b.priority = 2 then ""
      else if b.priority = 3 then "[+]" else "" 
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

type lemma = 
  | PlainLemma of string * string
  | ReachabilityLemma of string * string list * (string * expr list) list
  | CorrespondenceLemma of string * string list * (string * expr list) * (string * expr list)

let print_lemma prt lemma = 
  match lemma with
  | PlainLemma (l, p) -> "\nlemma "^l^" : "^p 
  | ReachabilityLemma (l, vars, facts) -> "\nlemma "^l^ " : exists-trace \"Ex "^
    (mult_list_with_concat vars " ") ^" " ^
    (mult_list_with_concat (List.map (fun (f, _) -> "#"^f^prt.prt_sep) facts) " ") ^ " . " ^
    (mult_list_with_concat (List.map (fun (f, el) -> print_fact_plain prt (f, el) ^ " @ " ^f^prt.prt_sep) facts) " & ") ^ " \""

  | CorrespondenceLemma (l, vars, (f1, el1), (f2, el2)) -> "\nlemma "^l^ " : all-traces \"All "^
    (mult_list_with_concat vars " ") ^" " ^ "#"^f1^prt.prt_sep ^" . " ^
    print_fact_plain prt (f1, el1) ^ " @ " ^ f1^prt.prt_sep ^" ==> "^
    "Ex " ^ "#"^f2^prt.prt_sep ^ " . " ^ print_fact_plain prt (f2, el2) ^ " @ " ^ f2^prt.prt_sep ^" & "^
    f2^prt.prt_sep ^" < "^ f1^prt.prt_sep ^ " \""


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

	        List.fold_left (fun l lem -> l ^ print_lemma prt lem) "" lem ^"\nend\n"

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
  in translate_expr2' e

(* let rec translate_stmt eng (t : tamarin) {Location.data=c; Location.loc=loc} syscalls priority_conf =  *)
(* [c](eng) = (rule list, eng') 
    eng can print state
*)
(* let rec translate_cmd eng (t : tamarin) {Location.data=c; Location.loc=loc} = 
  match c with
  | Input.Skip -> 
    let eng_f = engine_index_inc eng in
    let state_i = engine_state eng in
    let state_f = engine_state
    [make_rule eng ]
  (ctx, lctx, Syntax.Skip)
  
  | Input.Sequence (c1, c2) -> 
     let (ctx, lctx, c1) = process_cmd ctx lctx c1 in
     let (ctx, lctx, c2) = process_cmd ctx lctx c2 in
     (ctx, lctx, Syntax.Sequence (c1, c2))

  | Input.Wait (fl, c) -> 
     let lctx' = Context.lctx_add_frame lctx in
     let (ctx, lctx', fl) = process_facts ctx lctx' fl in  
     let (ctx, lctx', c) = process_cmd ctx lctx' c in
     (ctx, lctx, Syntax.Wait (fl, c))

  | Input.Put fl -> 
     let (ctx, fl) = process_facts_closed ctx lctx fl in 
     (ctx, lctx, Syntax.Put (fl))

  | Input.Let (v, e) -> 
     (if Context.lctx_check_var lctx v then error ~loc (AlreadyDefined v) else ());
     let lctx = Context.lctx_add_new_var ~loc lctx v in
     (ctx, lctx, Syntax.Let(v, process_expr ctx lctx e))

  | Input.Assign (v, e) -> 
     (if Context.lctx_check_var lctx v then () else error ~loc (UnknownIdentifier v));
     (ctx, lctx, Syntax.Assign(v, process_expr ctx lctx e))

  | Input.FCall (ov, f, el) ->
     begin match ov with
     | Some v -> 
        (if Context.lctx_check_var lctx v then () else error ~loc (UnknownIdentifier v));
        (ctx, lctx, Syntax.FCall (Some v, process_expr ctx lctx f, List.map (process_expr ctx lctx) el))
     | None -> 
        (ctx, lctx, Syntax.FCall (None, process_expr ctx lctx f, List.map (process_expr ctx lctx) el))
     end
  | Input.SCall (ov, o, args) ->
     (* test if o is defined *)
     (if Context.ctx_check_ext_syscall ctx o then () else error ~loc (UnknownIdentifier o));   
     let args_ty = Context.ctx_get_ext_syscall_arity ~loc ctx o in
     (* test if the number of arguments are correct *)
     (if List.length args = List.length args_ty then () else error ~loc (ArgNumMismatch (o, List.length args, List.length args_ty)));
     (match ov with
     | Some v -> 
        (if Context.lctx_check_var lctx v then () else error ~loc (UnknownIdentifier v));
     | None -> ());
     (ctx, lctx, Syntax.SCall(ov, o, 
        List.map2 (fun arg arg_ty -> 
           let e = process_expr ctx lctx arg in                   
              (match e.Location.data, arg_ty with
              | Syntax.Channel (s, _), Input.TyChannel -> Location.locate ~loc:e.Location.loc (Syntax.Channel (s, o))
              | _, Input.TyChannel -> error ~loc (WrongInputType)
              | _, _ -> e)
              (* , arg_ty *)
           ) args args_ty))

  | Input.Case (al, c1, bl, c2) ->
     let plctx = Context.lctx_add_frame lctx in
     
     let (ctx, lctx1, al) = process_facts ctx plctx al in 
     let (ctx, _, c1) = process_cmd ctx lctx1 c1 in 

     let (ctx, lctx2, bl) = process_facts ctx plctx bl in 
     let (ctx, _, c2) = process_cmd ctx lctx2 c2 in 

     (ctx, lctx, Syntax.Case (al, c1, bl, c2))

 | Input.While (al, bl, c) ->
     let plctx = Context.lctx_add_frame lctx in
     let (ctx, plctx, al) = process_facts ctx plctx al in
     let (ctx, plctx, bl) = process_facts ctx plctx bl in
     let (ctx, plctx, c) = process_cmd ctx plctx c in 
     (ctx, lctx, Syntax.While (al, bl, c))

 | Input.Event (fl) ->
     let (ctx, fl) = process_facts_closed ctx lctx fl in
     (ctx, lctx, Syntax.Event (fl))
  in 
  let (ctx, lctx, c) = process_cmd' ctx lctx c in 
  (ctx, lctx, Location.locate ~loc c)


 *)
let translate_process eng t {
        Context.proc_pid=k;
        Context.proc_name=s;
        Context.proc_attack=attks;
        Context.proc_channel=chs;
        Context.proc_file=fls;
        Context.proc_type=pty_unused;
        Context.proc_filesys=fsys;
        Context.proc_variable=vars;
        Context.proc_function=fns;
        Context.proc_main=m
      } syscalls =
  let namespace = String.capitalize_ascii (s ^ (if k = 0 then "" else string_of_int k)) in (* this must be unique *)
  let eng = eng_set_namespace eng namespace in 
  let eng = eng_set_role eng namespace in

  let eng = eng_set_scope eng "init" in 

  let eng = eng_set_filesys eng (match fsys with Some fsys -> fsys | None -> "") in
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
    (* let eng_start = eng_add_frame (eng_pop_frame (eng_set_mode eng "run")) in *)
    let eng_start = List.fold_left (fun eng v -> eng_add_var eng v) eng args in 
    let eng_start = eng_set_mode eng_start "run" in 
    let eng = eng_add_frame eng in 
    let eng = eng_set_func eng f in 

    let t = add_rule t (eng_state eng_start, eng_get_role eng,
			[("Run"^eng.sep, [String namespace; String f; List (List.map (fun s -> Var s) args); Var ("top_frame"^eng.sep)], config_linear_less)], 
			[],
			[(eng_get_frame_title eng, [String (eng_state eng); List (List.map (fun s -> Var s) (List.rev args)) ; Var ("top_frame"^eng.sep)], config_linear)]) in

    let eng = List.fold_left (fun eng v -> eng_add_var eng v) eng args in 
    (* let t = add_rule t (eng.namespace^f, [(eng.namespace^f, eng_var_list eng)], [], [(eng_state eng, eng_var_list eng)]) in *)
    let eng, t = List.fold_left (fun (eng, t) stmt -> translate_stmt eng t stmt syscalls config_linear_prior) (eng, t) stmts in
    let eng_return = eng_set_mode (eng_set_scope eng f) "return" in 

    let t = add_rule t (eng_state eng_return, eng_get_role eng,
			[(eng_get_frame_title eng, [String (eng_state eng); List (eng_var_list_loc eng) ; List (eng_var_list_top eng)], config_linear_prior)],
			[], 
			[("Return"^eng.sep, [String namespace ; String f; Var v; List (eng_var_list_top eng)], config_linear)])
    in t in  





  let t = List.fold_left (fun t f -> translate_function eng t f) t fns in

  let t = add_comment t ("-- main function ") in 	
  let eng_main = eng_set_scope eng "main" in 
  let t = add_rule t (eng_state (eng_set_mode eng_main "start"), namespace, [(eng_get_frame_title eng, [String (eng_state eng); List (eng_var_list_loc eng) ; (List (eng_var_list_top eng))], config_linear)], [], 
		      [(eng_get_frame_title eng, [String (eng_state eng_main); List (eng_var_list_loc eng_main) ; (List (eng_var_list_top eng))], config_linear)]) in 

  let eng = eng_add_frame eng_main in 
  let eng, t = List.fold_left (fun (eng, t) stmt -> translate_stmt eng t stmt syscalls config_linear) (eng, t) m in
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
  let t = add_comment t "Attacks:" in
  let t = List.fold_left (fun t r -> 

	      let (f, (ch_vars, path_vars, process_vars), (pre, post)) = r in
	      match ch_vars, path_vars, process_vars with
	      | [ch_var], [], [] -> 
		 (* when it is an attack on a channel *)
		 (* find types of channels under this attack *)
		 let ch_tys = List.map fst (List.find_all (fun (ch_t, a) -> a = f) pol.Context.pol_attack) in
		 (* find ch names with ch_ty *)
		 let chs = List.find_all (fun (ch, ch_t) -> List.exists (fun x -> x = ch_t) ch_tys) ctx.Context.ctx_ch in
		 List.fold_left (fun t ch -> translate_attack eng t r ch) t (List.map fst chs) 

	      | [], [path_var], [] -> error ~loc:Location.Nowhere (UnintendedError "attack..")

	      | [], [], [proc_var] -> 
		 (* when it is an attack on a channel *)
		 (* find types of channels under this attack *)
		 let proc_tys = List.map fst (List.find_all (fun (ch_t, a) -> a = f) pol.Context.pol_attack) in
		 (* find ch names with ch_ty *)
		 let procs = List.find_all (fun p -> List.exists (fun x -> x = p.Context.proc_type) proc_tys) proc in
		 List.fold_left (fun t ch -> translate_attack eng t r ch) t (List.map (fun p -> 
						                                 String.capitalize_ascii (p.Context.proc_name ^ (if p.Context.proc_pid = 0 then "" else string_of_int p.Context.proc_pid))
				                                               ) procs)
	      | _, _, _ -> error ~loc:Location.Nowhere (UnintendedError "attack..")) t (List.rev def.Context.def_ext_attack) in

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
			          if (match p.Context.proc_filesys with Some a -> a | None -> "") <> dir then (t, il) else
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
  (* let t = add_comment t "Attacker policy:" in

     let t, il = List.fold_left (fun (t, il) (c, ty) -> 
     match Context.pol_get_attack_opt pol ty with 
     | Some attk -> add_rule t (mk_fact_name c ^ eng.sep ^ attk, "",
     [], 
     [(mk_fact_name c ^ eng.sep ^ attk ^ eng.sep ^ "init", [], config_linear)], 
     [(mk_fact_name attk ^ eng.sep ^"Allowed", [String c], config_linear)]
     ), (mk_fact_name c ^ eng.sep ^ attk ^ eng.sep ^ "init"):: il
     | None -> t, il) (t, il) ctx.Context.ctx_ch in 
     
   *)

  let t = add_comment t "Processes:" in
  let t = List.fold_left (fun t p -> translate_process eng t p (List.rev def.Context.def_ext_syscall)) t (List.rev proc) in


  let init_list = List.map (fun p -> String.capitalize_ascii (p.Context.proc_name ^ 
		                                                (if p.Context.proc_pid = 0 then "" else string_of_int p.Context.proc_pid )
	                               ) ^ eng.sep^"init") proc in 

  let init_list = init_list @ il in 

  (* translating lemmas now *)
  let lem = List.map (fun l ->
    match l.Location.data with
    | Syntax.PlainLemma (l, p) -> PlainLemma (l, p)
    | Syntax.ReachabilityLemma (l, vars, evs) -> 
      ReachabilityLemma (l, vars, 
        List.map (fun ev -> 
          match ev.Location.data with
          | Syntax.Event (id, el) -> (mk_fact_name id), List.map (translate_expr ~ch:false) el
        ) evs)
    | Syntax.CorrespondenceLemma (l, vars, e1, e2) -> 
      CorrespondenceLemma (l, vars, 
          (match e1.Location.data with
          | Syntax.Event (id, el) -> (mk_fact_name id, List.map (translate_expr ~ch:false) el)),
          (match e2.Location.data with
          | Syntax.Event (id, el) -> (mk_fact_name id, List.map (translate_expr ~ch:false) el)))
    ) lem in

  (t, init_list, lem), {prt_sep=eng.sep;}


