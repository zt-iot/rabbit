(* For translating to and printing Tamarin models.
   * 'Rabbit' is a string value palceholder for void output of system calls and functions.
   * GlobalFact is fact that does not bound to any process or channel. Currently 
   it only contains reserved facts.
 *)
let separator = ref "_"
let fresh_ident = ref "rab"
let fresh_string = ref "rab"

let mk_my_fact_name s = 
  (String.capitalize_ascii s)

let replace_string s t str = 
  String.concat t (String.split_on_char s str)

 let int_to_list n =
  let rec aux i acc =
    if i < 0 then acc
    else aux (i - 1) (i :: acc)
  in
  aux (n - 1) []


let mult_list_with_concat l sep = 
  match l with
  | h :: t -> h ^ (List.fold_left (fun r s-> r ^ sep ^ s) "" t) 
  | [] -> ""


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
  | MetaVar of int
  | LocVar of int
  | TopVar of int
  | Apply of string * expr list
  | String of string
  | Integer of int
  | List of expr list
  | One
  | Int of string
  | AddOne of expr

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


(* state consists of its identifier and numbers of variables.
    How to read: *)
type action = 
  | ActionReturn of expr
  | ActionAssign of (int * bool) * expr
  | ActionSeq of action * action
  | ActionAddMeta of int
  | ActionIntro of expr list
  | ActionPopLoc of int
  | ActionPopMeta of int
  | ActionLetTop of expr

type state = {
  state_namespace : string;
  state_index : ((int list) * int) list; 
  state_vars : int * int * int;
}

type transition = {
  transition_namespace : string;
  transition_name : string;
  transition_from : state;
  transition_to : state;
  transition_pre : fact list;
  transition_post : fact list;
  transition_function_facts : action;
  transition_label : fact list;
}

type rule = 
| Rule of string * string * fact list * fact list * fact list
| Comment of string

(* type tamarin = signature * rule list *)

type model = {
  model_name : string;
  model_states : state list;
  model_transitions : transition list;
  model_init_rules : rule list ;
  model_init_state : state
}

let add_rule (mo : model) (a, b, c, d, e) = 
  {mo with model_init_rules = (Rule (a, b, c, d, e)) :: mo.model_init_rules}

let add_comment (mo : model) r = 
  {mo with model_init_rules = (Comment r) :: mo.model_init_rules}
  
let add_comment t s = ((Comment s) :: ((t)))

let add_state m s = {m with model_states = s :: m.model_states}

let initial_state name = 
{
  state_namespace = name;
  state_index = [];
  state_vars = (0, 0, 0)
}

let initial_model name = 
  let st = initial_state name in
  {model_name = name; model_states = [st]; model_transitions = []; model_init_rules = []; model_init_state = st}, st

let add_transition m t = {m with model_transitions = t :: m.model_transitions}

let get_state_fact_name (s : state) = 
  "State" ^  !separator  ^ s.state_namespace

let state_index_to_string_aux (st : state) =
  (List.fold_left (fun s (scope, ind) -> s ^  !separator  ^
    (mult_list_with_concat (List.map string_of_int scope) "_")
    ^ "_" ^ string_of_int ind) "" (List.rev st.state_index)) 

let state_index_to_string st = String (state_index_to_string_aux st)
  
let mk_state (st : state) return_var = 
  let meta_num, loc_num, top_num = st.state_vars in
  (get_state_fact_name st, 
    [
      List [state_index_to_string st];
      return_var; 
      List (List.map (fun i -> MetaVar i) (int_to_list meta_num)); 
      List (List.map (fun i -> LocVar i) (int_to_list loc_num)); 
      List (List.map (fun i -> TopVar i) (int_to_list top_num))
      ], config_linear) 
(* 

let mk_state_app eng return_var (meta_num, loc_num, top_num) e tnum = 
  (get_state_fact_name st, 
      [
      List [engine_state eng; tnum] ;
      return_var; 
      List (List.map (fun i -> MetaVar i) (int_to_list meta_num)); 
      List (e :: (List.map (fun i -> LocVar i) (int_to_list loc_num))); 
      List (List.map (fun i -> TopVar i) (int_to_list top_num))
      ], config_linear) 

let mk_state_app_list eng return_var (meta_num, loc_num, top_num) el tnum = 
  (get_state_fact_name st, 
      [
      List [engine_state eng; tnum] ;
      return_var; 
      List (List.map (fun i -> MetaVar i) (int_to_list meta_num)); 
      List (el @ (List.map (fun i -> LocVar i) (int_to_list loc_num))); 
      List (List.map (fun i -> TopVar i) (int_to_list top_num))
      ], config_linear) 

let mk_state_app_top eng return_var (meta_num, loc_num, top_num) e tnum = 
  (get_state_fact_name st, 
      [
      List [engine_state eng; tnum] ;
      return_var; 
      List (List.map (fun i -> MetaVar i) (int_to_list meta_num)); 
      List ((List.map (fun i -> LocVar i) (int_to_list loc_num))); 
      List (e ::  (List.map (fun i -> TopVar i) (int_to_list top_num)))
      ], config_linear) 

let mk_state_shift eng return_var (meta_num, loc_num, top_num) (n, m, l) tnum = 
  (get_state_fact_name st, 
      [
      List [engine_state eng; tnum] ;
      return_var; 
      List (List.map (fun i -> MetaVar (i+n)) (int_to_list meta_num)); 
      List (List.map (fun i -> LocVar (i+m)) (int_to_list loc_num)); 
      List (List.map (fun i -> TopVar (i+l)) (int_to_list top_num))
     ], config_linear) 

let mk_state_replace eng return_var (meta_num, loc_num, top_num) (j, b) e tnum = 
  (get_state_fact_name st, 
      [      
      List [engine_state eng; tnum] ;
      return_var; 
      List (List.map (fun i -> MetaVar i) (int_to_list meta_num)); 
      List (List.map (fun i -> if (not b) && i = j then e else LocVar i) (int_to_list loc_num)); 
      List (List.map (fun i -> if b && i = j then e else TopVar i) (int_to_list top_num)) 
    ], config_linear) 

let mk_state_replace_and_shift eng return_var (meta_num, loc_num, top_num) (n, m, l) (j, b) e tnum =  
  (get_state_fact_name st, 
      [      
      List [engine_state eng; tnum] ;
      return_var;  
      List (List.map (fun i -> MetaVar (i+n)) (int_to_list meta_num)); 
      List (List.map (fun i -> if (not b) && i = j then e else LocVar (i+m)) (int_to_list loc_num)); 
      List (List.map (fun i -> if b && i = j  then e else TopVar (i+l)) (int_to_list top_num))
    ], config_linear) 
 *)

(* tamarin as a pair of a sigature and a finite list of models *)
(* model and its initialization rules *)
type tamarin = signature * model list * rule list

let add_fun (((fns,eqns), mo, rules) : tamarin) f : tamarin = ((f::fns, eqns), mo, rules)
let add_const (((fns,eqns), mo, rules) : tamarin) c = (((c,0)::fns, eqns), mo, rules)
let add_eqn (((fns,eqns), mo, rules): tamarin) eq = ((fns, eq::eqns), mo, rules)

let add_model (t : tamarin) m = 
  let (si, mo, rules) = t in 
    (si, m :: mo, rules)

let tamarin_add_rule (t : tamarin) (a, b, c, d, e) = 
  let (si, mo, rules) = t in 
    (si, mo, (Rule (a, b, c, d, e)) :: rules)

let tamarin_add_comment (t : tamarin) s = 
  let (si, mo, rules) = t in 
    (si, mo, (Comment s :: rules))

let empty_tamarin : tamarin  = empty_signature , [], []

let get_return_var () =
  Var ("return" ^ !separator ^ "var") 

let rec print_expr e = 
  match e with
  | Var s -> s 
  | MetaVar i -> "meta"^ !separator ^string_of_int i
  | LocVar i -> "loc"^ !separator ^string_of_int i
  | TopVar i -> "top"^ !separator ^string_of_int i
  | Apply (s, el) -> s ^ "(" ^ (mult_list_with_concat (List.map (print_expr) el) ", ") ^ ")"
  | String s -> "\'rab" ^  !separator  ^ (replace_string '/'  !separator  s)^"\'"
  | Integer i -> "\'"^string_of_int i^"\'"
  | List el -> 
     (match el with
     | [] -> "\'rab"^ !separator ^"\'"
     | [e] -> print_expr e 
     | _ -> 	"<" ^ (mult_list_with_concat (List.map (print_expr) el) ", ") ^ ">")
  | One -> "%1"
  | Int v -> "%"^v
  | AddOne e -> (print_expr e)^" %+ %1"

let print_signature (fns, eqns) = 
  let print_functions fns = 
    (if List.length fns = 0 then "" else "functions: ")^(mult_list_with_concat (List.map (fun (f, ar) -> f ^"/"^(string_of_int ar)) fns) ", ") ^"\n" in 
  let print_equations eqns = 
    (if List.length eqns = 0 then "" else "equations: ")^(mult_list_with_concat (List.map (fun (e1, e2) -> (print_expr e1)^"="^(print_expr e2)) eqns) ", ") ^"\n" in 
  (print_functions fns) ^ (print_equations eqns)

let print_fact_plain (f, el) = 
  f^"(" ^ (mult_list_with_concat (List.map (print_expr) el) ", ") ^ ")" 

let print_transition (tr : transition) (is_dev : bool) = 
  (* name of this rule: *)
  let f = tr.transition_namespace ^ !separator ^ tr.transition_name in 
  let pre = tr.transition_pre in
  let post = tr.transition_post in
  let label = tr.transition_label in
  let initial_state_fact = mk_state tr.transition_from (get_return_var ()) in 
  let final_state_fact = mk_state tr.transition_to (get_return_var ()) in 
  (* how to print a fact *)
  let print_fact (f, el, b) = 
    (if b.is_persist then "!" else "") ^f^"(" ^ (mult_list_with_concat (List.map print_expr el) ", ") ^ ")" 
    ^ if b.priority = 0 then "[-,no_precomp]" 
      else if b.priority = 1 then "[-]" 
      else if b.priority = 2 then ""
      else if b.priority = 3 then "[+]" else "" 
  in 
  let print_fact2 (f, el, b) = 
    (if b.is_persist then "!" else "") ^f^"(" ^ (mult_list_with_concat (List.map print_expr el) ", ") ^ ")" in 



    "rule "^f ^ (if tr.transition_namespace = "" || not is_dev then "" else "[role=\"" ^ tr.transition_namespace ^ "\"]") ^ " : " ^ 
	
    "["^(mult_list_with_concat (List.map print_fact (initial_state_fact :: pre)) ", ") ^ "]" ^
	  
    (* when the transition has label *)
    (match tr.transition_label with 
	   | [] -> "-->" 
	   | _ -> 	"--[" ^ (mult_list_with_concat (List.map print_fact2 label) ", ") ^ "]->")^

	    "["^(mult_list_with_concat (List.map print_fact2 (final_state_fact :: post)) ", ") ^ "] \n"	

let print_model m is_dev = 
  List.map (fun t -> print_transition t is_dev) m.model_transitions |> String.concat "\n"

let print_rule2 (f, act, pre, label, post) dev = 
  let print_fact (f, el, b) = 
    (if b.is_persist then "!" else "") ^f^"(" ^ (mult_list_with_concat (List.map print_expr el) ", ") ^ ")" 
    ^ if b.priority = 0 then "[-,no_precomp]" 
      else if b.priority = 1 then "[-]" 
      else if b.priority = 2 then ""
      else if b.priority = 3 then "[+]" else "" 
  in 
  let print_fact2 (f, el, b) = 
    (if b.is_persist then "!" else "") ^f^"(" ^ (mult_list_with_concat (List.map print_expr el) ", ") ^ ")" in 
  "rule "^f ^
    (if act = "" || not dev then "" else "[role=\"" ^act^ "\"]") ^
      " : "^ 
  "["^(mult_list_with_concat (List.map print_fact pre) ", ") ^ "]" ^
    (match label with 
      | [] -> "-->" 
      | _ -> 	"--[" ^ (mult_list_with_concat (List.map print_fact2 label) ", ") ^ "]->")^

      "["^(mult_list_with_concat (List.map print_fact2 post) ", ") ^ "] \n"	

let print_comment s = "\n// "^s^"\n\n" 
  
let print_rule prt r dev = match r with | Rule (a, b, c, d, e) -> print_rule2 (a, b, c, d, e) dev | Comment s ->print_comment s 
  
  

type lemma = 
  | PlainLemma of string * string
  | ReachabilityLemma of string * string list * (string * expr list) list
  | CorrespondenceLemma of string * string list * (string * expr list) * (string * expr list)

let print_lemma lemma = 
  match lemma with
  | PlainLemma (l, p) -> "\nlemma "^l^" : "^p 
  | ReachabilityLemma (l, vars, facts) -> "\nlemma "^l^ " : exists-trace \"Ex "^
    (mult_list_with_concat vars " ") ^" " ^
    (mult_list_with_concat (List.map (fun (f, _) -> "#"^f^ !separator ) facts) " ") ^ " . " ^
    (mult_list_with_concat (List.map (fun (f, el) -> print_fact_plain (f, el) ^ " @ " ^f^ !separator ) facts) " & ") ^ " \""

  | CorrespondenceLemma (l, vars, (f1, el1), (f2, el2)) -> "\nlemma "^l^ " : all-traces \"All "^
    (mult_list_with_concat vars " ") ^" " ^ "#"^f1^ !separator  ^" . " ^
    print_fact_plain (f1, el1) ^ " @ " ^ f1^ !separator  ^" ==> "^
    "Ex " ^ "#"^f2^ !separator  ^ " . " ^ print_fact_plain (f2, el2) ^ " @ " ^ f2^ !separator  ^" & "^
    f2^ !separator  ^" < "^ f1^ !separator  ^ " \""


let print_tamarin ((sign, models), init_list, procs, lem) is_dev = 
  "theory rabbit\n\nbegin\nbuiltins: natural-numbers\n\n"^
  print_signature sign ^
    (mult_list_with_concat (List.map (fun m -> print_model m is_dev) (List.rev models)) "")^
	
  	List.fold_left (fun l s -> l^"\nrestriction "^s^" : \" All #i #j . "^s^"() @ #i & "^s^"() @ #j ==> #i = #j \"") "" init_list ^ "\n" ^

    "\nrestriction Init"^ !separator ^" : \" All x #i #j . Init"^ !separator ^"(x) @ #i & Init"^ !separator ^"(x) @ #j ==> #i = #j \"\n" ^

	  (* if then else restriction *)

	  (* "\nrestriction OnlyOnce : \" All x #i #j . OnlyOnce(x) @ #i & OnlyOnce(x) @ #j ==> #i = #j \"\n" ^ *)

    "restriction Equality: \" All x y #i. Eq(x,y) @ #i ==> x = y\"\n" 

    ^

    "restriction Inequality: \"All x #i. Neq(x,x) @ #i ==> F\"\n" 

    ^

    "rule Equality_gen: [] --> [!Eq"^ !separator ^"(x,x)]\n" 

    ^

    "rule NEquality_gen: [] --[NEq_"^ !separator ^"(x,y)]-> [!NEq"^ !separator ^"(x,y)]\n" 

    ^

    "restriction NEquality_rule: \"All x #i. NEq_"^ !separator ^"(x,x) @ #i ==> F\"\n"

    ^

    List.fold_left (fun s p -> 
      let tfact = "Trace"^ !separator ^p in 
      s^"lemma "^tfact^"[use_induction,reuse] : all-traces \"All x y #i #j . "^tfact^"(x, y) @ #i & "^tfact^"(x, y) @ #j ==> #i = #j\"\n") "" (List.rev procs) 

    ^

    List.fold_left (fun l lem -> l ^ print_lemma lem) "" lem ^"\nend\n"


let index_inc index scope = 
  match scope with
  | None ->
    begin match index with
    | (l,i)::lst -> (l,i+1)::lst
    | _ -> error ~loc:Location.Nowhere (UnintendedError "index ill-defined")
    end
  | Some s -> (s, 0)::index

let next_state ?(shift=(0,0,0)) st scope  = 
  let (a, b, c) = shift in 
  let (meta_num, loc_num, top_num) = st.state_vars in
  {st with state_index = index_inc st.state_index scope; 
           state_vars = (meta_num + a, loc_num + b, top_num + c)}
  (* {st with state_index = index_inc st.state_index scope} *)

(* let next_state_app st scope num = 
  {st with state_index = index_inc st.state_index scope} *)
  

let rec translate_expr ?(ch=false) {Location.data=e; Location.loc=loc} = 
  let translate_expr' = function
    | Syntax.ExtConst s -> Apply (s, [])
    | Syntax.Const s -> error ~loc (UnintendedError ("translating constant " ^ s))
    | Syntax.TopVariable (v, i) -> TopVar i
    | Syntax.LocVariable (v, i) -> LocVar i
    | Syntax.MetaVariable (v, i) -> MetaVar i
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
    | Syntax.TopVariable (v, i) -> TopVar i, []
    | Syntax.LocVariable (v, i) -> LocVar i, []
    | Syntax.MetaVariable (v, i) -> MetaVar i, []
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



(* let make_rule_name eng scope = 
  eng.namespace^engine_state_aux eng ^ (match scope with Some scope -> (mult_list_with_concat (List.map string_of_int scope) "_") | None -> "") *)

let lctx_to_var_list lctx =
  (List.map (fun s -> Var s) lctx)

let rec var_list_replace lctx s e =
  match lctx with
  | Var w :: l -> (if w = s then e else Var w) :: (var_list_replace l s e)
  | _ :: l -> error ~loc:Location.Nowhere (UnintendedError "lctx is not list") 
  | [] -> [] 


(* let append_loc state e =
  (engine_state eng, 
    [return_var; 
     List (List.map (fun i -> Var ("meta"^ !separator  ^ (int_to_list meta_num)))); 
     List (List.map (fun i -> Var ("meta"^ !separator  ^ (int_to_list loc_num)))); 
     List (List.map (fun i -> Var ("meta"^ !separator  ^ (int_to_list top_num))));
     ])  *)

let translate_fact namespace f = 
  match f.Location.data with
  | Syntax.Fact(id, el) -> 
    let el, gv = List.fold_left (fun (el, gv) e -> let e, g = translate_expr2 e in
                                  (el @ [e], gv @ g)) ([],[]) el in    
    let gv = List.map (fun s -> ("Const"^ !separator , [String s ; Var s], config_persist)) gv in 
    (mk_my_fact_name id, (String namespace) :: el, config_linear), gv, []

  | Syntax.GlobalFact(id, el) -> 
    let el, gv = List.fold_left (fun (el, gv) e -> let e, g = translate_expr2 e in
                                  (el @ [e], gv @ g)) ([],[]) el in    
    let gv = List.map (fun s -> ("Const"^ !separator , [String s ; Var s], config_persist)) gv in 

    (mk_my_fact_name id, el, config_linear), gv, []

  | Syntax.ChannelFact(ch, id, el) ->
    let el, gv = List.fold_left (fun (el, gv) e -> let e, g = translate_expr2 e in
                                  (el @ [e], gv @ g)) ([],[]) (ch::el) in    
    let gv = List.map (fun s -> ("Const"^ !separator , [String s ; Var s], config_persist)) gv in 
    
    (* let acp = ("ACP"^ !separator ^"chan", String eng.namespace, String ch, config_persist) in  *)
    
    (mk_my_fact_name id, el, config_linear), gv, [translate_expr ch]

  | Syntax.PathFact (path, id, el) -> 
    let el, gv = List.fold_left (fun (el, gv) e -> let e, g = translate_expr2 e in
                                  (el @ [e], gv @ g)) ([],[]) (path::el) in    
    let gv = List.map (fun s -> ("Const"^ !separator , [String s ; Var s], config_persist)) gv in 
    
    (* let acp = ("ACP"^ !separator "path", String eng.namespace, String ch, config_persist) in  *)

    (mk_my_fact_name id, (String namespace)::el, config_linear), gv, [translate_expr path]

  | Syntax.ResFact (0, el) -> 
    let el, gv = List.fold_left (fun (el, gv) e -> let e, g = translate_expr2 e in
                                  (el @ [e], gv @ g)) ([],[]) (el) in    
    let gv = List.map (fun s -> ("Const"^ !separator , [String s ; Var s], config_persist)) gv in 
    
    (* let acp = ("ACP"^ !separator "path", String eng.namespace, String ch, config_persist) in  *)

    ("Eq"^ !separator , el, config_persist), gv, []

  | Syntax.ResFact (1, el) -> 
    let el, gv = List.fold_left (fun (el, gv) e -> let e, g = translate_expr2 e in
                                  (el @ [e], gv @ g)) ([],[]) (el) in    
    let gv = List.map (fun s -> ("Const"^ !separator , [String s ; Var s], config_persist)) gv in 
    
    (* let acp = ("ACP"^ !separator "path", String eng.namespace, String ch, config_persist) in  *)

    ("NEq"^ !separator , el, config_persist), gv, []

  | _ -> 
    error ~loc:Location.Nowhere (UnintendedError "process fact")

let translate_facts namespace fl =
  List.fold_left (fun (fl, gv, acps) f -> 
              let (f, gv', acps') = translate_fact namespace f in 
              (fl @ [f], gv@gv', acps@acps')) ([],[],[]) fl

let rec expr_shift_meta shift e = 
  let e' = 
  match e.Location.data with
  | Syntax.MetaVariable (v, i) -> Syntax.MetaVariable (v, i+ shift)
  | Syntax.Apply (o, el) -> 
    Syntax.Apply (o, List.map (expr_shift_meta shift) el)  
  | Syntax.Tuple el -> 
    Syntax.Tuple (List.map (expr_shift_meta shift) el)  
  | _ -> e.Location.data
  in Location.locate ~loc:e.Location.loc e' 

let fact_shift_meta shift f = 
  match f.Location.data with
  | Syntax.Fact(id, el) -> 
    Syntax.Fact(id, (List.map (expr_shift_meta shift) el))

  | Syntax.GlobalFact(id, el) -> 
    Syntax.GlobalFact(id, (List.map (expr_shift_meta shift) el))

  | Syntax.ChannelFact(ch, id, el) -> 
    Syntax.ChannelFact(expr_shift_meta shift ch, id, (List.map (expr_shift_meta shift) el))

  | Syntax.PathFact (path, id, el) -> 
    Syntax.PathFact(expr_shift_meta shift path, id, (List.map (expr_shift_meta shift) el))
  
  | Syntax.ResFact (i, el) -> 
    Syntax.ResFact(i, (List.map (expr_shift_meta shift) el))

  | _ -> 
    error ~loc:Location.Nowhere (UnintendedError "process fact")

let rec tamarin_expr_shift_meta shift e = 
  match e with
  | MetaVar i -> MetaVar (i + shift)
  | Apply (s, el) ->
    Apply (s, List.map (tamarin_expr_shift_meta shift) el)
  | List el -> List (List.map (tamarin_expr_shift_meta shift) el)
  | _ -> e

let rec pop_hd n lst =
  if n > 0 then
  match lst with
  | _ :: lst -> pop_hd (n-1) lst 
  | [] -> error ~loc:Location.Nowhere (UnintendedError "pop empty list")
  else if n = 0 then lst else error ~loc:Location.Nowhere (UnintendedError "pop negative elements")


(* 
  given a model, the current state that is promised to be already in the model,
  this function returns an extended model 
*)
let rec translate_cmd mo (st : state) funs syscalls vars scope syscall {Location.data=c; Location.loc=loc} = 
  let return_var = Var ("return"^ !separator ) in
  let return_unit = String ("unit"^ !separator ) in 
  let (meta_num, loc_num, top_num) = vars in 
  
  match c with
  | Syntax.Return e ->
    let e, gv = translate_expr2 e in  
    let gv = List.map (fun s -> ("Const"^ !separator , [String s ; Var s], config_persist)) gv in 
    let (st_f : state) = next_state st scope in 
    let mo = add_state mo st_f in 
    let mo = add_transition mo {
      transition_namespace = mo.model_name;
      transition_name = "return";
      transition_from = st;
      transition_to = st_f;
      transition_pre = gv;
      transition_post = [];
      transition_function_facts = ActionReturn e;
      transition_label = []
    } in
    (mo, st_f)


  | Syntax.Skip -> 
    let st_f = next_state st scope in 
    let mo = add_state mo st_f in 
    let mo = add_transition mo {
      transition_namespace = mo.model_name;
      transition_name = "skip";
      transition_from = st;
      transition_to = st_f;
      transition_pre = [];
      transition_post = [];
      transition_function_facts = ActionReturn return_unit;
      transition_label = []
    } in
    (mo, st_f)

  | Syntax.Sequence (c1, c2) -> 
    let (mo, st) = translate_cmd mo st funs syscalls vars scope syscall c1 in
    let (mo, st) = translate_cmd mo st funs syscalls vars None syscall c2 in
    (mo, st)

  | Syntax.Put fl -> 
    let fl, gv, acps = translate_facts mo.model_name fl in
    let acps = List.map (fun target -> ("ACP"^ !separator , [String mo.model_name; 
                                                    target; 
                                                    String syscall], config_persist)) acps in
    let st_f = next_state st scope in
    let mo = add_state mo st_f in
    let mo = add_transition mo {
      transition_namespace = mo.model_name;
      transition_name = "put";
      transition_from = st;
      transition_to = st_f;
      transition_pre = gv @ acps;
      transition_post = fl;
      transition_function_facts = ActionReturn return_unit;
      transition_label = []
    } in                                            
    (mo, st_f)

  | Syntax.Let (v, e, c) -> 
    
    let e, gv = translate_expr2 e in  
    let gv = List.map (fun s -> ("Const"^ !separator , [String s ; Var s], config_persist)) gv in 
    
    let st_f = next_state ~shift:(0,1,0) st scope  in 
    let mo = add_state mo st_f in
    let mo = add_transition mo {
      transition_namespace = mo.model_name;
      transition_name = "let_intro";
      transition_from = st;
      transition_to = st_f;
      transition_pre = gv;
      transition_post = [];
      transition_function_facts = ActionIntro [e];
      transition_label = []
    } in
  
    let (mo, st) = translate_cmd mo st_f funs syscalls (meta_num, loc_num+1, top_num) None syscall c in

    let st_f = next_state ~shift:(0,-1,0) st scope in 
    let mo = add_state mo st_f in
    let mo = add_transition mo {
      transition_namespace = mo.model_name;
      transition_name = "let_out";
      transition_from = st;
      transition_to = st_f;
      transition_pre = gv;
      transition_post = [];
      transition_function_facts = ActionPopLoc 1;
      transition_label = []
    } in
    (mo, st_f)

  | Syntax.Assign ((v, di), e) -> 

    let e, gv = translate_expr2 e in  
    let gv = List.map (fun s -> ("Const"^ !separator , [String s ; Var s], config_persist)) gv in 
    let st_f = next_state st scope in
    let mo = add_state mo st_f in
    let mo = add_transition mo {
      transition_namespace = mo.model_name;
      transition_name = "assign";
      transition_from = st;
      transition_to = st_f;
      transition_pre = gv;
      transition_post = [];
      transition_function_facts = ActionAssign (di, e);
      transition_label = []
    } in
    (mo, st_f)

  | Syntax.FCall (ov, f, el) ->
    let el, gv = List.fold_left (fun (el, gv) e -> let e, g = translate_expr2 e in
                                  (el @ [e], gv @ g)) ([],[]) el in  
    let el = List.rev el in  
    let gv = List.map (fun s -> ("Const"^ !separator , [String s ; Var s], config_persist)) gv in 
    
    let (f, args, cmd) = List.find (fun (f', args, cmd) -> f = f') funs in 

    let st_f = next_state ~shift:(0,List.length el,0) st scope in
    let mo = add_state mo st_f in
    let mo = add_transition mo {
      transition_namespace = mo.model_name;
      transition_name = "fcall_intro";
      transition_from = st;
      transition_to = st_f;
      transition_pre = gv;
      transition_post = [];
      transition_function_facts = ActionIntro el;
      transition_label = []
    } in

    let (mo, st) = translate_cmd mo st_f funs syscalls (meta_num, loc_num + (List.length el), top_num) None syscall cmd in

    let st_f = next_state ~shift:(0,- (List.length el),0) st scope in
    let mo = add_state mo st_f in
    let mo = add_transition mo {
      transition_namespace = mo.model_name;
      transition_name = "fcall_out";
      transition_from = st;
      transition_to = st_f;
      transition_pre = [];
      transition_post = [];
      transition_function_facts = 
      (match ov with
      | None -> ActionPopLoc (List.length el)
      | Some (_, v) -> ActionSeq (ActionPopLoc (List.length el), ActionAssign (v, return_var))
      );
      transition_label = []
    } in
    (mo, st_f)      

  | Syntax.SCall (ov, o, el) ->
    let el, gv = List.fold_left (fun (el, gv) e -> let e, g = translate_expr2 e in
                                  (el @ [e], gv @ g)) ([],[]) el in    
    let el = List.rev el in 
    let gv = List.map (fun s -> ("Const"^ !separator , [String s ; Var s], config_persist)) gv in 
    
    let (f, args, cmd) = List.find (fun (f', args, cmd) -> o = f') syscalls in 

    let st_f = next_state ~shift:(0,List.length el,0) st scope in
    let mo = add_state mo st_f in
    let mo = add_transition mo {
      transition_namespace = mo.model_name;
      transition_name = "scall_intro";
      transition_from = st;
      transition_to = st_f;
      transition_pre = gv;
      transition_post = [];
      transition_function_facts = ActionIntro el;
      transition_label = []
    } in

    let (mo, st) = translate_cmd mo st_f funs syscalls (meta_num, loc_num + (List.length el), top_num) None o cmd in

    let st_f = next_state ~shift:(0, - (List.length el),0) st scope in
    let mo = add_state mo st_f in
    let mo = add_transition mo {
      transition_namespace = mo.model_name;
      transition_name = "scall_out";
      transition_from = st;
      transition_to = st_f;
      transition_pre = [];
      transition_post = [];
      transition_function_facts = 
      (match ov with
      | None -> ActionPopLoc (List.length el)
      | Some (_, v) -> ActionSeq (ActionPopLoc (List.length el), ActionAssign (v, return_var))
      );
      transition_label = []
    } in
    (mo, st_f)

  | Syntax.Case (cs) ->
    let scope_lst =
      begin match scope with
      | None ->
        List.map (fun i -> Some [i]) (List.init (List.length cs) (fun i -> i))
      | Some l ->
        List.map (fun i -> Some (i :: l)) (List.init (List.length cs) (fun i -> i))
      end in 

    (* final state for all branches *)
    let st_f = next_state st None in

    let mo = List.fold_left2 (fun mo scope (vl, fl, c) -> 
      let (mo, st) = translate_guarded_cmd mo st funs syscalls vars scope syscall (vl, fl, c) in
      add_transition mo {
        transition_namespace = mo.model_name;
        transition_name = "case_out";
        transition_from = st;
        transition_to = st_f;
        transition_pre = [];
        transition_post = [];
        transition_function_facts = ActionPopMeta (List.length vl);
        transition_label = []
      }) mo scope_lst cs in

    (add_state mo st_f, st_f)

 | Syntax.While (cs1, cs2) ->
    let scope_lst1 =
      begin match scope with
      | None ->
        List.map (fun i -> Some [i]) (List.init (List.length cs1) (fun i -> i))
      | Some l ->
        List.map (fun i -> Some (i :: l)) (List.init (List.length cs1) (fun i -> i))
      end in 
    let scope_lst2 =
      begin match scope with
      | None ->
        List.map (fun i -> Some [i]) (List.init (List.length cs2) (fun i -> i + (List.length cs1)))
      | Some l ->
        List.map (fun i -> Some (i :: l)) (List.init (List.length cs2) (fun i -> i + (List.length cs1)))
      end in 
  
    let st_f = next_state st None in

    let mo = List.fold_left2 (fun mo scope (vl, fl, c) -> 
      let (mo, st_f) = translate_guarded_cmd mo st funs syscalls vars scope syscall (vl, fl, c) in
      add_transition mo {
        transition_namespace = mo.model_name;
        transition_name = "repeat";
        transition_from = st_f;
        transition_to = st;
        transition_pre = [];
        transition_post = [];
        transition_function_facts = ActionPopMeta (List.length vl);
        transition_label = []
      }) mo scope_lst1 cs1 in

    let mo = List.fold_left2 (fun mo scope (vl, fl, c) -> 
      let (mo, st) = translate_guarded_cmd mo st funs syscalls vars scope syscall (vl, fl, c) in
      add_transition mo {
        transition_namespace = mo.model_name;
        transition_name = "repeat_out";
        transition_from = st_f;
        transition_to = st;
        transition_pre = [];
        transition_post = [];
        transition_function_facts = ActionPopMeta (List.length vl);
        transition_label = []
      }) mo scope_lst2 cs2 in
    
    (add_state mo st_f, st_f)

 | Syntax.Event (fl) ->
    let fl, gv, acps = translate_facts mo.model_name fl in 
    let st_f = next_state st scope in
    let mo = add_state mo st_f in
    let mo = add_transition mo {
      transition_namespace = mo.model_name;
      transition_name = "event";
      transition_from = st;
      transition_to = st_f;
      transition_pre = gv;
      transition_post = [];
      transition_function_facts = ActionReturn return_unit;
      transition_label = fl
    } in
  (mo, st_f)

and translate_guarded_cmd mo st funs syscalls vars scope syscall (vl, fl, c) = 
  let (meta_num, loc_num, top_num) = vars in 

  let fl, gv, acps = translate_facts mo.model_name fl in
  let acps = List.map (fun target -> ("ACP"^ !separator , [String mo.model_name; 
                                                      target; 
                                                      String syscall], config_persist)) acps in
  let st_f = next_state ~shift:(List.length vl, 0, 0) st scope in
  let mo = add_state mo st_f in
  (* let eng_f = engine_index_inc eng scope in *)
  let mo = add_transition mo {
    transition_namespace = mo.model_name;
    transition_name = "guarded";
    transition_from = st;
    transition_to = st_f;
    transition_pre = fl @ gv @ acps;
    transition_post = [];
    transition_function_facts = ActionAddMeta (List.length vl);
    transition_label = []
  } in
  let (mo, st_f) = translate_cmd mo st_f funs syscalls (meta_num + List.length vl, loc_num, top_num) None syscall c in
  (mo, st_f)




let translate_process {
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
  let return_unit = String ("unit"^ !separator ) in 
  let sep = !separator in
  (* let t = add_comment t ("- Process name: " ^ namespace) in  *)

  let mo, st = initial_model namespace in 


  (* initialize file system *)
  let mo = List.fold_left (fun mo (path, e, _, _) ->
      (* let path = (mk_dir eng fsys path) in *)
      let e, gv = translate_expr2 e in  
      let gv = List.map (fun s -> ("Const"^ !separator, [String s ; Var s], config_persist)) gv in 
      let name = mk_fact_name  namespace^ replace_string '/' !separator path in 
      add_rule mo (name, "",
            gv,
            [("Init"^ !separator, [List [String namespace; String path]], config_linear)],
            [("File", [String namespace; String path ; e], config_linear)])) mo fls in 
          
  (* initialize memory *)
  let (mo, st) = List.fold_left
		   (fun (mo, st) (x, e) -> 
          let st_f = next_state ~shift:(0,0,1) st None in 
          let mo = add_state mo st_f in
          let e, gv = translate_expr2 e in  
          let gv = List.map (fun s -> ("Const"^ !separator , [String s ; Var s], config_persist)) gv in 
          let mo = add_transition mo {
            transition_namespace = mo.model_name;
            transition_name = "init_mem";
            transition_from = st;
            transition_to = st_f;
            transition_pre = gv;
            transition_post = [];
            transition_function_facts = ActionLetTop [e];
            transition_label = []
          } in
          (mo, st_f)) (mo, st) (List.rev vars) in 


  (* translate the main function *)
  let (mo, st) = translate_cmd mo st fns syscalls (0, 0, List.length vars) None "" m in
  
  mo
  (* List.fold_left (fun t r -> add_rule t 
    (let (rname, pre, lab, post) = r in
    (rname, namespace, pre, lab, post))) t r  *)


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

  separator := (let names = get_fact_names ctx in 
   let rec f s = if List.exists (fun u -> contains u s) names then f (s ^"_") else s in 
    f "_");
  
  fresh_ident := (let rec f s = if List.exists (fun u -> u = s) used_idents then f (s^"_") else s in 
	  f "rab") ;

  fresh_string := (let rec f s = if List.exists (fun u -> u = s) used_string then f (s^"_") else s in 
		                  f "rab") ;
  

  let sep = !separator in

  let t : tamarin = empty_tamarin in

  (* process signature *)
  let t = List.fold_left (fun t (f, k) -> add_fun t (f, k)) t (List.rev ctx.Context.ctx_ext_func) in
  let t = List.fold_left (fun t c -> add_const t c) t (List.rev ctx.Context.ctx_ext_const) in
  let t = List.fold_left (fun t (_, e1, e2) -> add_eqn t (translate_expr e1, translate_expr e2)) t (List.rev def.Context.def_ext_eq) in

  (* let t = add_comment t "external system calls:" in
     let t = List.fold_left (fun t r -> translate_syscall eng t r) t (List.rev def.Context.def_ext_syscall) in*)

  (* let t = add_comment t "Attacks:" in *)
(*   let t = List.fold_left (fun t r -> 

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
 *)
  (* load global variables *)

  (* let t = add_comment t "Global constants:" in *)

  (* global constants *)
  let t = List.fold_left (fun t (v, e) -> 
	      match e with
	      | None -> (* when v is fresh *) 
          tamarin_add_rule t ("Const"^sep^v, "", [("Fr", [Var v], config_linear)], [], [("Const"^sep, [String v ; Var v], config_persist)])
	      | Some e -> (* when v is defined *) 
          let e, gv = translate_expr2 e in  
          let gv = List.map (fun s -> ("Const"^sep, [String s ; Var s], config_persist)) gv in 
      		tamarin_add_rule t ("Const"^sep^v, "", gv, [], [("Const"^sep, [String v ; e], config_persist)])) t (List.rev def.Context.def_const) in

  (* initialize files *)
  (* def_fsys    :  (Name.ident * Name.ident * Syntax.expr) list ; *)
(*   let t = add_comment t "Initial file system:" in
  let t, il = List.fold_left (fun (t, il) (fsys, path, e) ->
		  (* let path = (mk_dir eng fsys path) in *)
		  let e, gv = translate_expr2 sep e in  
		  let gv = List.map (fun s -> ("Const"^sep, [String s ; Var s], config_persist)) gv in 
		  let name = mk_fact_name  fsys^ replace_string '/' sep path ^ sep ^"init" in 
		  add_rule t (name, "",
			      gv,
			      [(name, [], config_linear)],
			      [("File", [String fsys; String path ; e], config_linear)]), name::il) (t, []) def.Context.def_fsys in 

 *)  let il =[] in 

  let t = tamarin_add_comment t "Access control:" in
  (* access control *)
  (* pol_access : (Name.ident * Name.ident list * Name.ident) list ; *)
  let t, il = List.fold_left (fun (t, il) p ->
		  let procname = String.capitalize_ascii (p.Context.proc_name ^ (if p.Context.proc_pid = 0 then "" else string_of_int p.Context.proc_pid)) in 
		  let t, il = List.fold_left (fun (t, il) (c, ty) -> 
			          match List.find_all (fun (a, b, sys) -> a = p.Context.proc_type && List.exists (fun b -> b = ty) b) pol.Context.pol_access with
			          | [] -> (t, il) 
			          | scall -> 
				     List.fold_left (fun (t, il) (_, _, sys) ->
					 let name = procname ^ sep ^ c ^ sep ^ sys in 
					 tamarin_add_rule t 
					   (name, "",
					    [], 
					    [(name, [], config_linear)], 
					    [("ACP"^sep, [String procname; String c; String sys], config_persist)])
					 , name::il) (t, il) scall) (t, il) ctx.Context.ctx_ch in 

      let t, il = List.fold_left (fun (t, il) (c, ty) -> 
                match List.find_all (fun (a, b) -> a = p.Context.proc_type && List.exists (fun b -> b = ty) b) pol.Context.pol_access_all with
                | [] -> (t, il) 
                | _ -> 
             
                 let name = procname ^ sep ^ c ^ sep in 
                 tamarin_add_rule t 
                  (name, "",
                  [], 
                  [(name, [], config_linear)], 
                  [("ACP"^sep, [String procname; String c; String ""], config_persist)]), name::il) (t, il) ctx.Context.ctx_ch in 


		  let t, il = 
		    match List.find_all (fun (a, b, sys) -> a = p.Context.proc_type && (match b with | [] -> true | _ -> false)) pol.Context.pol_access with
		    | [] -> (t, il) 
		    | scall -> 
		       List.fold_left (fun (t, il) (_, _, sys) ->
			   let name = procname ^ sep ^ sys in 
			   tamarin_add_rule t 
			     (name, "",
			      [], 
			      [(name, [], config_linear)], 
			      [(mk_fact_name sys ^ sep ^"Allowed", [String procname], config_persist)])
			   , name::il) (t, il) scall 

		  in 

(*  		  let t, il = List.fold_left (fun (t, il) (dir, path, ty) -> 
			          if (match p.Context.proc_filesys with Some a -> a | None -> "") <> dir then (t, il) else
			            match List.find_all (fun (a, b, sys) -> a = p.Context.proc_type && List.exists (fun b -> b = ty) b) pol.Context.pol_access with
			            | [] -> (t, il)
			            | scall ->				
				       List.fold_left (fun (t, il) (_, _, sys) ->
					   let name = procname ^ sep ^ dir ^ sep ^replace_string '/' sep path ^ sep ^ sys in 
					   add_rule t 
					     (name, "",
					      [], 
					      [(name, [], config_linear)], 
					      [(mk_fact_name sys ^ sep ^"Allowed", [String procname; List [String dir ; String path]], config_persist)])
				           , name::il) (t, il) scall
		                ) (t, il) ctx.Context.ctx_fsys in  *)
 
      let t, il = List.fold_left (fun (t, il) (dir, path, ty) -> 
          if (match p.Context.proc_filesys with Some a -> a | None -> "") <> dir then (t, il) else
            match List.find_all (fun (a, b, sys) -> a = p.Context.proc_type && List.exists (fun b -> b = ty) b) pol.Context.pol_access with
            | [] -> (t, il)
            | scall ->        
         List.fold_left (fun (t, il) (_, _, sys) ->
       let name = procname ^ sep ^ dir ^ sep ^replace_string '/' sep path ^ sep ^ sys in 
       tamarin_add_rule t 
         (name, "",
          [], 
          [(name, [], config_linear)], 
          [("ACP"^sep, [String procname; String path; String sys], config_persist)])
             , name::il) (t, il) scall
              ) (t, il) ctx.Context.ctx_fsys in 

		  (t, il)) (t, il) proc in
  

  (* initialize attacks on channels!!! *)
  (* let t = add_comment t "Attacker policy:" in

     let t, il = List.fold_left (fun (t, il) (c, ty) -> 
     match Context.pol_get_attack_opt pol ty with 
     | Some attk -> add_rule t (mk_fact_name c ^  !separator  ^ attk, "",
     [], 
     [(mk_fact_name c ^  !separator  ^ attk ^  !separator  ^ "init", [], config_linear)], 
     [(mk_fact_name attk ^  !separator  ^"Allowed", [String c], config_linear)]
     ), (mk_fact_name c ^  !separator  ^ attk ^  !separator  ^ "init"):: il
     | None -> t, il) (t, il) ctx.Context.ctx_ch in 
     
   *)

  (* let t = add_comment t "Processes:" in *)
  let t = List.fold_left (fun t p -> add_model t (translate_process p (List.rev def.Context.def_ext_syscall))) t (List.rev proc) in

  (* translating lemmas now *)
  let lem = List.map (fun l ->
    match l.Location.data with
    | Syntax.PlainLemma (l, p) -> PlainLemma (l, p)
(*     | Syntax.ReachabilityLemma (l, vars, evs) -> 
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
 *)    

    | _ -> error ~loc:Location.Nowhere (UnintendedError "")
  ) lem in

  (t, lem)


