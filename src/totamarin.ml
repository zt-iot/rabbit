(* For translating to and printing Tamarin models.
   * 'Rabbit' is a string value palceholder for void output of system calls and functions.
   * GlobalFact is fact that does not bound to any process or channel. Currently 
   it only contains reserved facts.
 *)
let separator = ref "_"
let fresh_ident = ref "rab"
let fresh_string = ref "rab"


let mult_list_with_concat l sep = 
  match l with
  | h :: t -> h ^ (List.fold_left (fun r s-> r ^ sep ^ s) "" t) 
  | [] -> ""

let index_to_string idx =
  (List.fold_left (fun s (scope, ind) -> s ^  !separator  ^
    (mult_list_with_concat (List.map string_of_int scope) "_")
    ^ "_" ^ string_of_int ind) "" (List.rev idx)) 
  

let rec replace_nth lst i new_val =
  match lst with
  | [] -> [] (* If the list is empty, return an empty list *)
  | x :: xs ->
      if i = 0 then new_val :: xs  (* Replace the i-th element *)
      else x :: replace_nth xs (i - 1) new_val (* Recur for the rest *)

let rec pop_n k lst =
  if k <= 0 then ([], lst) (* If k is 0 or negative, return the original list *)
  else match lst with
    | [] -> ([], []) (* Not enough elements, return empty popped list *)
    | x :: xs ->
        let (popped, rest) = pop_n (k - 1) xs in
        (x :: popped, rest)

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
  | MetaNewVar of int
  | Apply of string * expr list
  | String of string
  | Integer of int
  | List of expr list
  | One
  | Int of string
  | AddOne of expr
  | Unit 

let get_return_var () =
  Var ("return" ^ !separator ^ "var") 
  
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

(* type fact = string * expr list * rule_config  *)
(* true is persistent fact *)

type fact = 
  | Fact of 
    string (* fact name *)
    * string (* name space*)
    * expr list
  | ConstantFact of expr * expr 
  | GlobalFact of string * expr list
  | ChannelFact of string * expr * expr list
  | PathFact of string  
    * string (* namespace *)
    * expr (* path *)
    * expr list
  | ProcessFact of string 
    * expr 
    * expr list
  | ResFact of int * expr list
  | AccessFact of string * expr * string 
  | AttackFact of string * expr 
  | FileFact of string  * string * expr
  | InitFact of expr list 
  | LoopFact of 
    string (* namespace *)
    * int (* transition id of the initial transition of the loop *)
    * int (* 0: loop in 2 : loop back 3 : loop out *)
  | TransitionFact of string * int * expr
  | InjectiveFact of 
    string * (* fact name *)
    string * (* namespace *)
    expr * (* identity *)
    expr (* arguments *)
  | FreshFact of expr
  
type fact' = string * expr list * rule_config

let print_fact' (f : fact) : fact' = 
  match f with
  | Fact (fid, nsp, el) -> (mk_my_fact_name fid ^ ! separator ^ nsp, el, config_linear)
  | ConstantFact (e1, e2) -> ("Const"^ !separator , [e1 ; e2], config_persist) 
  | GlobalFact (fid, el) -> (mk_my_fact_name fid, el, config_linear)
  | ChannelFact (fid, ch, el) -> (mk_my_fact_name fid, ch :: el, config_linear)
  | PathFact (fid, nsp, path, el) -> (mk_my_fact_name fid ^ ! separator ^ nsp,path :: el, config_linear)
  | ResFact (0, el) -> ("Eq"^ !separator , el, config_persist)
  | ResFact (1, el) -> ("NEq"^ !separator , el, config_persist)
  | ResFact (2, el) -> ("Fr", el, config_linear)
  | AccessFact (nsp, target, syscall) -> ("ACP"^ !separator, [String nsp; target; String syscall], config_persist )
  | AttackFact (attack, target) ->  ("Attack"^ !separator, [String attack; target], config_persist )
  | FileFact (nsp, path, e) -> ("File"^ !separator ^ nsp, [String path; e], config_linear)
  | InitFact el -> ("Init"^ !separator, el, config_linear)
  | LoopFact (nsp, tid, b) -> ("Loop" ^ ! separator ^ 
    (if b =0 then "Start" else if b = 1 then "Back" else "Finish"), [String (nsp ^ !separator ^ string_of_int tid)], config_linear)
  | TransitionFact (nsp, ind, e) -> ("Transition"^ !separator ^ nsp, [String (string_of_int ind); e], config_linear)
  | InjectiveFact (fid, nsp, id, el) -> (mk_my_fact_name fid ^ ! separator ^ nsp, [id ; el], config_linear)
  | FreshFact (e) -> ("Fr", [e], config_linear)
  | _ -> error ~loc:Location.Nowhere (UnintendedError "process fact")

let mk_constant_fact s = ConstantFact (String s, Var s)


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
  | ActionLetTop of expr list

let rec action_sem (a : action) ((ret, meta_lst, loc_lst, top_lst) : expr * expr list * expr list * expr list) : expr * expr list * expr list * expr list =
  match a with
  | ActionReturn e -> (e, meta_lst, loc_lst, top_lst)
  | ActionAssign ((i, b), e) -> (Unit, meta_lst, (if not b then replace_nth loc_lst i e else loc_lst), (if b then replace_nth top_lst i e else top_lst))
  | ActionSeq (a, b) -> action_sem b (action_sem a (ret, meta_lst, loc_lst, top_lst))
  | ActionAddMeta k -> (Unit, 
   List.map (fun i -> MetaNewVar i) (int_to_list k)
    @ meta_lst, loc_lst, top_lst)
  | ActionIntro el -> (Unit, meta_lst, el @ loc_lst, top_lst)
  | ActionPopLoc k -> (ret, meta_lst, snd (pop_n k loc_lst), top_lst)
  | ActionPopMeta k -> (ret, snd (pop_n k meta_lst), loc_lst, top_lst)
  | ActionLetTop e -> (Unit, meta_lst, loc_lst, e @ top_lst)

type state = {
  state_namespace : string;
  state_index : ((int list) * int) list; 
  state_vars : int * int * int;
}

type transition = {
  transition_id : int;
  transition_namespace : string;
  transition_name : string;
  transition_from : state;
  transition_to : state;
  transition_pre : fact list;
  transition_post : fact list;
  transition_state_transition : (expr * expr list * expr list  * expr list) * (expr * expr list * expr list  * expr list) ;
  transition_label : fact list;
  transition_is_loop_back : bool;
}

let mk_state_transition_from_action a (meta_num, loc_num, top_num) = 
  let return_var = get_return_var () in
  let meta_var = (List.map (fun i -> MetaVar i) (int_to_list meta_num)) in 
  let loc_var = (List.map (fun i -> LocVar i) (int_to_list loc_num)) in 
  let top_var = (List.map (fun i -> TopVar i) (int_to_list top_num)) in 
  (return_var, meta_var, loc_var, top_var),   
  action_sem a (return_var, meta_var, loc_var, top_var)

let get_state_fact_name (s : state) = 
  "State" ^  !separator  ^ s.state_namespace



let state_index_to_string_aux (st : state) =
  index_to_string st.state_index

let state_index_to_string st = String (state_index_to_string_aux st)
  

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
  | Unit -> "\'rab"^ !separator ^"\'"
  | MetaNewVar i -> "new"^ !separator ^string_of_int i
  
let mk_state st (ret, meta, loc, top) : fact' = 
  (* (let (a,b,c) = st.state_vars in
    if not (List.length meta = a ) || not (List.length loc = b ) || not (List.length top = c ) then
      print_endline (print_expr (state_index_to_string st))
    else ()); *)
  (get_state_fact_name st 
  (* ^ (let (a,b,c) = st.state_vars in "_" ^(string_of_int a)^"_" ^(string_of_int b)^"_" ^(string_of_int c)) *)
  , 
  [List [state_index_to_string st]; ret; List meta; List loc; List top], config_linear) 
      

type rule = 
| Rule of string * string * fact' list * fact' list * fact' list
| Comment of string

(* type tamarin = signature * rule list *)

type model = {
  model_name : string;
  model_states : state list;
  model_transitions : transition list;
  model_init_rules : rule list ;
  model_init_state : state ;
  model_transition_id_max : int
}

let add_rule (mo : model) (a, b, c, d, e) = 
  {mo with model_init_rules = (Rule (a, b, List.map print_fact' c, List.map print_fact' d, List.map print_fact' e)) :: mo.model_init_rules}

let add_comment (mo : model) r = 
  {mo with model_init_rules = (Comment r) :: mo.model_init_rules}
  
let add_comment t s = ((Comment s) :: ((t)))

let add_state m s = {m with model_states = s :: m.model_states}

let initial_state name = 
{
  state_namespace = name;
  state_index = [([],0)];
  state_vars = (0, 0, 0)
}

let mk_state_transition st (ret, meta, loc, top) is_initial is_loop : fact' = 
  (get_state_fact_name st, 
  [List [state_index_to_string st; 
    if is_loop then 
      AddOne (Int ("v"^ !separator)) else 
    if is_initial then 
      One else
        Int ("v"^ !separator)]; ret; List meta; List loc; List top], config_linear) 


let initial_model name = 
  let st = initial_state name in
  {model_name = name; model_states = [st]; model_transitions = []; 
  model_init_rules = [Rule ("Init"^name, name, [], [print_fact' (InitFact ([String name]))], [(
    if !Config.tag_transition 
      then  mk_state_transition st (Unit, [], [], []) true false 
      else mk_state st (Unit, [], [], []) 
      )])]; 
  model_init_state = st; model_transition_id_max =0}, st

let initial_state name = 
{
  state_namespace = name;
  state_index = [([],0)];
  state_vars = (1, 0, 0)
}
  
let initial_attacker_model name = 
  let st = initial_state name in
  {model_name = name; model_states = [st]; model_transitions = []; 
  model_init_rules = [
    Rule ("Init"^name, 
    name, 
    [print_fact' (AttackFact (name, MetaNewVar 0))], 
    [], 
    [mk_state st (Unit, [MetaNewVar 0], [], [])])]; 
    model_init_state = st; model_transition_id_max =0}, st
  

let add_transition m t = {m with model_transitions = t :: m.model_transitions; model_transition_id_max = m.model_transition_id_max + 1}



 (* tamarin lemma *)
 type lemma = 
  | PlainLemma of string * string
  | ReachabilityLemma of string * string list * (string * expr list) list
  | CorrespondenceLemma of string * string list * (string * expr list) * (string * expr list)

(* tamarin as a pair of a sigature and a finite list of models *)
(* model and its initialization rules *)
type tamarin = signature * model list * rule list * lemma list

let add_fun (((fns,eqns), mo, rules, lemmas) : tamarin) f : tamarin = ((f::fns, eqns), mo, rules, lemmas)
let add_const (((fns,eqns), mo, rules, lemmas) : tamarin) c = (((c,0)::fns, eqns), mo, rules, lemmas)
let add_eqn (((fns,eqns), mo, rules, lemmas): tamarin) eq = ((fns, eq::eqns), mo, rules, lemmas)

let add_model (t : tamarin) m = 
  let (si, mo, rules, lemmas) = t in 
    (si, m :: mo, rules, lemmas)

let tamarin_add_rule (t : tamarin) (a, b, c, d, e) = 
  let (si, mo, rules, lemmas) = t in 
    (si, mo, (Rule (a, b,List.map print_fact' c,List.map print_fact' d,List.map print_fact' e)) :: rules, lemmas)

let tamarin_add_comment (t : tamarin) s = 
  let (si, mo, rules, lemmas) = t in 
    (si, mo, (Comment s :: rules), lemmas)

let tamarin_add_lemma ((si, mo, rules, lemmas): tamarin) lem = 
  (si, mo, rules, lem :: lemmas)

let empty_tamarin : tamarin  = empty_signature , [] , [] , []



let print_signature (fns, eqns) = 
  let print_functions fns = 
    (if List.length fns = 0 then "" else "functions: ")^(mult_list_with_concat (List.map (fun (f, ar) -> f ^"/"^(string_of_int ar)) fns) ", ") ^"\n" in 
  let print_equations eqns = 
    (if List.length eqns = 0 then "" else "equations: ")^(mult_list_with_concat (List.map (fun (e1, e2) -> (print_expr e1)^"="^(print_expr e2)) eqns) ", ") ^"\n" in 
  (print_functions fns) ^ (print_equations eqns)

let print_fact_plain (f, el) = 
  f^"(" ^ (mult_list_with_concat (List.map (print_expr) el) ", ") ^ ")" 

let print_fact (f, el, b) = 
  (if b.is_persist then "!" else "") ^f^"(" ^ (mult_list_with_concat (List.map print_expr el) ", ") ^ ")" 
  ^ if b.priority = 0 then "[-,no_precomp]" 
    else if b.priority = 1 then "[-]" 
    else if b.priority = 2 then ""
    else if b.priority = 3 then "[+]" else "" 

let print_fact2 (f, el, b) = 
  (if b.is_persist then "!" else "") ^f^"(" ^ (mult_list_with_concat (List.map print_expr el) ", ") ^ ")" 

let transition_to_rule (tr : transition) : rule =    
  let f = tr.transition_namespace ^ !separator ^ tr.transition_name ^ !separator ^ state_index_to_string_aux tr.transition_from ^ !separator ^ state_index_to_string_aux tr.transition_to ^ !separator ^ string_of_int tr.transition_id in 
  let pre = tr.transition_pre in
  let post = tr.transition_post in
  let label = tr.transition_label in
  let initial_state_fact = mk_state tr.transition_from (fst tr.transition_state_transition)  in 
  let final_state_fact = mk_state tr.transition_to (snd tr.transition_state_transition) in 
  Rule (f, tr.transition_namespace, initial_state_fact :: List.map print_fact' pre, List.map print_fact'  label, final_state_fact ::List.map print_fact' post)


    
let transition_to_transition_rule (tr : transition) : rule =    
  let f = tr.transition_namespace ^ 
      !separator ^ tr.transition_name ^ 
      !separator ^ state_index_to_string_aux tr.transition_from ^ 
      !separator ^ state_index_to_string_aux tr.transition_to ^ 
      !separator ^ string_of_int tr.transition_id in 
  let pre = tr.transition_pre in
  let post = tr.transition_post in
  let label = TransitionFact(tr.transition_namespace, tr.transition_id, Int ("v"^ !separator)) :: tr.transition_label in
  let initial_state_fact = mk_state_transition tr.transition_from (fst tr.transition_state_transition) (tr.transition_id = 0) false in 
  let final_state_fact = mk_state_transition tr.transition_to (snd tr.transition_state_transition) (tr.transition_id = 0) tr.transition_is_loop_back in 
  Rule (f, tr.transition_namespace, initial_state_fact :: List.map print_fact' pre, List.map print_fact'  label, final_state_fact ::List.map print_fact' post)
  
  
let print_rule_aux (f, act, pre, label, post) dev = 
  "rule "^f ^
    (if act = "" || not dev then "" else "[role=\"" ^act^ "\"]") ^
      " : "^ 
  "["^(mult_list_with_concat (List.map print_fact pre) ", ") ^ "]" ^
    (match label with 
      | [] -> "-->" 
      | _ -> 	"--[" ^ (mult_list_with_concat (List.map print_fact2 label) ", ") ^ "]->")^

      "["^(mult_list_with_concat (List.map print_fact2 post) ", ") ^ "] \n"	

let print_comment s = "\n// "^s^"\n\n" 
  
let print_rule r dev = match r with | Rule (a, b, c, d, e) -> print_rule_aux (a, b,  c,  d, e) dev | Comment s ->print_comment s 

let print_transition (tr : transition) (is_dev : bool) = 
  let r = transition_to_rule tr in 
  print_rule r is_dev

let print_model m is_dev = 
  (* initialization rule  *)
  (List.map (fun r -> print_rule r is_dev) m.model_init_rules |> String.concat "\n")  ^ "\n" ^
  (List.map (fun t -> print_transition t is_dev) m.model_transitions |> String.concat "\n")

let print_transition_transition_rule (tr : transition) (is_dev : bool) = 
  let r = transition_to_transition_rule tr in 
  print_rule r is_dev

let print_model_transition_rule m is_dev = 
  (* initialization rule  *)
  (List.map (fun r -> print_rule r is_dev) m.model_init_rules |> String.concat "\n")  ^ "\n" ^
  (List.map (fun t -> print_transition_transition_rule t is_dev) m.model_transitions |> String.concat "\n")
  
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


(* signature * model list * rule list * lemma list *)
let print_tamarin ((si, mo_lst, r_lst, lem_lst) : tamarin) is_dev print_transition_label = 
  "theory rabbit\n\nbegin\nbuiltins: natural-numbers\n\n"^

    (* print signature *)
    (print_comment "The signature of our model:\n\n") ^
    print_signature si ^

    (* print initializing rules *)
    (print_comment "Initializing the gloval constants and access policy rules:\n\n") ^
    (mult_list_with_concat (List.map (fun r -> print_rule r is_dev) (List.rev r_lst)) "\n")^
	
    (* print models  *)
    (mult_list_with_concat (List.map (fun m -> 
      (print_comment ("Model:  "^ m.model_name ^"\n")) ^
      (if print_transition_label then print_model_transition_rule else print_model) m is_dev
    ) (List.rev mo_lst)) "\n")^
	
    (* default restrictions *)
    "\nrestriction Init"^ !separator ^" : \" All x #i #j . Init"^ !separator ^"(x) @ #i & Init"^ !separator ^"(x) @ #j ==> #i = #j \"\n" ^
(* 
    "restriction Equality: \" All x y #i. Eq(x,y) @ #i ==> x = y\"\n"  ^

    "restriction Inequality: \"All x #i. Neq(x,x) @ #i ==> F\"\n"  ^
 *)
    "rule Equality_gen: [] --> [!Eq"^ !separator ^"(x,x)]\n" ^

    "rule NEquality_gen: [] --[NEq_"^ !separator ^"(x,y)]-> [!NEq"^ !separator ^"(x,y)]\n" ^

    "restriction NEquality_rule: \"All x #i. NEq_"^ !separator ^"(x,x) @ #i ==> F\"\n" ^

    
    (* "lemma AlwaysStarts_"^ ! separator ^ "[sources]:\n
    \"All x #i. Loop"^ ! separator ^"Back(x) @i ==> Ex #j. Loop"^ ! separator ^"Start(x) @j & j < i\"\n"^
    
    "lemma AlwaysStartsWhenEnds_"^ ! separator ^ "[sources]:\n
    \"All x #i. Loop"^ ! separator ^"Finish(x) @i ==> Ex #j. Loop"^ ! separator ^"Start(x) @j & j < i\"\n"^ *)


    "lemma AlwaysStarts"^ ! separator ^ "[reuse,use_induction]:\n
    \"All x #i. Loop"^ ! separator ^"Back(x) @i ==> Ex #j. Loop"^ ! separator ^"Start(x) @j & j < i\"\n"^
    
    "lemma AlwaysStartsWhenEnds"^ ! separator ^ "[reuse,use_induction]:\n
    \"All x #i. Loop"^ ! separator ^"Finish(x) @i ==> Ex #j. Loop"^ ! separator ^"Start(x) @j & j < i\"\n"^

    (mult_list_with_concat (List.map (fun mo -> 
      "lemma transition"^ ! separator ^ mo.model_name ^ "[reuse,use_induction]:\n
      \"All x %i #j #k . Transition"^ ! separator ^ mo.model_name ^ "(x, %i) @#j &
       Transition"^ ! separator ^ mo.model_name ^ "(x, %i) @ #k ==> #j = #k\"\n"   
      ) (List.rev mo_lst)) "\n")^
    
    (* print lemmas *)
    List.fold_left (fun l lem -> l ^ print_lemma lem) "" lem_lst ^"\nend\n"


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
    | Syntax.MetaNewVariable (v, i) -> MetaNewVar i
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
    | Syntax.MetaNewVariable (v, i) -> MetaNewVar i, []
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


let translate_fact namespace f = 
  match f.Location.data with
  | Syntax.Fact(id, el) -> 
    let el, gv = List.fold_left (fun (el, gv) e -> let e, g = translate_expr2 e in
                                  (el @ [e], gv @ g)) ([],[]) el in    
    let gv = List.map (fun s -> mk_constant_fact s) gv in 
    Fact (id, namespace, el), gv, []

  | Syntax.GlobalFact(id, el) -> 
    let el, gv = List.fold_left (fun (el, gv) e -> let e, g = translate_expr2 e in
                                  (el @ [e], gv @ g)) ([],[]) el in    
    let gv = List.map (fun s -> mk_constant_fact s) gv in 

    GlobalFact (id, el), gv, []

  | Syntax.ChannelFact(ch, id, el) ->
    let el, gv = List.fold_left (fun (el, gv) e -> let e, g = translate_expr2 e in
                                  (el @ [e], gv @ g)) ([],[]) (el) in    
    let e, g = translate_expr2 ch in

    let gv = List.map (fun s -> mk_constant_fact s) (gv @ g) in 
    
    (* let acp = ("ACP"^ !separator ^"chan", String eng.namespace, String ch, config_persist) in  *)
    
    ChannelFact (id, e, el), gv, [e]

  | Syntax.PathFact (path, id, el) -> 
    let el, gv = List.fold_left (fun (el, gv) e -> let e, g = translate_expr2 e in
                                  (el @ [e], gv @ g)) ([],[]) (el) in    
    let e, g = translate_expr2 path in

    let gv = List.map (fun s -> mk_constant_fact s) (gv @ g) in 
    
    (* let acp = ("ACP"^ !separator "path", String eng.namespace, String ch, config_persist) in  *)

    PathFact (id, namespace, e, el), gv, [e]

  | Syntax.ResFact (0, el) -> 
    let el, gv = List.fold_left (fun (el, gv) e -> let e, g = translate_expr2 e in
                                  (el @ [e], gv @ g)) ([],[]) (el) in    
    let gv = List.map (fun s -> mk_constant_fact s) gv in 
    
    (* let acp = ("ACP"^ !separator "path", String eng.namespace, String ch, config_persist) in  *)

    ResFact (0, el), gv, []

  | Syntax.ResFact (1, el) -> 
    let el, gv = List.fold_left (fun (el, gv) e -> let e, g = translate_expr2 e in
                                  (el @ [e], gv @ g)) ([],[]) (el) in    
    let gv = List.map (fun s -> mk_constant_fact s) gv in 
    
    (* let acp = ("ACP"^ !separator "path", String eng.namespace, String ch, config_persist) in  *)

    ResFact (1, el), gv, []

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
let rec translate_cmd mo (st : state) funs syscalls attacks vars scope syscall {Location.data=c; Location.loc=loc} = 
  let return_var = get_return_var () in
  let (meta_num, loc_num, top_num) = vars in 
  
  match c with
  | Syntax.Return e ->
    let e, gv = translate_expr2 e in  
    let gv = List.map (fun s -> mk_constant_fact s) gv in 
    let (st_f : state) = next_state st scope in 
    let mo = add_state mo st_f in 
    let mo = add_transition mo {
      transition_id = List.length mo.model_transitions;
      transition_namespace = mo.model_name;
      transition_name = "return";
      transition_from = st;
      transition_to = st_f;
      transition_pre = gv;
      transition_post = [];
      transition_state_transition = mk_state_transition_from_action (ActionReturn e) vars;
      transition_label = [];
      transition_is_loop_back = false 
    } in
    (mo, st_f)


  | Syntax.Skip -> 
    let st_f = next_state st scope in 
    let mo = add_state mo st_f in 
    let mo = add_transition mo {
      transition_id = List.length mo.model_transitions;
      transition_namespace = mo.model_name;
      transition_name = "skip";
      transition_from = st;
      transition_to = st_f;
      transition_pre = [];
      transition_post = [];      
      transition_state_transition = mk_state_transition_from_action (ActionReturn Unit) vars; 
      transition_label = [];
      transition_is_loop_back = false 

    } in
    (mo, st_f)

  | Syntax.Sequence (c1, c2) -> 
    let (mo, st) = translate_cmd mo st funs syscalls attacks vars scope syscall c1 in
    let (mo, st) = translate_cmd mo st funs syscalls attacks vars None syscall c2 in
    (mo, st)

  | Syntax.Put fl -> 
    let fl, gv, acps = translate_facts mo.model_name fl in
    let acps = List.map (fun target -> AccessFact(mo.model_name, target, syscall)) acps in
    let st_f = next_state st scope in
    let mo = add_state mo st_f in
    let mo = add_transition mo {
      transition_id = List.length mo.model_transitions;
      transition_namespace = mo.model_name;
      transition_name = "put";
      transition_from = st;
      transition_to = st_f;
      transition_pre = gv @ acps;
      transition_post = fl;
      transition_state_transition = mk_state_transition_from_action (ActionReturn Unit) vars; 
      transition_label = [];
      transition_is_loop_back = false 

    } in                                            
    (mo, st_f)

  | Syntax.Let (v, e, c) -> 
    
    let e, gv = translate_expr2 e in  
    let gv = List.map (fun s -> mk_constant_fact s) gv in 
    
    let st_f = next_state ~shift:(0,1,0) st scope  in 
    let mo = add_state mo st_f in
    let mo = add_transition mo {
      transition_id = List.length mo.model_transitions;
      transition_namespace = mo.model_name;
      transition_name = "let_intro";
      transition_from = st;
      transition_to = st_f;
      transition_pre = gv;
      transition_post = [];
      transition_state_transition = mk_state_transition_from_action (ActionIntro [e]) vars; 
      transition_label = [];
      transition_is_loop_back = false 

    } in
  
    let (mo, st) = translate_cmd mo st_f funs syscalls attacks (meta_num, loc_num+1, top_num) None syscall c in

    let st_f = next_state ~shift:(0,-1,0) st scope in 
    let mo = add_state mo st_f in
    let mo = add_transition mo {
      transition_id = List.length mo.model_transitions;
      transition_namespace = mo.model_name;
      transition_name = "let_out";
      transition_from = st;
      transition_to = st_f;
      transition_pre = [];
      transition_post = [];
      transition_state_transition = mk_state_transition_from_action (ActionPopLoc 1) st.state_vars; 
      transition_label = [];
      transition_is_loop_back = false 

    } in
    (mo, st_f)

  | Syntax.Assign ((v, di), e) -> 

    let e, gv = translate_expr2 e in  
    let gv = List.map (fun s -> mk_constant_fact s) gv in 
    let st_f = next_state st scope in
    let mo = add_state mo st_f in
    let mo = add_transition mo {
      transition_id = List.length mo.model_transitions;
      transition_namespace = mo.model_name;
      transition_name = "assign";
      transition_from = st;
      transition_to = st_f;
      transition_pre = gv;
      transition_post = [];
      transition_state_transition = mk_state_transition_from_action (ActionAssign (di, e)) st.state_vars; 
      transition_label = [];
      transition_is_loop_back = false 

    } in
    (mo, st_f)

  | Syntax.FCall (ov, f, el) ->
    let el, gv = List.fold_left (fun (el, gv) e -> let e, g = translate_expr2 e in
                                  (el @ [e], gv @ g)) ([],[]) el in  
    let el = List.rev el in  
    let gv = List.map (fun s -> mk_constant_fact s) gv in 
    
    let (f, args, cmd) = List.find (fun (f', args, cmd) -> f = f') funs in 

    let st_f = next_state ~shift:(0,List.length el,0) st scope in
    let mo = add_state mo st_f in
    let mo = add_transition mo {
      transition_id = List.length mo.model_transitions;
      transition_namespace = mo.model_name;
      transition_name = "fcall_intro";
      transition_from = st;
      transition_to = st_f;
      transition_pre = gv;
      transition_post = [];
      transition_state_transition = mk_state_transition_from_action (ActionIntro el) st.state_vars; 
      transition_label = [];
      transition_is_loop_back = false 

    } in

    let (mo, st) = translate_cmd mo st_f funs syscalls attacks (meta_num, loc_num + (List.length el), top_num) None syscall cmd in

    let st_f = next_state ~shift:(0,- (List.length el),0) st scope in
    let mo = add_state mo st_f in
    let mo = add_transition mo {
      transition_id = List.length mo.model_transitions;
      transition_namespace = mo.model_name;
      transition_name = "fcall_out";
      transition_from = st;
      transition_to = st_f;
      transition_pre = [];
      transition_post = [];
      transition_state_transition = mk_state_transition_from_action (match ov with
      | None -> ActionPopLoc (List.length el)
      | Some (_, v) -> ActionSeq (ActionPopLoc (List.length el), ActionAssign (v, return_var))
      ) st.state_vars; 
      transition_label = [];
      transition_is_loop_back = false 

    } in
    (mo, st_f)      

  | Syntax.SCall (ov, o, el) ->
    let el, gv = List.fold_left (fun (el, gv) e -> let e, g = translate_expr2 e in
                                  (el @ [e], gv @ g)) ([],[]) el in    
    let el = List.rev el in 
    let gv = List.map (fun s -> mk_constant_fact s) gv in 
    
    let (f, args, cmd) = List.find (fun (f', args, cmd) -> o = f') syscalls in 

    let st_i = next_state ~shift:(0,List.length el,0) st (Some [0]) in
    
    let mo = add_state mo st_i in
    let mo = add_transition mo {
      transition_id = List.length mo.model_transitions;
      transition_namespace = mo.model_name;
      transition_name = "scall_intro";
      transition_from = st;
      transition_to = st_i;
      transition_pre = gv;
      transition_post = [];
      transition_state_transition = mk_state_transition_from_action (ActionIntro el) st.state_vars; 
      transition_label = [];
      transition_is_loop_back = false 

    } in

    let (mo, st_m) = translate_cmd mo st_i funs syscalls attacks (meta_num, loc_num + (List.length el), top_num) None o cmd in

    let st_f = next_state st None in
    let mo = add_state mo st_f in
    let mo = add_transition mo {
      transition_id = List.length mo.model_transitions;
      transition_namespace = mo.model_name;
      transition_name = "scall_out";
      transition_from = st_m;
      transition_to = st_f;
      transition_pre = [];
      transition_post = [];
      transition_state_transition = mk_state_transition_from_action (match ov with
      | None -> ActionPopLoc (List.length el)
      | Some (_, v) -> ActionSeq (ActionPopLoc (List.length el), ActionAssign (v, return_var))
      ) st_m.state_vars; 
      transition_label = [];
      transition_is_loop_back = false 

    } in

    (* if this system call is attacked *)
    begin match List.find_all (fun (a, t, _,cmd) -> t = o) attacks with
    | [] ->  (mo, st_f)
    | lst -> 
      let scope_lst = List.map (fun i -> Some [i+1]) (List.init (List.length lst) (fun i -> i)) in 
      let mo = List.fold_left2 (fun mo scope (a,_, _, c) -> 
        let st_i2 = next_state ~shift:(0,List.length el,0) st scope in
        let mo = add_state mo st_i2 in  
        let mo = add_transition mo {
          transition_id = List.length mo.model_transitions;
          transition_namespace = mo.model_name;
          transition_name = "attack_intro";
          transition_from = st;
          transition_to = st_i2;
          transition_pre = AttackFact (mo.model_name, String a) :: gv;
          transition_post = [];
          transition_state_transition = mk_state_transition_from_action (ActionIntro el) st.state_vars; 
          transition_label = [];
          transition_is_loop_back = false 
        } in
        let (mo, st_m) = translate_cmd mo st_i2 funs syscalls attacks (meta_num, loc_num + (List.length el), top_num) None o c in
        add_transition mo {
          transition_id = List.length mo.model_transitions;
          transition_namespace = mo.model_name;
          transition_name = "attack_out";
          transition_from = st_m;
          transition_to = st_f;
          transition_pre = [];
          transition_post = [];
          transition_state_transition = mk_state_transition_from_action (match ov with
          | None -> ActionPopLoc (List.length el)
          | Some (_, v) -> ActionSeq (ActionPopLoc (List.length el), ActionAssign (v, return_var))
          ) st_m.state_vars; 
          transition_label = [];
          transition_is_loop_back = false   
        }) mo scope_lst lst in
        (mo, st_f)
      end 
  
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
      let (mo, st) = translate_guarded_cmd mo st funs syscalls attacks vars scope syscall (vl, fl, c) in
      add_transition mo {
        transition_id = List.length mo.model_transitions;
        transition_namespace = mo.model_name;
        transition_name = "case_out";
        transition_from = st;
        transition_to = st_f;
        transition_pre = [];
        transition_post = [];
        transition_state_transition = mk_state_transition_from_action (ActionPopMeta (List.length vl)) st.state_vars; 
        transition_label = [];
        transition_is_loop_back = false   
      }) mo scope_lst cs in

    (add_state mo st_f, st_f)

 | Syntax.While (cs1, cs2) ->

    let st_i = next_state st scope in
    let tid = List.length mo.model_transitions in 
    let mo = add_transition mo {
      transition_id = tid;
      transition_namespace = mo.model_name;
      transition_name = "repeat_in";
      transition_from = st;
      transition_to = st_i;
      transition_pre = [];
      transition_post = [];
      transition_state_transition = mk_state_transition_from_action (ActionReturn Unit) st.state_vars; 
      transition_label = [
        (LoopFact (mo.model_name, tid, 0))
      ];
      transition_is_loop_back = false   
    } in
    let st = st_i in 

    let scope_lst1 =
        List.map (fun i -> Some [i]) (List.init (List.length cs1) (fun i -> i)) in 
    let scope_lst2 =
        List.map (fun i -> Some [i]) (List.init (List.length cs2) (fun i -> i + (List.length cs1))) in 
  
    let st_f = next_state st None in

    let mo = List.fold_left2 (fun mo scope (vl, fl, c) -> 
      let (mo, st_f) = translate_guarded_cmd mo st funs syscalls attacks vars scope syscall (vl, fl, c) in
      add_transition mo {
        transition_id = List.length mo.model_transitions;
        transition_namespace = mo.model_name;
        transition_name = "repeat";
        transition_from = st_f;
        transition_to = st;
        transition_pre = [];
        transition_post = [];
        transition_state_transition = mk_state_transition_from_action (ActionPopMeta (List.length vl)) st_f.state_vars; 
        transition_label = [
          (LoopFact (mo.model_name, tid, 1))
        ];
        transition_is_loop_back = true   
      }) mo scope_lst1 cs1 in

    let mo = List.fold_left2 (fun mo scope (vl, fl, c) -> 
      let (mo, st) = translate_guarded_cmd mo st funs syscalls attacks vars scope syscall (vl, fl, c) in
      add_transition mo {
        transition_id = List.length mo.model_transitions;
        transition_namespace = mo.model_name;
        transition_name = "repeat_out";
        transition_from = st;
        transition_to = st_f;
        transition_pre = [];
        transition_post = [];
        transition_state_transition = mk_state_transition_from_action (ActionPopMeta (List.length vl)) st.state_vars; 
        transition_label = [          
          (LoopFact (mo.model_name, tid, 2))
        ];
        transition_is_loop_back = false   
      }) mo scope_lst2 cs2 in
    
    (add_state mo st_f, st_f)

 | Syntax.Event (fl) ->
    let fl, gv, acps = translate_facts mo.model_name fl in 
    let st_f = next_state st scope in
    let mo = add_state mo st_f in
    let mo = add_transition mo {
      transition_id = List.length mo.model_transitions;
      transition_namespace = mo.model_name;
      transition_name = "event";
      transition_from = st;
      transition_to = st_f;
      transition_pre = gv;
      transition_post = [];
      transition_state_transition = mk_state_transition_from_action (ActionReturn Unit) st.state_vars; 
      transition_label = fl;
      transition_is_loop_back = false 
    } in
  (mo, st_f)

  (* | New of Name.ident * Name.ident * expr list * cmd 
  | Get of Name.ident list * expr * Name.ident * cmd
  | Del of expr * Name.ident *)

| Syntax.New (v, fid, el, c) ->
  let el, gv = List.fold_left (fun (el, gv) e -> let e, g = translate_expr2 e in
    (el @ [e], gv @ g)) ([],[]) el in    
  let gv = List.map (fun s -> mk_constant_fact s) gv in 

  (* | InjectiveFact of 
    string * (* fact name *)
    string * (* namespace *)
    expr list (* arguments *)
  | FreshFact of expr *)

  let st_f = next_state ~shift:(1,0,0) st scope  in 
  let mo = add_state mo st_f in
  let mo = add_transition mo {
    transition_id = List.length mo.model_transitions;
    transition_namespace = mo.model_name;
    transition_name = "new_intro";
    transition_from = st;
    transition_to = st_f;
    transition_pre = (FreshFact (MetaNewVar 0))::gv;
    transition_post = (if fid = "" then [] else [InjectiveFact (fid, mo.model_name, (MetaNewVar 0), List el)]);
    transition_state_transition = mk_state_transition_from_action (ActionAddMeta 1) vars; 
    transition_label = [];
    transition_is_loop_back = false 
  } in

  let (mo, st) = translate_cmd mo st_f funs syscalls attacks (meta_num+1, loc_num, top_num) None syscall c in

  let st_f = next_state ~shift:(-1,0,0) st scope in 
  let mo = add_state mo st_f in
  let mo = add_transition mo {
    transition_id = List.length mo.model_transitions;
    transition_namespace = mo.model_name;
    transition_name = "new_out";
    transition_from = st;
    transition_to = st_f;
    transition_pre = [];
    transition_post = [];
    transition_state_transition = mk_state_transition_from_action (ActionPopMeta 1) st.state_vars; 
    transition_label = [];
    transition_is_loop_back = false 
  } in
  (mo, st_f)



  | Syntax.Get (vl, id, fid, c) ->
    let e, g = translate_expr2 id in
    let g = List.map (fun s -> mk_constant_fact s) g in 

  (* | InjectiveFact of 
    string * (* fact name *)
    string * (* namespace *)
    expr list (* arguments *)
  | FreshFact of expr *)

  let st_f = next_state ~shift:(List.length vl,0,0) st scope  in 
  let mo = add_state mo st_f in
  let mo = add_transition mo {
    transition_id = List.length mo.model_transitions;
    transition_namespace = mo.model_name;
    transition_name = "get_intro";
    transition_from = st;
    transition_to = st_f;
    transition_pre = [InjectiveFact (fid, mo.model_name, e, List (List.map (fun i -> MetaNewVar i) (int_to_list (List.length vl))))] @ g;
    transition_post = [InjectiveFact (fid, mo.model_name, e, List (List.map (fun i -> MetaNewVar i) (int_to_list (List.length vl))))];
    transition_state_transition = mk_state_transition_from_action (ActionAddMeta (List.length vl)) vars; 
    transition_label = [];
    transition_is_loop_back = false 
  } in

  let (mo, st) = translate_cmd mo st_f funs syscalls attacks (meta_num + (List.length vl), loc_num, top_num) None syscall c in

  let st_f = next_state ~shift:(-(List.length vl),0,0) st scope in 
  let mo = add_state mo st_f in
  let mo = add_transition mo {
    transition_id = List.length mo.model_transitions;
    transition_namespace = mo.model_name;
    transition_name = "get_out";
    transition_from = st;
    transition_to = st_f;
    transition_pre = [];
    transition_post = [];
    transition_state_transition = mk_state_transition_from_action (ActionPopMeta (List.length vl)) st.state_vars; 
    transition_label = [];
    transition_is_loop_back = false 
  } in
  (mo, st_f)

  | Syntax.Del (id, fid) ->    
    let e, g = translate_expr2 id in
    let g = List.map (fun s -> mk_constant_fact s) g in 
    let st_f = next_state st scope  in 
    let mo = add_state mo st_f in
    let mo = add_transition mo {
      transition_id = List.length mo.model_transitions;
      transition_namespace = mo.model_name;
      transition_name = "del";
      transition_from = st;
      transition_to = st_f;
      transition_pre = [InjectiveFact (fid, mo.model_name, e, (MetaNewVar 0)) ] @g;
      transition_post = [];
      transition_state_transition = mk_state_transition_from_action (ActionReturn Unit) vars; 
      transition_label = [];
      transition_is_loop_back = false 
    } in
    (mo, st_f)
  


and translate_guarded_cmd mo st funs syscalls attacks vars scope syscall (vl, fl, c) = 
  let (meta_num, loc_num, top_num) = vars in 

  let fl, gv, acps = translate_facts mo.model_name fl in
  let acps = List.map (fun target -> AccessFact(mo.model_name,target,syscall)) acps in
  let st_f = next_state ~shift:(List.length vl, 0, 0) st scope in
  let mo = add_state mo st_f in
  (* let eng_f = engine_index_inc eng scope in *)
  let mo = add_transition mo {
    transition_id = List.length mo.model_transitions;
    transition_namespace = mo.model_name;
    transition_name = "guarded";
    transition_from = st;
    transition_to = st_f;
    transition_pre = fl @ gv @ acps;
    transition_post = [];
    transition_state_transition = mk_state_transition_from_action (ActionAddMeta (List.length vl)) st.state_vars;
    transition_label = [];
    transition_is_loop_back = false 

  } in
  let (mo, st_f) = translate_cmd mo st_f funs syscalls attacks (meta_num + List.length vl, loc_num, top_num) None syscall c in
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
      } syscalls attacks =
  let namespace = String.capitalize_ascii (s ^ (if k = 0 then "" else string_of_int k)) in (* this must be unique *)
  (* let t = add_comment t ("- Process name: " ^ namespace) in  *)

  let mo, st = initial_model namespace in 

  (* initialize file system *)
  let mo = List.fold_left (fun mo (path, e, _, _) ->
      (* let path = (mk_dir eng fsys path) in *)
      let e, gv = translate_expr2 e in  
      let gv = List.map (fun s -> mk_constant_fact s) gv in 
      let name = mk_fact_name  namespace^ replace_string '/' !separator path in 
      add_rule mo (name, "",
            gv,
            [InitFact([List [String namespace; String path]])],
            [FileFact(namespace, path, e)])) mo fls in 
     
  (* initialize rule *)
  (* let mo = add_rule mo (name, "",
  [],
  [InitFact([String namespace; String path])],
  [FileFact(namespace, path, e)]) in *)



  (* initialize memory *)
  let (mo, st) = List.fold_left
		   (fun (mo, st) (x, e) -> 
          let st_f = next_state ~shift:(0,0,1) st None in 
          let mo = add_state mo st_f in
          let e, gv = translate_expr2 e in  
          let gv = List.map (fun s -> mk_constant_fact s) gv in 
          let mo = add_transition mo {
            transition_id = List.length mo.model_transitions;
            transition_namespace = mo.model_name;
            transition_name = "init_mem";
            transition_from = st;
            transition_to = st_f;
            transition_pre = gv;
            transition_post = [];
            transition_state_transition = mk_state_transition_from_action (ActionLetTop [e]) st.state_vars;
            transition_label = [];
            transition_is_loop_back = false 
      
          } in
          (mo, st_f)) (mo, st) (List.rev vars) in 


  (* translate the main function *)
  let (mo, st) = translate_cmd mo st fns syscalls attacks (0, 0, List.length vars) None "" m in
  
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

  (* let t = tamarin_add_comment t "Attacks:" in
  let t = List.fold_left (fun t (f, (ty, var), cmd) -> 
    
    let namespace = String.capitalize_ascii f in (* this must be unique *)
    (* let t = add_comment t ("- Process name: " ^ namespace) in  *)
    let mo, st = initial_attacker_model namespace in 
    let (mo, st) = translate_cmd mo st [] [] (1, 0, 0) None "" cmd in
    add_model t mo) t (List.rev def.Context.def_ext_attack) in *)

  (* load global variables *)

  (* let t = add_comment t "Global constants:" in *)

  (* global constants *)
  let t = tamarin_add_comment t "Global Constants:" in

  let t = List.fold_left (fun t (v, e) -> 
	      match e with
	      | None -> (* when v is fresh *) 
          tamarin_add_rule t 
          ("Const"^sep^v, "", [ResFact(2, [Var v])], [InitFact [String ("Const"^sep^v)]; InitFact [List [String ("Const"^sep^v); Var v]]], [mk_constant_fact v])
	      | Some e -> (* when v is defined *) 
          let e, gv = translate_expr2 e in  
          let gv = List.map (fun s -> mk_constant_fact s) gv in 
      		tamarin_add_rule t ("Const"^sep^v, "", gv, [], [ConstantFact(Var v, e)])) t (List.rev def.Context.def_const) in

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

		  let t, il = 
        List.fold_left (fun (t, il) (c, ty) -> 
          match List.find_all (fun (a, b, sys) -> a = p.Context.proc_type && List.exists (fun b -> b = ty) b) pol.Context.pol_access with
          | [] -> (t, il) 
          | scall -> 
            List.fold_left (fun (t, il) (_, _, sys) ->
				      let name = procname ^ sep ^ c ^ sep ^ sys in 
					      tamarin_add_rule t 
                  (name, "",
                    [], 
                    [], 
                    [AccessFact(procname, String c, sys)]), name::il) (t, il) scall) (t, il) ctx.Context.ctx_ch in 

      let t, il = List.fold_left (fun (t, il) (c, ty) -> 
                match List.find_all (fun (a, b) -> a = p.Context.proc_type && List.exists (fun b -> b = ty) b) pol.Context.pol_access_all with
                | [] -> (t, il) 
                | _ -> 
                 let name = procname ^ sep ^ c ^ sep in 
                 tamarin_add_rule t 
                  (name, "",
                  [], 
                  [], 
                  [AccessFact(procname, String c, "")]), name::il) (t, il) ctx.Context.ctx_ch in 

      let t = List.fold_left (fun (t : tamarin) (pty, att) -> 
        if p.Context.proc_type = pty 
        then
          let name = procname ^ sep ^ sep ^ att in 
          tamarin_add_rule t (name, "",
          [], 
          [], 
          [AttackFact(procname, String att)]) 
        else t) t pol.Context.pol_attack in


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
          [], 
          [AccessFact(procname, String path, sys)])
             , name::il) (t, il) scall
              ) (t, il) ctx.Context.ctx_fsys in 

		  (t, il)) (t, il) proc in
  

  (* initialize attacks on channels!!! *)
  (* let t = tamarin_add_comment t "Attacker policy:" in

     let t = List.fold_left (fun t (c, ty) -> 
      match Context.pol_get_attack_opt pol ty with 
      | Some attk -> 
        let t = tamarin_add_rule t (mk_fact_name c ^  !separator  ^ attk, "", [], [], [AttackFact(mk_fact_name attk, String c)]) in 
        tamarin_add_rule t (mk_fact_name c ^  !separator  ^ attk ^ !separator, "", [], [], [AccessFact(mk_fact_name attk, String c, "")])
     | None -> t) t ctx.Context.ctx_pr in 
      *)
  

  (* let t = add_comment t "Processes:" in *)
  let t = List.fold_left (fun t p -> add_model t (translate_process p def.Context.def_ext_syscall def.Context.def_ext_attack)) t (List.rev proc) in

  (* translating lemmas now *)
  let t = List.fold_left (fun t l ->
    let l =
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
    in tamarin_add_lemma t l) t lem in
  t

