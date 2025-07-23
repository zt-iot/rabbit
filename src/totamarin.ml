(* For translating to and printing Tamarin models.
   * 'Rabbit' is a string value palceholder for void output of system calls and functions.
   * GlobalFact is fact that does not bound to any process or channel. Currently 
   it only contains reserved facts.
 *)
let separator = ref "_"
let fresh_ident = ref "rab"
let fresh_string = ref "rab"

let fresh_param = ref "param"


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


type mindex =  ((int list) * int) list

(* we do not do well-formedness check (at the moment..) *)
type functions = (string * int) list 

type expr = 
  | FVar of expr
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
  | Param 

let rec expr_collect_vars e =
  match e with
  | FVar e -> [FVar e ]
  | Var s -> [Var s]
  | MetaVar i -> [MetaVar i]
  | LocVar i -> [LocVar i]
  | TopVar i -> [TopVar i]
  | MetaNewVar i -> [MetaNewVar i]
  | Apply(s, el) -> List.fold_left (fun vl e -> (expr_collect_vars e) @ vl) [] el 
  | String _ -> []
  | Integer _ -> []
  | List el -> List.fold_left (fun vl e -> (expr_collect_vars e) @ vl) [] el
  | One -> []
  | Int _ -> []
  | AddOne e -> expr_collect_vars e
  | Unit -> []
  | Param -> [Param]



let expr_pair a b = List [a ; b]

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
  | AccessFact of string * expr * expr * string 
  | AttackFact of string * expr 
  | FileFact of string  * expr * expr
  | InitFact of expr list 
  | LoopFact of 
    string (* namespace *)
    * mindex (* the index when the loop is entered  *)
    * int (* 0: loop in 2 : loop back 3 : loop out *)
  | TransitionFact of string * string * expr * expr
  | InjectiveFact of 
    string * (* fact name *)
    string * (* namespace *)
    expr * (* identity *)
    expr (* arguments *)
  | FreshFact of expr
  | AccessGenFact of string (* namespace *) * expr (* param *)
  
let global_fact_collect_vars f =
  match f with
  | GlobalFact (s, el) -> 
    List.fold_left (fun vl v -> 
      if List.exists (fun w -> w = v) vl then vl else v::vl
      ) []
        (List.fold_left (fun vl e -> (expr_collect_vars e) @ vl) [] el)
  | ConstantFact (e1, e2) -> expr_collect_vars e1 @expr_collect_vars e2

  | _ -> error ~loc:Location.Nowhere (UnintendedError "process fact")

type fact' = string * expr list * rule_config

let print_fact' (f : fact) : fact' = 
  match f with
  | Fact (fid, nsp, el) -> (mk_my_fact_name fid ^ ! separator ^ nsp, Param::el, config_linear)
  | ConstantFact (e1, e2) -> ("Const"^ !separator , [e1 ; e2], config_persist) 
  | GlobalFact (fid, el) -> (mk_my_fact_name fid, el, config_linear)
  | ChannelFact (fid, ch, el) -> (mk_my_fact_name fid, ch :: el, config_linear)
  (* | PathFact (fid, nsp, path, el) -> (mk_my_fact_name fid ^ ! separator ^ nsp,path :: el, config_linear) *)
  | ResFact (0, el) -> ("Eq"^ !separator , el, config_linear) (* linear because we will move this to tag and it wont be used as facts*)
  | ResFact (1, el) -> ("NEq"^ !separator , el, config_linear) (* linear because we will move this to tag and it wont be used as facts*)
  | ResFact (2, el) -> ("Fr", el, config_linear)
  | AccessFact (nsp, param, target, syscall) -> ("ACP"^ !separator, [List [String nsp; param]; target; String syscall], config_persist )
  | AttackFact (attack, target) ->  ("Attack"^ !separator, [String attack; target], config_persist )
  | FileFact (nsp, path, e) -> ("File"^ !separator ^ nsp, [Param;path; e], config_linear)
  | InitFact el -> ("Init"^ !separator, el, config_linear)
  | LoopFact (nsp, tid, b) -> ("Loop" ^ ! separator ^ 
    (if b =0 then "Start" else if b = 1 then "Back" else "Finish"), 
    [List [String nsp; Param]; String (index_to_string tid)], 
    config_linear)
  | TransitionFact (nsp, ind, e, p) -> ("Transition"^ !separator, [List [String nsp; p]; String ind; e], config_linear)
  | InjectiveFact (fid, nsp, id, el) -> (mk_my_fact_name fid ^ ! separator ^ nsp, [Param; FVar id ; el], config_linear)
  | FreshFact (e) -> ("Fr", [FVar e], config_linear)
  | AccessGenFact (nsp, param) -> ("ACP"^ !separator ^ "GEN"^ !separator, [String nsp; param], config_persist)
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
  | FVar e -> 
    (* "~"^ *)
  print_expr e
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
  | Param -> !fresh_param
  
let mk_state ?(param="") st (ret, meta, loc, top) : fact' = 
  (* (let (a,b,c) = st.state_vars in
    if not (List.length meta = a ) || not (List.length loc = b ) || not (List.length top = c ) then
      print_endline (print_expr (state_index_to_string st))
    else ()); *)
  (get_state_fact_name st 
  (* ^ (let (a,b,c) = st.state_vars in "_" ^(string_of_int a)^"_" ^(string_of_int b)^"_" ^(string_of_int c)) *)
  , 
  [List [state_index_to_string st; if param = "" then Param else String param]; ret; List meta; List loc; List top], config_linear) 
      

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
  model_transition_id_max : int;
  model_type : string; 
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

let mk_state_transition ?(param="") st (ret, meta, loc, top) is_initial is_loop : fact' = 
  (get_state_fact_name st, 
  [List [state_index_to_string st; 
    if param = "" then Param else String param;
    if is_loop then 
      AddOne (Int ("v"^ !separator)) else 
    if is_initial then One else
        Int ("v"^ !separator)]; ret; List meta; List loc; List top], config_linear) 


let initial_model name ty = 
  let st = initial_state name in
  {model_name = name; model_states = [st]; model_transitions = []; model_type = ty;
  model_init_rules = []; 
  model_init_state = st; model_transition_id_max =0}, st

let initial_state name = 
{
  state_namespace = name;
  state_index = [([],0)];
  state_vars = (1, 0, 0)
}
  
let initial_attacker_model name ty = 
  let st = initial_state name in
  {model_name = name; model_states = [st]; model_transitions = []; model_type = ty;
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
  | ReachabilityLemma of string * string list * string list * string list * fact list * fact list
  | CorrespondenceLemma of string * string list * (fact list * fact) * (fact list * fact)

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

let tamarin_add_rule' (t : tamarin) (a, b, c, d, e) = 
  let (si, mo, rules, lemmas) = t in 
    (si, mo, (Rule (a, b, c,d,e)) :: rules, lemmas)

    

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
  let label = TransitionFact(tr.transition_namespace, 
  index_to_string (tr.transition_from.state_index)
  (* tr.transition_id *)
  , Int ("v"^ !separator), Param) :: tr.transition_label in
  let initial_state_fact = mk_state_transition tr.transition_from (fst tr.transition_state_transition) false false in 
  let final_state_fact = mk_state_transition tr.transition_to (snd tr.transition_state_transition) false tr.transition_is_loop_back in 
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
  | ReachabilityLemma (l, cs, ps, vars,gv, facts) ->
    let var1 = List.flatten (List.map global_fact_collect_vars facts) in
    let var2 = List.flatten (List.map global_fact_collect_vars gv) in
    let var = List.fold_left (fun var v -> 
      (* print_string (print_expr v);
      print_string "  "; *)
      if List.exists (fun w -> w = v) var then var else v::var) [] (var1@var2) in 
    
    "\nlemma "^l^ " : exists-trace \"Ex "^

    (mult_list_with_concat (List.map print_expr var) " ") ^
    (mult_list_with_concat (fst (List.fold_left (fun (times, n) _ -> (" #time" ^ !separator ^ string_of_int n) :: times, n+1) ([],0) facts)) " ") ^ 
    (mult_list_with_concat (fst (List.fold_left (fun (times, n) _ -> (" #label_time" ^ !separator ^ string_of_int n) :: times, n+1) ([],0) gv)) " ") ^ 
    " . " ^
    (mult_list_with_concat (fst (List.fold_left (fun (s, n) g -> ((print_fact (print_fact' g)) ^"@#label_time"^ !separator ^ string_of_int n)::s , n+1) ([],0) gv)) " & ") ^
    (if List.length gv = 0 then "" else " & ") ^
    (mult_list_with_concat (fst (List.fold_left (fun (s, n) g -> ((print_fact (print_fact' g)) ^"@#time"^ !separator ^ string_of_int n)::s , n+1) ([],0) facts)) " & ") ^
   " \""



  | CorrespondenceLemma (l, vl, (gva, a), (gvb, b)) -> 
    let var1 = List.flatten (List.map global_fact_collect_vars [a]) in
    let var2 = List.flatten (List.map global_fact_collect_vars gva) in
    let vara = List.fold_left (fun var v -> 
      if List.exists (fun w -> w = v) var then var else v::var) [] (var1@var2) in 

    let var1 = List.flatten (List.map global_fact_collect_vars [b]) in
    let var2 = List.flatten (List.map global_fact_collect_vars gvb) in
    let varb = List.fold_left (fun var v -> 
      if List.exists (fun w -> w = v) (var@vara) then var else v::var) [] (var1@var2) in 
      
    
    
    
    "\nlemma "^l^ " : all-traces \"All "^

    (mult_list_with_concat (List.map print_expr vara) " ") ^
    (mult_list_with_concat (fst (List.fold_left (fun (times, n) _ -> (" #label_time" ^ !separator ^ string_of_int n) :: times, n+1) ([],0) gva)) " ") ^ 
    " #time" ^ !separator ^ "1 . " ^
    (mult_list_with_concat (fst (List.fold_left (fun (s, n) g -> ((print_fact (print_fact' g)) ^"@#label_time"^ !separator ^ string_of_int n)::s , n+1) ([],0) gva)) " & ") ^
    (if List.length gva = 0 then "" else " & ") ^
    (print_fact (print_fact' a)) ^"@#time" ^ !separator ^ "1 ==> Ex "^
    (mult_list_with_concat (List.map print_expr varb) " ") ^
    (mult_list_with_concat (fst (List.fold_left (fun (times, n) _ -> (" #label__time" ^ !separator ^ string_of_int n) :: times, n+1) ([],0) gvb)) " ") ^ 
    
    " #time" ^ !separator ^ "2 . " ^
    (mult_list_with_concat (fst (List.fold_left (fun (s, n) g -> ((print_fact (print_fact' g)) ^"@#label__time"^ !separator ^ string_of_int n)::s , n+1) ([],0) gvb)) " & ") ^
    (if List.length gvb = 0 then "" else " & ") ^
    (print_fact (print_fact' b)) ^"@#time" ^ !separator ^ "2 & #time" ^ !separator ^"2 < #time" ^ !separator ^"1 \""


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


    "restriction Equality_rule: \"All x y #i. Eq"^ !separator ^"(x,y) @ #i ==> x = y\"\n" ^
    "restriction NEquality_rule: \"All x #i. NEq"^ !separator ^"(x,x) @ #i ==> F\"\n" ^

    (if !Config.tag_transition then
      begin 
      "lemma AlwaysStarts"^ ! separator ^ "[reuse,use_induction]:\n
      \"All x p #i. Loop"^ ! separator ^"Back(x, p) @i ==> Ex #j. Loop"^ ! separator ^"Start(x, p) @j & j < i\"\n"^
      
      "lemma AlwaysStartsWhenEnds"^ ! separator ^ "[reuse,use_induction]:\n
      \"All x p #i. Loop"^ ! separator ^"Finish(x, p) @i ==> Ex #j. Loop"^ ! separator ^"Start(x, p) @j & j < i\"\n"^

      "lemma TransitionOnce"^ ! separator ^ "[reuse,use_induction]:\n
      \"All x p %i #j #k . Transition"^ ! separator ^ "(x, p, %i) @#j &
        Transition"^ ! separator  ^"(x, p, %i) @ #k ==> #j = #k\"\n"   


      (* (mult_list_with_concat (List.map (fun mo -> 
        "lemma transition"^ ! separator ^ mo.model_name ^ "[reuse,use_induction]:\n
        \"All x p %i #j #k . Transition"^ ! separator ^ mo.model_name ^ "(x, %i, p) @#j &
        Transition"^ ! separator ^ mo.model_name ^ "(x, %i, p) @ #k ==> #j = #k\"\n"   
        ) (List.rev mo_lst)) "\n") *)

      end
    else "") ^
    
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
    | Syntax.ParamChan (cid, e) -> expr_pair (String (cid)) (translate_expr ~ch:ch e)
    | Syntax.ParamConst (cid, e) -> error ~loc (UnintendedError ("translating constant " ^ cid))
    | Syntax.Param _ -> Param
  in translate_expr' e

  (* ConstantFact (String s, Var s) *)
let rec translate_expr2 ?(ch=false) ?(num=0) {Location.data=e; Location.loc=loc} = 
  let translate_expr2' = function
    | Syntax.ExtConst s -> Apply (s, []), [], num
    | Syntax.Const s -> Var s, [ConstantFact (String s, Var s)], num
    | Syntax.TopVariable (v, i) -> TopVar i, [], num
    | Syntax.LocVariable (v, i) -> LocVar i, [], num
    | Syntax.MetaVariable (v, i) -> MetaVar i, [], num
    | Syntax.MetaNewVariable (v, i) -> MetaNewVar i, [], num
    | Syntax.Boolean b -> error ~loc (UnintendedError "translating boolean")
    | Syntax.String s -> String s, [], num
    | Syntax.Integer z -> Integer z, [], num
    | Syntax.Float f -> error ~loc (UnintendedError "translating float")
    | Syntax.Apply (o, el) -> 
       let (el, sl, n) = List.fold_left (fun (el, sl, n) e -> 
			  let e, s, n = translate_expr2 ~ch:ch ~num:n e in 
			  (el @ [e], sl @ s, n)) ([], [], num) el in 
       Apply (o, el), sl, n
    | Syntax.Tuple el -> 
       let (el, sl, n) = List.fold_left (fun (el, sl, n) e -> 
			  let e, s, n = translate_expr2 ~ch:ch ~num:n e in 
			  (el @ [e], sl @ s, n)) ([], [], num) el in 
       List el, sl, n
    | Syntax.Channel (c, l) -> if ch then Var c, [], num else String c, [], num
    | Syntax.Process v -> Var v, [], num
    | Syntax.Path v -> Var v, [], num
    | Syntax.ParamChan (cid, e) -> 
      let e', l, n = (translate_expr2 ~ch:ch ~num:num e) in 
      (* let var_name = (cid ^ !separator ^ string_of_int num) in *)
      expr_pair (String (cid)) e', l, n
    | Syntax.ParamConst (cid, e) -> 
      let e', l, n = (translate_expr2 ~ch:ch ~num:(num+1) e) in 
      let var_name = (cid ^ !separator ^ string_of_int num) in
      Var var_name, (ConstantFact (expr_pair (String cid) e', Var var_name))::l, n
    | Syntax.Param _ -> Param, [], num

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


let translate_fact ?(num=0) namespace f = 
  match f.Location.data with
  | Syntax.Fact(id, el) -> 
    let el, gv, n = List.fold_left (fun (el, gv, n) e -> let e, g, n = translate_expr2 ~num:n e in
                                  (el @ [e], gv @ g, n)) ([],[], num) el in    
    Fact (id, namespace, el), gv, [], n

  | Syntax.GlobalFact(id, el) -> 
    let el, gv, n = List.fold_left (fun (el, gv, n) e -> let e, g, n = translate_expr2 ~num:n e in
                                  (el @ [e], gv @ g, n)) ([],[], num) el in    
    GlobalFact (id, el), gv, [], n

  | Syntax.ChannelFact(ch, id, el) ->
    let el, gv, n = List.fold_left (fun (el, gv, n) e -> let e, g, n = translate_expr2 ~num:n e in
                                  (el @ [e], gv @ g, n)) ([],[], num) el in    
    let e, g, n = translate_expr2 ~num:n ch in
        
    ChannelFact (id, e, el), gv@g, [e], n

  | Syntax.ResFact (0, el) -> 
    let el, gv, n = List.fold_left (fun (el, gv, n) e -> let e, g, n = translate_expr2 ~num:n e in
                                  (el @ [e], gv @ g, n)) ([],[], num) el in    

    ResFact (0, el), gv, [], n

  | Syntax.ResFact (1, el) -> 
    let el, gv, n = List.fold_left (fun (el, gv, n) e -> let e, g, n = translate_expr2 ~num:n e in
                                  (el @ [e], gv @ g, n)) ([],[], num) el in    

    ResFact (1, el), gv, [], n

  | Syntax.ResFact (3, [p; d]) -> 
    let p, g1, n = translate_expr2 ~num:num p in
    let d, g2, n = translate_expr2 ~num:n d in
    
    FileFact (namespace, p, d), g1@g2, [p], n
  

  | _ -> 
    error ~loc:Location.Nowhere (UnintendedError "process fact")

let translate_facts ?(num=0) namespace fl =
  List.fold_left (fun (fl, gv, acps, n) f -> 
              let (f, gv', acps', n) = translate_fact ~num:n namespace f in 
              (fl @ [f], gv@gv', acps@acps', n)) ([],[],[], num) fl

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

  (* | Syntax.PathFact (path, id, el) -> 
    Syntax.PathFact(expr_shift_meta shift path, id, (List.map (expr_shift_meta shift) el)) *)
  
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
let rec translate_cmd mo (st : state) funs syscalls attacks vars scope syscall pol {Location.data=c; Location.loc=loc} = 
  let return_var = get_return_var () in
  let (meta_num, loc_num, top_num) = vars in 
  
  match c with
  | Syntax.Return e ->
    let e, gv, _ = translate_expr2 e in  
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
    let (mo, st) = translate_cmd mo st funs syscalls attacks vars scope syscall pol  c1 in
    let (mo, st) = translate_cmd mo st funs syscalls attacks vars None syscall pol  c2 in
    (mo, st)

  | Syntax.Put fl -> 
    let fl, gv, acps, _ = translate_facts mo.model_name fl in
    let acps = List.map (fun target -> AccessFact(mo.model_name, Param, target, syscall)) acps in
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
    
    let e, gv, _ = translate_expr2 e in  
    
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
  
    let (mo, st) = translate_cmd mo st_f funs syscalls attacks (meta_num, loc_num+1, top_num) None syscall pol c in

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

    let e, gv, _ = translate_expr2 e in  
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
    let el, gv, _ = List.fold_left (fun (el, gv, n) e -> let e, g, n = translate_expr2 ~num:n e in
                                  (el @ [e], gv @ g, n)) ([],[], 0) el in  
    let el = List.rev el in  
    
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

    let (mo, st) = translate_cmd mo st_f funs syscalls attacks (meta_num, loc_num + (List.length el), top_num) None syscall pol cmd in

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
    let el, gv, _ = List.fold_left (fun (el, gv, n) e -> let e, g, n = translate_expr2 ~num:n e in
                                  (el @ [e], gv @ g, n)) ([],[], 0) el in  
    let el = List.rev el in 
    
    let (f, args, cmd) = List.find (fun (f', args, cmd) -> o = f') syscalls in 

    (* node for exiting system *)
    let st_f = next_state st None in
    let mo = add_state mo st_f in
    
    (* add attacks in paralell *)
    (* if this system call is attacked *)
    let mo = 
    begin match List.find_all (fun (a, t, _,cmd) -> t = o && List.exists (fun (s1,s2) -> s1 = mo.model_type && s2 = a) pol.Context.pol_attack) attacks with
    | [] ->  mo
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
          transition_pre =  gv;
          transition_post = [];
          transition_state_transition = mk_state_transition_from_action (ActionIntro el) st.state_vars; 
          transition_label = [];
          transition_is_loop_back = false 
        } in
        let (mo, st_m) = translate_cmd mo st_i2 funs syscalls attacks (meta_num, loc_num + (List.length el), top_num) None o pol c in
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
        mo
      end 
    in 

    (* now add normal behavior *)
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
    let (mo, st_m) = translate_cmd mo st_i funs syscalls attacks (meta_num, loc_num + (List.length el), top_num) None o pol cmd in


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
      let (mo, st) = translate_guarded_cmd mo st funs syscalls attacks vars scope syscall pol (vl, fl, c) in
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
    let mindex = st.state_index in 
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
        (LoopFact (mo.model_name, mindex, 0))
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
      let (mo, st_f) = translate_guarded_cmd mo st funs syscalls attacks vars scope syscall pol (vl, fl, c) in
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
          (LoopFact (mo.model_name, mindex, 1))
        ];
        transition_is_loop_back = true   
      }) mo scope_lst1 cs1 in

    let mo = List.fold_left2 (fun mo scope (vl, fl, c) -> 
      let (mo, st) = translate_guarded_cmd mo st funs syscalls attacks vars scope syscall pol (vl, fl, c) in
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
          (LoopFact (mo.model_name, mindex, 2))
        ];
        transition_is_loop_back = false   
      }) mo scope_lst2 cs2 in
    
    (add_state mo st_f, st_f)

 | Syntax.Event (fl) ->
    let fl, gv, acps, _ = translate_facts mo.model_name fl in 
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
  let el, gv, _ = List.fold_left (fun (el, gv, n) e -> let e, g, n = translate_expr2 ~num:n e in
    (el @ [e], gv @ g, n)) ([],[], 0) el in    

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

  let (mo, st) = translate_cmd mo st_f funs syscalls attacks (meta_num+1, loc_num, top_num) None syscall pol  c in

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
    let e, g, _ = translate_expr2 id in

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

  let (mo, st) = translate_cmd mo st_f funs syscalls attacks (meta_num + (List.length vl), loc_num, top_num) None syscall pol c in

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
    let e, g, _ = translate_expr2 id in
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
  


and translate_guarded_cmd mo st funs syscalls attacks vars scope syscall pol (vl, fl, c) = 
  let (meta_num, loc_num, top_num) = vars in 

  let fl, gv, acps, _ = translate_facts mo.model_name fl in
  let acps = List.map (fun target -> AccessFact(mo.model_name, Param, target,syscall)) acps in
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
  let (mo, st_f) = translate_cmd mo st_f funs syscalls attacks (meta_num + List.length vl, loc_num, top_num) None syscall pol c in
  (mo, st_f)




let translate_process {
        Context.proc_pid=k;
        Context.proc_name=s;
        Context.proc_type=pty_unused;
        Context.proc_filesys=fls;
        Context.proc_variable=vars;
        Context.proc_function=fns;
        Context.proc_main=m;
        Context.proc_channels=channels;
        
      } syscalls attacks pol =
  let namespace = String.capitalize_ascii (s ^ (if k = 0 then "" else string_of_int k)) in (* this must be unique *)
  (* let t = add_comment t ("- Process name: " ^ namespace) in  *)

  let mo, st = initial_model namespace pty_unused in 

  (* installed channels: *)
  (* let (mo, st) = List.fold_left (fun (mo, st) c ->

  ) (mo, st) channels in *)


  (* initialize file system *)
  let (mo, st) = List.fold_left (fun (mo, st) (path, ty, e) ->
      (* let path = (mk_dir eng fsys path) in *)
      let st_f = next_state ~shift:(0,0,0) st None in 
      let mo = add_state mo st_f in  
      let e, gv, _ = translate_expr2 e in  
      let path, gv', _ = translate_expr2 path in  
      
      (* let name = mk_fact_name  namespace^ replace_string '/' !separator path in  *)
      let mo = add_transition mo {
        transition_id = List.length mo.model_transitions;
        transition_namespace = mo.model_name;
        transition_name = "init_filesys";
        transition_from = st;
        transition_to = st_f;
        transition_pre = gv;
        transition_post = [FileFact(namespace, path, e)] 
        @ List.map (fun (_, _, scall) -> AccessFact(mo.model_name, Param, path, scall)) (List.filter (fun (pty, tyl, _) -> pty = pty_unused && List.exists (fun s -> s = ty) tyl) pol.Context.pol_access)
        @ if List.exists (fun (pty, tyl) -> pty = pty_unused && List.exists (fun s -> s = ty) tyl) pol.Context.pol_access_all then [AccessFact(mo.model_name,Param,  path, "")] else []
        ;
        transition_state_transition = mk_state_transition_from_action (ActionReturn Unit) st.state_vars;
        transition_label = [];
        transition_is_loop_back = false   
      } in
      (mo, st_f)) (mo, st) fls in 
     
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
          let e, gv, _ = translate_expr2 e in  
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
  let (mo, st) = translate_cmd mo st fns syscalls attacks (0, 0, List.length vars) None "" pol  m in
  
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
  Context.sys_param_proc = param_proc ;
  Context.sys_lemma = lem
} (used_idents, used_string) = 

  separator := (let names = get_fact_names ctx in 
   let rec f s = if List.exists (fun u -> contains u s) names then f (s ^"_") else s in 
    f "_");
  
  fresh_ident := (let rec f s = if List.exists (fun u -> u = s) used_idents then f (s^"_") else s in 
	  f "rab") ;

  fresh_string := (let rec f s = if List.exists (fun u -> u = s) used_string then f (s^"_") else s in 
		                  f "rab") ;

  fresh_param := (let rec f s = if List.exists (fun u -> u = s) used_string then f (s^"_") else s in 
  f "param") ;                      
  

  let sep = !separator in

  let t : tamarin = empty_tamarin in

  (* process signature *)
  let t = List.fold_left (fun t (f, k) -> add_fun t (f, k)) t (List.rev ctx.Context.ctx_ext_func) in
  let t = List.fold_left (fun t c -> add_const t c) t (List.rev ctx.Context.ctx_ext_const) in
  let t = List.fold_left (fun t (_, e1, e2) -> add_eqn t (translate_expr e1, translate_expr e2)) t (List.rev def.Context.def_ext_eq) in

  (* global constants *)
  let t = tamarin_add_comment t "Global Constants:" in

  let t = List.fold_left (fun t (v, e) -> 
	      match e with
	      | None -> (* when v is fresh *) 
          tamarin_add_rule t 
          ("Const"^sep^v, "", [ResFact(2, [Var v])], 
            [InitFact [String ("Const"^sep^v)]; 
            InitFact [List [String ("Const"^sep^v); Var v]]; mk_constant_fact v], 
            [mk_constant_fact v])
	      | Some e -> (* when v is defined *) 
          let e, gv, _ = translate_expr2 e in  
      		tamarin_add_rule t ("Const"^sep^v, "", gv, [ConstantFact(String v, e)], [ConstantFact(String v, e)])) t (List.rev def.Context.def_const) in

  let t = tamarin_add_comment t "Parametric global Constants:" in

  let t = List.fold_left (fun t (v, e) -> 
    match e with
    | None -> (* when v is fresh *) 
      tamarin_add_rule t 
      ("Const"^sep^v, "", 
        [ResFact(2, [Var v])], 
        [InitFact [expr_pair (String v) Param]; ConstantFact (expr_pair (String v) Param, Var v)], 
        [ConstantFact (expr_pair (String v) Param, Var v)])
    | Some (p, e) -> (* when v is defined *) 
      let e, gv, _ = translate_expr2 e in  
      tamarin_add_rule t ("Const"^sep^v, "", gv, 
        [InitFact [expr_pair (String v) Param]; ConstantFact (expr_pair (String v) Param, e)], 
        [ConstantFact (expr_pair (String v) Param, e)])) 
      t (List.rev def.Context.def_param_const) in
    

  let il =[] in 
  let t = tamarin_add_comment t "Access control:" in
  (* access control *)

  (* let t = add_comment t "Processes:" in *)
  let mos = List.fold_left (fun mos p ->  (translate_process p def.Context.def_ext_syscall def.Context.def_ext_attack pol)::mos) [] (List.rev proc) in
  let facts_gv_list = List.fold_left (fun (facts_gv_list) p -> 
    let namespace = String.capitalize_ascii (p.Context.proc_name ^ (if p.Context.proc_pid = 0 then "" else string_of_int p.Context.proc_pid)) in 
    let new_pol = pol.Context.pol_access @ (List.map (fun (a, b) -> (a, b, "")) pol.Context.pol_access_all) in
    let facts_gv_list' = List.fold_left (fun (facts_gv_list) c -> 
      (* List.fold_left  *)
      begin
      match c with
      | Syntax.ChanArgPlain (cname, cty) -> 
        false, List.map (fun (_, _, scall) ->
          print_fact' (AccessFact(namespace, String !fresh_string, String cname, scall))) 
          (List.filter (fun (pty, tyl, scall ) -> pty = p.Context.proc_type && List.exists (fun v -> v = cty) tyl) new_pol), []
      | Syntax.ChanArgParam (cname, cty) -> 
        true, List.map (fun (_, _, scall) ->
          print_fact' (AccessFact(namespace, String !fresh_string,List [String cname; Var !fresh_ident], scall))) 
          (List.filter (fun (pty, tyl, scall ) -> pty = p.Context.proc_type && List.exists (fun v -> v = cty) tyl) new_pol), []
      | Syntax.ChanArgParamInst (cname, e, cty) -> 
        let e, gv', _ = translate_expr2 e in 
        false, List.map (fun (_, _, scall) ->
          print_fact' (AccessFact(namespace, String !fresh_string,List [String cname; e], scall))) 
          (List.filter (fun (pty, tyl, scall ) -> pty = p.Context.proc_type && List.exists (fun v -> v = cty) tyl) new_pol), gv'
        end :: facts_gv_list 
      ) [] (p.Context.proc_channels) in 
    facts_gv_list@facts_gv_list'
    ) ([]) (List.rev proc) in 
  
  
  let t = tamarin_add_rule' t 
    ("Init"^ !separator ^"system", "system", [], [print_fact' (InitFact ([String "system"]))], 
    (* initializing tokens..  *)
    (List.map (fun m -> 
      let st = m.model_init_state in
      (if !Config.tag_transition 
      then mk_state_transition ~param:!fresh_string st (Unit, [], [], []) true false 
      else mk_state ~param:!fresh_string st (Unit, [], [], []))) mos) @
      [print_fact' (AccessGenFact ("system"^ !separator, String !fresh_string)) ]
      ) in 

  let t, _ = List.fold_left (fun (t, n) (b, facts, gv) ->  
    List.fold_left (fun (t, n) (fact : fact') -> 
      tamarin_add_rule' t 
        ("Init"^ !separator ^"system"^ !separator^"ACP" ^ !separator^ string_of_int n, "system", 
        (List.map print_fact' gv)@
        [print_fact' (AccessGenFact ("system"^ !separator, String !fresh_string))], 
        [print_fact'
          (if b then (InitFact ([List [String ("system" ^ !separator^ "ACP" ^ !separator ^ string_of_int n) ; Var !fresh_ident]]))
          else (InitFact [(String ("system" ^ !separator ^ "ACP" ^ !separator ^ string_of_int n))]))
          ],
        [fact]), n+1) (t, n) facts) (t,0) facts_gv_list in       


    

  let t = List.fold_left (fun t m -> add_model t m) t mos in

  let t, _ = List.fold_left (fun (t, n) pl ->
    
    let mos = List.fold_left (fun mos p ->  (translate_process p def.Context.def_ext_syscall def.Context.def_ext_attack pol)::mos) [] (List.rev pl) in
    let facts_gv_list = List.fold_left (fun facts_gv_list p -> 
      let namespace = String.capitalize_ascii (p.Context.proc_name ^ (if p.Context.proc_pid = 0 then "" else string_of_int p.Context.proc_pid)) in 
      (* print_string namespace; *)
      let new_pol = pol.Context.pol_access @ (List.map (fun (a, b) -> (a, b, "")) pol.Context.pol_access_all) in
      let facts_gv_list' = List.fold_left (fun facts_gv_list c -> 
        begin match c with
        | Syntax.ChanArgPlain (cname, cty) -> 
  
          false, List.map (fun (_, _, scall) ->
            print_fact' (AccessFact(namespace, Param, String cname, scall))) 
            (List.filter (fun (pty, tyl, scall ) -> pty = p.Context.proc_type && List.exists (fun v -> v = cty) tyl) new_pol), []
        | Syntax.ChanArgParam (cname, cty) -> 
  
          true, List.map (fun (_, _, scall) ->
            print_fact' (AccessFact(namespace, Param, List [String cname; Var !fresh_ident], scall))) 
            (List.filter (fun (pty, tyl, scall ) -> pty = p.Context.proc_type && List.exists (fun v -> v = cty) tyl) new_pol), []
        | Syntax.ChanArgParamInst (cname, e, cty) -> 
  
          let e, gv', _ = translate_expr2 e in 
          false, List.map (fun (_, _, scall) ->
            print_fact' (AccessFact(namespace, Param, List [String cname; e], scall))) 

            (List.filter (fun (pty, tyl, scall ) -> pty = p.Context.proc_type && List.exists (fun v -> v = cty) tyl) new_pol), gv'
          
        end :: facts_gv_list
        ) ([]) (p.Context.proc_channels) in 
      (facts_gv_list@facts_gv_list')
      ) ([]) (List.rev pl) in 
    
    
    let t = tamarin_add_rule' t 
      ("Init"^ !separator ^"system"^string_of_int n, "system"^string_of_int n, 
      [("Fr", [Param], config_linear)], 
      [print_fact' (InitFact ([List [String ("system"^string_of_int n); Param]]))], 
      [print_fact' (AccessGenFact ("system"^string_of_int n^ !separator, Param)) ] @ List.map (fun m -> 
        let st = m.model_init_state in
        (if !Config.tag_transition 
        then mk_state_transition st (Unit, [], [], []) true false 
        else mk_state st (Unit, [], [], []))) mos) in 
    
    let t, _ = List.fold_left (fun (t, m) (b, facts, gv) ->  
      List.fold_left (fun (t, m) (fact : fact') -> 
        tamarin_add_rule' t 
          ("Init"^ !separator ^"system"^string_of_int n^ !separator^"ACP" ^ !separator^ string_of_int m, "system"^string_of_int n, 
          (List.map print_fact' gv)@
          [print_fact' (AccessGenFact ("system"^string_of_int n^ !separator, Param))], 
          [print_fact'
            (if b then (InitFact ([List [String ("system"^string_of_int n ^ !separator^ "ACP" ^ !separator ^ string_of_int m) ; Param ; Var !fresh_ident]]))
            else (InitFact [List [(String ("system"^string_of_int n ^ !separator ^ "ACP" ^ !separator ^ string_of_int m)) ; Param  ]]))
            ],
          [fact]), m+1) (t, m) facts) (t,0) facts_gv_list in       
      

    let t = List.fold_left (fun t m -> add_model t m) t mos in
    (t, n+1)
  ) (t, 1) (List.rev param_proc) in 


  (* translating lemmas now *)
  let t = List.fold_left (fun t l ->
    let l =
      match l.Location.data with
      | Syntax.PlainLemma (l, p) -> PlainLemma (l, p)
      | Syntax.ReachabilityLemma (l, cs, ps, vs, fs) -> 
        let fs, gv, _, _ = translate_facts "" fs in 
        ReachabilityLemma (l, cs, ps, vs, gv, fs)     
      | Syntax.CorrespondenceLemma (l, vl,a, b) -> 
        let [a], gva, _, _ = translate_facts "" [a] in 
        let [b], gvb, _, _ = translate_facts "" [b] in 
        CorrespondenceLemma (l, vl, (gva, a), (gvb, b))

          (* | ReachabilityLemma of string * string list * string list * string list * (string * expr list) list *)
          (* | CorrespondenceLemma of string * string list * (string * expr list) * (string * expr list) *)


      (* | Syntax.CorrespondenceLemma (l, vars, e1, e2) -> 
        CorrespondenceLemma (l, vars, 
            (match e1.Location.data with
            | Syntax.Event (id, el) -> (mk_fact_name id, List.map (translate_expr ~ch:false) el)),
            (match e2.Location.data with
            | Syntax.Event (id, el) -> (mk_fact_name id, List.map (translate_expr ~ch:false) el)))
      *)    

      | _ -> error ~loc:Location.Nowhere (UnintendedError "")
    in tamarin_add_lemma t l) t lem in
  t

