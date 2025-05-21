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

let _mk_fact_name s = String.capitalize_ascii s

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
  | Apply(_s, el) -> List.fold_left (fun vl e -> (expr_collect_vars e) @ vl) [] el
  | String _ -> []
  | Integer _ -> []
  | List el -> List.fold_left (fun vl e -> (expr_collect_vars e) @ vl) [] el
  | One -> []
  | Int _ -> []
  | AddOne e -> expr_collect_vars e
  | Unit -> []
  | Param -> [Param]

let get_return_var () =
  Var ("return" ^ !separator ^ "var")

type equations = (expr * expr) list
type signature = functions * equations

let empty_signature = ([], [])

type rule_config = {is_persist : bool ; priority : int}

let config_linear = {is_persist=false; priority = 2}
let config_persist = {is_persist=true; priority = 2}
let _config_linear_delayed = {is_persist=false; priority = 0}
let _config_persist_delayed = {is_persist=true; priority = 0}
let _config_linear_prior = {is_persist=false; priority = 3}
let _config_linear_less = {is_persist=false; priority = 1}
let _config_persist_less = {is_persist=true; priority = 1}

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
  | GlobalFact (_s, el) ->
    List.fold_left (fun vl v ->
      if List.exists (fun w -> w = v) vl then vl else v::vl
      ) []
        (List.fold_left (fun vl e -> (expr_collect_vars e) @ vl) [] el)
  | ConstantFact (e1, e2) -> expr_collect_vars e1 @expr_collect_vars e2
  | _ -> assert false

type fact' = string * expr list * rule_config

let print_fact' (f : fact) : fact' =
  match f with
  | Fact (fid, nsp, el) -> (mk_my_fact_name fid ^ ! separator ^ nsp, Param::el, config_linear)
  | ConstantFact (e1, e2) -> ("Const"^ !separator , [e1 ; e2], config_persist)
  | GlobalFact (fid, el) -> (mk_my_fact_name fid, el, config_linear)
  | ChannelFact (fid, ch, el) -> (mk_my_fact_name fid, ch :: el, config_linear)
  (* | PathFact (fid, nsp, path, el) -> (mk_my_fact_name fid ^ ! separator ^ nsp,path :: el, config_linear) *)
  | ResFact (0, el) -> ("Eq"^ !separator , el, config_persist)
  | ResFact (1, el) -> ("NEq"^ !separator , el, config_persist)
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
  | _ -> assert false

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
     | _ ->     "<" ^ (mult_list_with_concat (List.map (print_expr) el) ", ") ^ ">")
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

type model = {
  model_name : string;
  model_states : state list;
  model_transitions : transition list;
  model_init_rules : rule list ;
  model_init_state : state ;
  model_transition_id_max : int;
  model_type : string;
}

let _add_rule (mo : model) (a, b, c, d, e) =
  {mo with model_init_rules = (Rule (a, b, List.map print_fact' c, List.map print_fact' d, List.map print_fact' e)) :: mo.model_init_rules}

let _add_comment (mo : model) r =
  {mo with model_init_rules = (Comment r) :: mo.model_init_rules}

let _add_comment t s = ((Comment s) :: ((t)))

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

let _initial_attacker_model name ty =
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

type tamarin = {
  signature : signature;
  models : model list;
  rules : rule list;
  lemmas : lemma list
}

let add_fun tamarin f =
  let fns, eqns = tamarin.signature in
  { tamarin with signature = (f::fns, eqns) }

let add_const tamarin c =
  let fns, eqns = tamarin.signature in
  { tamarin with signature = ((c,0)::fns, eqns) }

let add_eqn tamarin eq =
  let fns, eqns = tamarin.signature in
  { tamarin with signature = (fns, eq::eqns) }

let add_model t m = { t with models = m :: t.models }

let add_rule t (a, b, c, d, e) =
  { t with rules = Rule (a, b,List.map print_fact' c,List.map print_fact' d,List.map print_fact' e) :: t.rules }

let add_rule' t (a, b, c, d, e) =
  { t with rules= Rule (a, b, c,d,e) :: t.rules }

let add_comment t s = { t with rules = Comment s :: t.rules }

let add_lemma t lem = { t with lemmas = lem :: t.lemmas }

let empty_tamarin : tamarin  = { signature= empty_signature; models= []; rules= []; lemmas= [] }

let print_signature (fns, eqns) =
  let print_functions fns =
    (if List.length fns = 0 then "" else "functions: ")^(mult_list_with_concat (List.map (fun (f, ar) -> f ^"/"^(string_of_int ar)) fns) ", ") ^"\n" in
  let print_equations eqns =
    (if List.length eqns = 0 then "" else "equations: ")^(mult_list_with_concat (List.map (fun (e1, e2) -> (print_expr e1)^"="^(print_expr e2)) eqns) ", ") ^"\n" in
  (print_functions fns) ^ (print_equations eqns)

let _print_fact_plain (f, el) =
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
      | _ ->    "--[" ^ (mult_list_with_concat (List.map print_fact2 label) ", ") ^ "]->")^

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
  | ReachabilityLemma (l, _cs, _ps, _vars, gv, facts) ->
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



  | CorrespondenceLemma (l, _vl, (gva, a), (gvb, b)) ->
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


let print_tamarin { signature=si; models= mo_lst; rules= r_lst; lemmas= lem_lst } is_dev print_transition_label =
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

    "rule Equality_gen: [] --> [!Eq"^ !separator ^"(x,x)]\n" ^

    "rule NEquality_gen: [] --[NEq_"^ !separator ^"(x,y)]-> [!NEq"^ !separator ^"(x,y)]\n" ^

    "restriction NEquality_rule: \"All x #i. NEq_"^ !separator ^"(x,x) @ #i ==> F\"\n" ^

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
