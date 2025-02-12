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
type rule = 
  | Rule of string * string * fact list * fact list * fact list
  | Comment of string

type tamarin = signature * rule list

let add_rule t (a, b, c, d, e) = (fst t, (Rule (a, b, c, d, e)) :: ( (snd t)))
let add_comment t s = (fst t, (Comment s) :: ((snd t)))

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
  | MetaVar i -> "meta"^prt.prt_sep^string_of_int i
  | LocVar i -> "loc"^prt.prt_sep^string_of_int i
  | TopVar i -> "top"^prt.prt_sep^string_of_int i
  | Apply (s, el) -> s ^ "(" ^ (mult_list_with_concat (List.map (print_expr prt) el) ", ") ^ ")"
  | String s -> "\'rab" ^ prt.prt_sep ^ (replace_string '/' prt.prt_sep s)^"\'"
  | Integer i -> "\'"^string_of_int i^"\'"
  | List el -> 
     (match el with
     | [] -> "\'rab"^prt.prt_sep^"\'"
     | [e] -> print_expr prt e 
     | _ -> 	"<" ^ (mult_list_with_concat (List.map (print_expr prt) el) ", ") ^ ">")
  | One -> "%1"
  | Int v -> "%"^v
  | AddOne e -> (print_expr prt e)^" %+ %1"

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


let print_tamarin prt ((sign, rules), init_list, procs, lem) dev = 
  "theory rabbit\n\nbegin\nbuiltins: natural-numbers\n\n"^
    print_signature prt sign ^
      (mult_list_with_concat (List.map (fun r -> print_rule prt r dev) (List.rev rules)) "")^
	
	List.fold_left (fun l s -> l^"\nrestriction "^s^" : \" All #i #j . "^s^"() @ #i & "^s^"() @ #j ==> #i = #j \"") "" init_list ^ "\n" ^

  "\nrestriction Init"^prt.prt_sep^" : \" All x #i #j . Init"^prt.prt_sep^"(x) @ #i & Init"^prt.prt_sep^"(x) @ #j ==> #i = #j \"\n" ^

	  (* if then else restriction *)

	  (* "\nrestriction OnlyOnce : \" All x #i #j . OnlyOnce(x) @ #i & OnlyOnce(x) @ #j ==> #i = #j \"\n" ^ *)

    "restriction Equality: \" All x y #i. Eq(x,y) @ #i ==> x = y\"\n" 

    ^

    "restriction Inequality: \"All x #i. Neq(x,x) @ #i ==> F\"\n" 

    ^

    "rule Equality_gen: [] --> [!Eq"^prt.prt_sep^"(x,x)]\n" 

    ^

    "rule NEquality_gen: [] --[NEq_"^prt.prt_sep^"(x,y)]-> [!NEq"^prt.prt_sep^"(x,y)]\n" 

    ^

    "restriction NEquality_rule: \"All x #i. NEq_"^prt.prt_sep^"(x,x) @ #i ==> F\"\n"

    ^

    List.fold_left (fun s p -> 
      let tfact = "Trace"^prt.prt_sep^p in 
      s^"lemma "^tfact^"[use_induction,reuse] : all-traces \"All x y #i #j . "^tfact^"(x, y) @ #i & "^tfact^"(x, y) @ #j ==> #i = #j\"\n") "" (List.rev procs) 

    ^

    List.fold_left (fun l lem -> l ^ print_lemma prt lem) "" lem ^"\nend\n"

type engine = {
    namespace : string; 
    index : ((int list) * int) list;
    sep : string;
  }

let empty_engine = {namespace = ""; index = [([],0)]; sep = "";}

let engine_index_inc eng scope = 
  match scope with
  | None ->
    begin match eng.index with
    | (l,i)::lst -> {eng with index=(l,i+1)::lst}
    | _ -> error ~loc:Location.Nowhere (UnintendedError "index ill-defined")
    end
  | Some s -> {eng with index=(s, 0)::eng.index}

let rec translate_expr ?(ch=false) sep {Location.data=e; Location.loc=loc} = 
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
    | Syntax.Apply (o, el) -> Apply (o, List.map (translate_expr ~ch:ch sep) el)
    | Syntax.Tuple el -> 
       List (List.map (translate_expr ~ch:ch sep) el)
    | Syntax.Channel (c, l) -> if ch then Var c else String c
    | Syntax.Process v -> Var v
    | Syntax.Path v -> Var v
  in translate_expr' e

let rec translate_expr2 ?(ch=false) sep {Location.data=e; Location.loc=loc} = 
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
			  let e, s = translate_expr2 ~ch:ch sep e in 
			  (el @ [e], sl @ s)) ([], []) el in 
       Apply (o, el), sl
    | Syntax.Tuple el -> 
       let (el, sl) = List.fold_left (fun (el, sl) e -> 
			  let e, s = translate_expr2 ~ch:ch sep e in 
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
(* engine has 
  (1) separator
  (2) index structure
  (3) and scope  *)
let engine_set_namespace eng nspace = {eng with namespace=nspace}
let engine_set_sep eng sep = {eng with sep=sep}

let engine_state_name eng =
  "State"^eng.sep^eng.namespace

let mk_my_fact_name eng s = 
  (String.capitalize_ascii s)
  (* ^eng.sep *)

let engine_state_aux eng =
  (
    List.fold_left (fun s (scope, ind) -> s ^ 
    (mult_list_with_concat (List.map string_of_int scope) "_")
    ^ eng.sep ^ string_of_int ind) "" eng.index
  ) 

let engine_state eng =
  String (engine_state_aux eng)

let make_rule_name eng scope = 
  eng.namespace^eng.sep^engine_state_aux eng ^ (match scope with Some scope -> (mult_list_with_concat (List.map string_of_int scope) "_") | None -> "")

let lctx_to_var_list lctx =
  (List.map (fun s -> Var s) lctx)

let rec var_list_replace lctx s e =
  match lctx with
  | Var w :: l -> (if w = s then e else Var w) :: (var_list_replace l s e)
  | _ :: l -> error ~loc:Location.Nowhere (UnintendedError "lctx is not list") 
  | [] -> [] 

let int_to_list n =
  let rec aux i acc =
    if i < 0 then acc
    else aux (i - 1) (i :: acc)
  in
  aux (n - 1) []

let mk_state eng return_var (meta_num, loc_num, top_num) tnum = 
  (engine_state_name eng, 
    [
      List [engine_state eng; tnum] ;
      return_var; 
      List (List.map (fun i -> MetaVar i) (int_to_list meta_num)); 
      List (List.map (fun i -> LocVar i) (int_to_list loc_num)); 
      List (List.map (fun i -> TopVar i) (int_to_list top_num))
      ], config_linear) 


let mk_state_app eng return_var (meta_num, loc_num, top_num) e tnum = 
  (engine_state_name eng, 
    [
      List [engine_state eng; tnum] ;
      return_var; 
      List (List.map (fun i -> MetaVar i) (int_to_list meta_num)); 
      List (e :: (List.map (fun i -> LocVar i) (int_to_list loc_num))); 
      List (List.map (fun i -> TopVar i) (int_to_list top_num))
      ], config_linear) 

let mk_state_app_list eng return_var (meta_num, loc_num, top_num) el tnum = 
  (engine_state_name eng, 
    [
      List [engine_state eng; tnum] ;
      return_var; 
      List (List.map (fun i -> MetaVar i) (int_to_list meta_num)); 
      List (el @ (List.map (fun i -> LocVar i) (int_to_list loc_num))); 
      List (List.map (fun i -> TopVar i) (int_to_list top_num))
      ], config_linear) 

let mk_state_app_top eng return_var (meta_num, loc_num, top_num) e tnum = 
  (engine_state_name eng, 
    [
      List [engine_state eng; tnum] ;
      return_var; 
      List (List.map (fun i -> MetaVar i) (int_to_list meta_num)); 
      List ((List.map (fun i -> LocVar i) (int_to_list loc_num))); 
      List (e ::  (List.map (fun i -> TopVar i) (int_to_list top_num)))
      ], config_linear) 

let mk_state_shift eng return_var (meta_num, loc_num, top_num) (n, m, l) tnum = 
  (engine_state_name eng, 
    [
      List [engine_state eng; tnum] ;
      return_var; 
      List (List.map (fun i -> MetaVar (i+n)) (int_to_list meta_num)); 
      List (List.map (fun i -> LocVar (i+m)) (int_to_list loc_num)); 
      List (List.map (fun i -> TopVar (i+l)) (int_to_list top_num))
     ], config_linear) 

let mk_state_replace eng return_var (meta_num, loc_num, top_num) (j, b) e tnum = 
  (engine_state_name eng, 
    [      
      List [engine_state eng; tnum] ;
      return_var; 
      List (List.map (fun i -> MetaVar i) (int_to_list meta_num)); 
      List (List.map (fun i -> if (not b) && i = j then e else LocVar i) (int_to_list loc_num)); 
      List (List.map (fun i -> if b && i = j then e else TopVar i) (int_to_list top_num)) 
    ], config_linear) 

let mk_state_replace_and_shift eng return_var (meta_num, loc_num, top_num) (n, m, l) (j, b) e tnum =  
  (engine_state_name eng, 
    [      
      List [engine_state eng; tnum] ;
      return_var;  
      List (List.map (fun i -> MetaVar (i+n)) (int_to_list meta_num)); 
      List (List.map (fun i -> if (not b) && i = j then e else LocVar (i+m)) (int_to_list loc_num)); 
      List (List.map (fun i -> if b && i = j  then e else TopVar (i+l)) (int_to_list top_num))
    ], config_linear) 


(* let append_loc state e =
  (engine_state eng, 
    [return_var; 
     List (List.map (fun i -> Var ("meta"^eng.sep ^ (int_to_list meta_num)))); 
     List (List.map (fun i -> Var ("meta"^eng.sep ^ (int_to_list loc_num)))); 
     List (List.map (fun i -> Var ("meta"^eng.sep ^ (int_to_list top_num))));
     ])  *)

let translate_fact eng f = 
  match f.Location.data with
  | Syntax.Fact(id, el) -> 
    let el, gv = List.fold_left (fun (el, gv) e -> let e, g = translate_expr2 eng.sep e in
                                  (el @ [e], gv @ g)) ([],[]) el in    
    let gv = List.map (fun s -> ("Const"^eng.sep, [String s ; Var s], config_persist)) gv in 
    (mk_my_fact_name eng id, (String eng.namespace) :: el, config_linear), gv, []

  | Syntax.GlobalFact(id, el) -> 
    let el, gv = List.fold_left (fun (el, gv) e -> let e, g = translate_expr2 eng.sep e in
                                  (el @ [e], gv @ g)) ([],[]) el in    
    let gv = List.map (fun s -> ("Const"^eng.sep, [String s ; Var s], config_persist)) gv in 

    (mk_my_fact_name eng id, el, config_linear), gv, []

  | Syntax.ChannelFact(ch, id, el) ->
    let el, gv = List.fold_left (fun (el, gv) e -> let e, g = translate_expr2 eng.sep e in
                                  (el @ [e], gv @ g)) ([],[]) (ch::el) in    
    let gv = List.map (fun s -> ("Const"^eng.sep, [String s ; Var s], config_persist)) gv in 
    
    (* let acp = ("ACP"^eng.sep^"chan", String eng.namespace, String ch, config_persist) in  *)
    
    (mk_my_fact_name eng id, el, config_linear), gv, [translate_expr eng.sep ch]

  | Syntax.PathFact (path, id, el) -> 
    let el, gv = List.fold_left (fun (el, gv) e -> let e, g = translate_expr2 eng.sep e in
                                  (el @ [e], gv @ g)) ([],[]) (path::el) in    
    let gv = List.map (fun s -> ("Const"^eng.sep, [String s ; Var s], config_persist)) gv in 
    
    (* let acp = ("ACP"^eng.sep"path", String eng.namespace, String ch, config_persist) in  *)

    (mk_my_fact_name eng id, (String eng.namespace)::el, config_linear), gv, [translate_expr eng.sep path]

  | Syntax.ResFact (0, el) -> 
    let el, gv = List.fold_left (fun (el, gv) e -> let e, g = translate_expr2 eng.sep e in
                                  (el @ [e], gv @ g)) ([],[]) (el) in    
    let gv = List.map (fun s -> ("Const"^eng.sep, [String s ; Var s], config_persist)) gv in 
    
    (* let acp = ("ACP"^eng.sep"path", String eng.namespace, String ch, config_persist) in  *)

    ("Eq"^eng.sep, el, config_persist), gv, []

  | Syntax.ResFact (1, el) -> 
    let el, gv = List.fold_left (fun (el, gv) e -> let e, g = translate_expr2 eng.sep e in
                                  (el @ [e], gv @ g)) ([],[]) (el) in    
    let gv = List.map (fun s -> ("Const"^eng.sep, [String s ; Var s], config_persist)) gv in 
    
    (* let acp = ("ACP"^eng.sep"path", String eng.namespace, String ch, config_persist) in  *)

    ("NEq"^eng.sep, el, config_persist), gv, []



  | _ -> 
    error ~loc:Location.Nowhere (UnintendedError "process fact")

let translate_facts eng fl =
  List.fold_left (fun (fl, gv, acps) f -> 
              let (f, gv', acps') = translate_fact eng f in 
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

let trace_fact eng tnum = ("Trace"^eng.sep^eng.namespace, [String (engine_state_aux eng) ; tnum], config_linear)


let rec translate_cmd eng funs syscalls vars scope syscall {Location.data=c; Location.loc=loc} = 
  let return_var = Var ("return"^eng.sep) in
  let return_unit = String ("unit"^eng.sep) in 
  let (meta_num, loc_num, top_num) = vars in 
  let trace_num = (Int ("n"^eng.sep^eng.sep)) in
  let trace_fact eng = ("Trace"^eng.sep^eng.namespace, [String (engine_state_aux eng) ; trace_num], config_linear) in

  match c with
  | Syntax.Return e ->
    let e, gv = translate_expr2 eng.sep e in  
    let gv = List.map (fun s -> ("Const"^eng.sep, [String s ; Var s], config_persist)) gv in 

    let eng_f = engine_index_inc eng scope in
    ([(
        (make_rule_name eng scope)^"_return", 
        [mk_state eng return_unit vars trace_num] @ gv, 
        [trace_fact eng],
        [mk_state eng_f e vars trace_num])
      ], eng_f)


  | Syntax.Skip -> 
    let eng_f = engine_index_inc eng scope in
    ([(
        (make_rule_name eng scope)^"skip", 
        [mk_state eng return_unit vars trace_num], 
        [trace_fact eng],
        [mk_state eng_f return_unit vars trace_num])
      ], eng_f)


  | Syntax.Sequence (c1, c2) -> 
    let (rl1, eng) = translate_cmd eng funs syscalls vars scope syscall c1 in
    let (rl2, eng) = translate_cmd eng funs syscalls vars None syscall c2 in
    (rl1 @ rl2, eng)

  | Syntax.Put fl -> 
    let fl, gv, acps = translate_facts eng fl in
    let acps = List.map (fun target -> ("ACP"^eng.sep, [String eng.namespace; 
                                                    target; 
                                                    String syscall], config_persist)) acps in
    let eng_f = engine_index_inc eng scope in
    ([((make_rule_name eng scope)^"_put", 
      [mk_state eng return_unit vars trace_num] @ gv @ acps, 
      [trace_fact eng],
      [mk_state eng_f return_unit vars trace_num] @ fl )], eng_f)

  | Syntax.Let (v, e, c) -> 
    
    let e, gv = translate_expr2 eng.sep e in  
    let gv = List.map (fun s -> ("Const"^eng.sep, [String s ; Var s], config_persist)) gv in 
    
    let eng_f = engine_index_inc eng scope in

    let initial_rule = 
      ((make_rule_name eng scope)^"_let", 
        [mk_state eng return_unit vars trace_num] @ gv, 
        [trace_fact eng],
        [mk_state_app eng_f return_unit vars e trace_num]) in 

    let (rl, eng_f) = translate_cmd eng_f funs syscalls (meta_num, loc_num+1, top_num) None syscall c in
   
   (* pop loc variables *)
    let rl = List.map
      (fun r -> 
        let (rname, preconds, label, postconds) = r in
        let postconds = List.fold_left 
          (fun postconds (fn, args , conf) ->
            match args with
            | [List [String st; num] ; ret; meta; List  loc; top] ->
                if st = engine_state_aux eng_f
                then
                  (* when this is the rule, find postcondition's meta variable number then lift current *)

                  postconds @ [(fn, [List [String st; num]; ret; meta; List (pop_hd 1 loc); top], conf)]

                else 
                  postconds @ [(fn, args , conf)]
            | _ -> postconds @ [(fn, args , conf)]) [] postconds in
          (rname, preconds, label, postconds)) rl in

  
    (initial_rule :: rl, eng_f)



  | Syntax.Assign ((v, di), e) -> 

    let e, gv = translate_expr2 eng.sep e in  
    let gv = List.map (fun s -> ("Const"^eng.sep, [String s ; Var s], config_persist)) gv in 

    let eng_f = engine_index_inc eng scope in
    ([((make_rule_name eng scope)^"_assign", 
      [mk_state eng return_unit vars trace_num] @ gv, 
      [trace_fact eng],
      [mk_state_replace eng_f return_unit vars di e trace_num])], eng_f)


  | Syntax.FCall (ov, f, el) ->
    let el, gv = List.fold_left (fun (el, gv) e -> let e, g = translate_expr2 eng.sep e in
                                  (el @ [e], gv @ g)) ([],[]) el in  
    let el = List.rev el in  
    let gv = List.map (fun s -> ("Const"^eng.sep, [String s ; Var s], config_persist)) gv in 
    
    let (f, args, cmd) = List.find (fun (f', args, cmd) -> f = f') funs in 



    let eng_f = engine_index_inc eng scope in
    let initial_rule = 
              ((make_rule_name eng scope)^"_fcall", 
              [mk_state eng return_unit vars trace_num] @ gv, 
              [trace_fact eng],
              [mk_state_app_list eng_f return_unit vars el trace_num]) in

    let (rl, eng_f) = translate_cmd eng_f funs syscalls (meta_num, loc_num + (List.length el), top_num) None syscall cmd in
    

    let eng_ff = engine_index_inc eng_f None in

    let final_rule = 
      begin match ov with
      | Some (_, v) -> 
        (make_rule_name eng_f scope, 
          [mk_state eng_f return_var (meta_num, loc_num + (List.length el), top_num) trace_num],
          [trace_fact eng_f],
          [mk_state_replace_and_shift eng_ff return_unit vars (0, (List.length el), 0) v return_var trace_num])

      | None -> 
        (make_rule_name eng_f scope, 
          [mk_state eng_f return_var (meta_num, loc_num + (List.length el), top_num) trace_num],
          [trace_fact eng_f],
          [mk_state_shift eng_ff return_unit vars (0, (List.length el), 0) trace_num])
      end
    in 
    (initial_rule :: rl @ [final_rule], eng_ff)


  | Syntax.SCall (ov, o, el) ->
    let el, gv = List.fold_left (fun (el, gv) e -> let e, g = translate_expr2 eng.sep e in
                                  (el @ [e], gv @ g)) ([],[]) el in    
    let el = List.rev el in 
    let gv = List.map (fun s -> ("Const"^eng.sep, [String s ; Var s], config_persist)) gv in 
    
    let (f, args, cmd) = List.find (fun (f', args, cmd) -> o = f') syscalls in 



    let eng_f = engine_index_inc eng scope in
    let initial_rule = 
              ((make_rule_name eng scope)^"_scall", 
              [mk_state eng return_unit vars trace_num] @ gv, 
              [trace_fact eng],
              [mk_state_app_list eng_f return_unit vars el trace_num]) in

    let (rl, eng_f) = translate_cmd eng_f funs syscalls (meta_num, loc_num + (List.length el), top_num) None o cmd in
    

    let eng_ff = engine_index_inc eng_f None in

    let final_rule = 
      begin match ov with
      | Some (_, v) -> 
        (make_rule_name eng_f scope, 
          [mk_state eng_f return_var (meta_num, loc_num + (List.length el), top_num) trace_num],
          [trace_fact eng_f],
          [mk_state_replace_and_shift eng_ff return_unit vars (0, (List.length el), 0) v return_var trace_num])

      | None -> 
        (make_rule_name eng_f scope, 
          [mk_state eng_f return_var (meta_num, loc_num + (List.length el), top_num) trace_num],
          [trace_fact eng_f],
          [mk_state_shift eng_ff return_unit vars (0, (List.length el), 0) trace_num])
      end
    in 
    (initial_rule :: rl @ [final_rule], eng_ff)



  | Syntax.Case (cs) ->
    let scope_lst =
      begin match scope with
      | None ->
        List.map (fun i -> Some [i]) (List.init (List.length cs) (fun i -> i))
      | Some l ->
        List.map (fun i -> Some (i :: l)) (List.init (List.length cs) (fun i -> i))
      end in 

    let eng_f = engine_index_inc eng None in

    let rl = List.map2 
    (fun scope c -> 
      let (rl, eng) = translate_guarded_cmd eng funs syscalls vars scope syscall c in
      let final_rule = (make_rule_name eng scope, 
        [mk_state eng return_var vars trace_num], [trace_fact eng], [mk_state eng_f return_var vars trace_num]) in
      rl @ [final_rule]) scope_lst cs in

    (List.flatten rl, eng_f)

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
  
    let eng_f = engine_index_inc eng None in

    let rl1 = List.map2 
      (fun scope c -> 
        let (rl, eng) = translate_guarded_cmd eng funs syscalls vars scope syscall c in
        let loop_rule = (make_rule_name eng scope, [mk_state eng return_var vars trace_num], [trace_fact eng], [mk_state eng return_unit vars (AddOne trace_num)]) in 
        rl @ [loop_rule]) scope_lst1 cs1 in

    let rl2 = List.map2 
      (fun scope c -> 
        let (rl, eng) = translate_guarded_cmd eng funs syscalls vars scope syscall c in
        let final_rule = (make_rule_name eng scope, [mk_state eng return_var vars trace_num], [trace_fact eng], [mk_state eng_f return_var vars trace_num]) in
        rl @ [final_rule]) scope_lst2 cs2 in
    
    (List.flatten (rl1 @ rl2), eng_f)

 | Syntax.Event (fl) ->
    let fl, gv, acps = translate_facts eng fl in 
    let eng_f = engine_index_inc eng scope in
    ([((make_rule_name eng scope)^"_event", 
        [mk_state eng return_unit vars trace_num] @ gv, 
        fl,
        [mk_state eng_f return_unit vars trace_num])
      ], eng_f)


and translate_guarded_cmd eng funs syscalls vars scope syscall (vl, fl, c) = 
  let return_var = Var ("return"^eng.sep) in
  let return_unit = String ("unit"^eng.sep) in 
  let (meta_num, loc_num, top_num) = vars in 
  let trace_num = (Int ("n"^eng.sep^eng.sep)) in
  let trace_fact eng = ("Trace"^eng.sep^eng.namespace, [String (engine_state_aux eng) ; trace_num], config_linear) in

  let fl, gv, acps = translate_facts eng fl in
  let acps = List.map (fun target -> ("ACP"^eng.sep, [String eng.namespace; 
                                                      target; 
                                                      String syscall], config_persist)) acps in
  let eng_f = engine_index_inc eng scope in
  let initial_rule = (
                      (make_rule_name eng scope)^"_wait", 
                      [mk_state_shift eng return_unit vars (List.length vl, 0, 0) trace_num] @ fl @ gv @ acps ,
                      [trace_fact eng],
                      [mk_state eng_f return_unit (meta_num + List.length vl, loc_num, top_num) trace_num]) in 

  let (rl, eng_f) = translate_cmd eng_f funs syscalls (meta_num + List.length vl, loc_num, top_num) None syscall c in

  (* pop meta variables *)
  let rl = List.map
    (fun r -> 
      let (rname, preconds, label, postconds) = r in
      let postconds = List.fold_left 
        (fun postconds (fn, args , conf) ->
          match args with
          | [List [String st; num] ; ret; List meta; loc; top] ->
              if st = engine_state_aux eng_f
              then
                (* when this is the rule, find postcondition's meta variable number then lift current *)

                postconds @ [(fn, [List [String st; num] ; ret; List (pop_hd (List.length vl) meta); loc; top], conf)]

              else 
                postconds @ [(fn, args , conf)]
          | _ -> postconds @ [(fn, args , conf)]) [] postconds in
        (rname, preconds, label, postconds)) rl in


  (initial_rule::rl, eng_f)




let translate_process sep t {
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
  let t = add_comment t ("- Process name: " ^ namespace) in 

  let t = add_comment t "Initial file system:" in
  let t = List.fold_left (fun t (path, e, _, _) ->
      (* let path = (mk_dir eng fsys path) in *)
      let e, gv = translate_expr2 sep e in  
      let gv = List.map (fun s -> ("Const"^sep, [String s ; Var s], config_persist)) gv in 
      let name = mk_fact_name  namespace^ replace_string '/' sep path in 
      add_rule t (name, "",
            gv,
            [("Init"^sep, [List [String namespace; String path]], config_linear)],
            [("File", [String namespace; String path ; e], config_linear)])) t fls in 


  let eng = engine_set_namespace empty_engine namespace in 
  let eng = engine_set_sep eng sep in 
  let eng_f = engine_index_inc eng None in
  let return_var = Var ("return"^eng.sep) in
  let return_unit = String ("unit"^eng.sep) in 

  (* let eng = eng_set_role eng namespace in *)
  (* let eng = eng_set_filesys eng (match fsys with Some fsys -> fsys | None -> "") in *)

  let t = add_comment t ("-- initialization rules") in 
  let t = add_rule t 
          (make_rule_name eng None, namespace,
          [], 
          [("Init"^sep, [String namespace], config_linear)], 
	        [mk_state eng_f return_unit (0, 0, 0) One]) in
  let eng = eng_f in 

  (* initialize memory *)
  let (eng, t, _) = List.fold_left
		   (fun (eng, t, i) (x, e) -> 
		     let eng_f = engine_index_inc eng None in 
		     let e, gv = translate_expr2 sep e in  
		     let gv = List.map (fun s -> ("Const"^eng.sep, [String s ; Var s], config_persist)) gv in 

		     let t = add_rule t 
                  (make_rule_name eng None, namespace,
					         [mk_state eng return_unit (0,0,i) (Int ("n" ^ sep ^sep))] @ gv, 
					         [trace_fact eng (Int ("n" ^ sep ^sep))],  
					         [mk_state_app_top eng_f return_unit (0,0,i) e (Int ("n" ^ sep ^sep))]) in
	       (eng_f, t, i+1)) (eng, t, 0) (List.rev vars) in 

  let t = add_comment t ("-- main function ") in 	
  
  let (r, eng) = translate_cmd eng fns syscalls (0, 0, List.length vars) None "" m in

  List.fold_left (fun t r -> add_rule t 
    (let (rname, pre, lab, post) = r in
    (rname, namespace, pre, lab, post))) t r 


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
  (* let eng = empty_engine in *)
  let sep = (let names = get_fact_names ctx in 
	           let rec f s = if List.exists (fun u -> contains u s) names then f (s ^"_") else s in 
	           f "_") in
  let fresh_ident = (let rec f s = if List.exists (fun u -> u = s) used_idents then f (s^"_") else s in 
		                f "rab") in 

  let fresh_string = (let rec f s = if List.exists (fun u -> u = s) used_string then f (s^"_") else s in 
		                  f "rab") in 
  

  (* process what has been defined first! *)
  let t = List.fold_left (fun t (f, k) -> add_fun t (f, k)) t (List.rev ctx.Context.ctx_ext_func) in
  let t = List.fold_left (fun t c -> add_const t c) t (List.rev ctx.Context.ctx_ext_const) in
  let t = List.fold_left (fun t (_, e1, e2) -> add_eqn t (translate_expr sep e1, translate_expr sep e2)) t (List.rev def.Context.def_ext_eq) in

  (* let t = add_comment t "external system calls:" in
     let t = List.fold_left (fun t r -> translate_syscall eng t r) t (List.rev def.Context.def_ext_syscall) in*)

  let t = add_comment t "Attacks:" in
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

  let t = add_comment t "Global constants:" in
  let t = List.fold_left (fun t (v, e) -> 
	      match e with
	      | None -> (* when v is fresh *) add_rule t ("Const"^sep^v, "", [("Fr", [Var v], config_linear)], [], [("Const"^sep, [String v ; Var v], config_persist)])
	      | Some e -> (* when v is defined *) 
		 let e, gv = translate_expr2 sep e in  
		 let gv = List.map (fun s -> ("Const"^sep, [String s ; Var s], config_persist)) gv in 
		 add_rule t ("Const"^sep^v, "", gv, [], [("Const"^sep, [String v ; e], config_persist)])) t (List.rev def.Context.def_const) in

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
					 let name = procname ^ sep ^ c ^ sep ^ sys in 
					 add_rule t 
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
                  add_rule t 
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
			   add_rule t 
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
       add_rule t 
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
     | Some attk -> add_rule t (mk_fact_name c ^ eng.sep ^ attk, "",
     [], 
     [(mk_fact_name c ^ eng.sep ^ attk ^ eng.sep ^ "init", [], config_linear)], 
     [(mk_fact_name attk ^ eng.sep ^"Allowed", [String c], config_linear)]
     ), (mk_fact_name c ^ eng.sep ^ attk ^ eng.sep ^ "init"):: il
     | None -> t, il) (t, il) ctx.Context.ctx_ch in 
     
   *)

  let t = add_comment t "Processes:" in
  let t = List.fold_left (fun t p -> translate_process sep t p (List.rev def.Context.def_ext_syscall)) t (List.rev proc) in

  let init_list = List.map (fun p -> String.capitalize_ascii (p.Context.proc_name ^ 
                                    (if p.Context.proc_pid = 0 then "" else string_of_int p.Context.proc_pid )
	                                   ) ^ sep^"init") proc in 
  let procs = List.map (fun p -> String.capitalize_ascii (p.Context.proc_name ^ 
                                    (if p.Context.proc_pid = 0 then "" else string_of_int p.Context.proc_pid )
                                     ) ) proc in 
  let init_list = init_list @ il in 

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

  (t, init_list, procs, lem), {prt_sep=sep;}


