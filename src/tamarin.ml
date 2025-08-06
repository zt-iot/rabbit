(* For translating to and printing Tamarin models.
   * 'Rabbit' is a string value palceholder for void output of system calls and functions.
   * GlobalFact is fact that does not bound to any process or channel. Currently
   it only contains reserved facts.
*)
let separator = ref "_"
let fresh_ident = ref "rab_ident"
let fresh_string = ref "rab_str"
let fresh_param = ref "param"

let rec replace_nth lst i new_val =
  match lst with
  | [] -> [] (* If the list is empty, return an empty list *)
  | x :: xs ->
      if i = 0
      then new_val :: xs (* Replace the i-th element *)
      else x :: replace_nth xs (i - 1) new_val (* Recur for the rest *)
;;

let rec pop_n k lst =
  if k <= 0
  then [], lst (* If k is 0 or negative, return the original list *)
  else (
    match lst with
    | [] -> [], [] (* Not enough elements, return empty popped list *)
    | x :: xs ->
        let popped, rest = pop_n (k - 1) xs in
        x :: popped, rest)
;;

let mk_my_fact_name s = String.capitalize_ascii s
let replace_string s t str = String.concat t (String.split_on_char s str)

let int_to_list n =
  let rec aux i acc = if i < 0 then acc else aux (i - 1) (i :: acc) in
  aux (n - 1) []
;;

let contains s1 s2 =
  let re = Str.regexp_string s2 in
  try
    ignore (Str.search_forward re s1 0);
    true
  with
  | Not_found -> false
;;

module Mindex = struct
  type t = Mindex of (int list * int) list

  let zero = Mindex [[], 0]

  let inc index scope =
    match scope with
    | None ->
        (match index with
         | Mindex ((l, i) :: lst) -> Mindex ((l, i + 1) :: lst)
         | _ -> assert false)
    | Some s ->
        let Mindex i = index in
        Mindex ((s, 0) :: i)

  let to_string (Mindex idx) =
    List.fold_left
      (fun s (scope, ind) ->
         s
         ^ !separator
         ^ String.concat "_" (List.map string_of_int scope)
         ^ "_"
         ^ string_of_int ind)
      ""
      (List.rev idx)
end

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
  | FVar _ | Var _ | MetaVar _ | LocVar _ | TopVar _ | MetaNewVar _ | Param -> [ e ]
  | Apply (_s, el) -> List.fold_left (fun vl e -> expr_collect_vars e @ vl) [] el
  | String _ -> []
  | Integer _ -> []
  | List el -> List.fold_left (fun vl e -> expr_collect_vars e @ vl) [] el
  | One -> []
  | Int _ -> []
  | AddOne e -> expr_collect_vars e
  | Unit -> []
;;

let get_return_var () = Var ("return" ^ !separator ^ "var")

type equations = (expr * expr) list

type signature =
  { functions : functions
  ; equations : equations
  }

let empty_signature = { functions = []; equations = [] }

type rule_config =
  { is_persist : bool
  ; priority : int
  }

let config_linear = { is_persist = false; priority = 2 }
let config_persist = { is_persist = true; priority = 2 }
let _config_linear_delayed = { is_persist = false; priority = 0 }
let _config_persist_delayed = { is_persist = true; priority = 0 }
let _config_linear_prior = { is_persist = false; priority = 3 }
let _config_linear_less = { is_persist = false; priority = 1 }
let _config_persist_less = { is_persist = true; priority = 1 }

type var_nums =
  { meta : int
  ; loc : int
  ; top : int
  }

type state =
  { state_namespace : string
  ; state_index : Mindex.t
  ; state_vars : var_nums
  }

type state_desc =
  { ret : expr
  ; metas : expr list
  ; locs : expr list
  ; tops : expr list
  }

type fact =
  | Fact of string (* fact name *) * string (* name space*) * expr list
  | ConstantFact of expr * expr
  | GlobalFact of string * expr list
  | ChannelFact of string * expr * expr list
  | PathFact of string * string (* namespace *) * expr (* path *) * expr list
  | ProcessFact of string * expr * expr list
  | EqFact of expr * expr
  | NeqFact of expr * expr
  | AccessFact of string * expr * expr * string option
  | AttackFact of string * expr
  | FileFact of string * expr * expr
  | InitFact of expr list
  | LoopFact of
      string (* namespace *)
      * Mindex.t (* the index when the loop is entered  *)
      * int (* 0: loop in 2 : loop back 3 : loop out *)
  | TransitionFact of string * string * expr * expr
  | InjectiveFact of
      string
      * (* fact name *)
        string
      * (* namespace *)
        expr
      * (* identity *)
        expr
    (* arguments *)
  | FreshFact of expr
  | FreshFact' of expr
  | AccessGenFact of string (* namespace *) * expr (* param *)
  | StateFact of
      { param : string option
      ; state : state
      ; state_desc : state_desc
      ; transition : expr option
      }

let global_fact_collect_vars f =
  match f with
  | GlobalFact (_s, el) ->
      List.fold_left
        (fun vl v -> if List.exists (fun w -> w = v) vl then vl else v :: vl)
        []
        (List.fold_left (fun vl e -> expr_collect_vars e @ vl) [] el)
  | ConstantFact (e1, e2) -> expr_collect_vars e1 @ expr_collect_vars e2
  | _ -> assert false
;;

type fact' =
  { name : string
  ; args : expr list
  ; config : rule_config
  }

let check_state_and_state_desc st desc =
  assert (List.length desc.metas = st.state_vars.meta);
  assert (List.length desc.locs = st.state_vars.loc);
  assert (List.length desc.tops = st.state_vars.top)
;;

let get_state_fact_name (s : state) = "State" ^ !separator ^ s.state_namespace
let state_index_to_string_aux (st : state) = Mindex.to_string st.state_index
let state_index_to_string st = String (state_index_to_string_aux st)

let compile_state_fact param state state_desc transition =
  check_state_and_state_desc state state_desc;
  { name = get_state_fact_name state
  ; args =
      [ List
          ([ state_index_to_string state
           ; (match param with
              | None -> Param
              | Some param -> String param)
           ]
           @ Option.to_list transition)
      ; state_desc.ret
      ; List state_desc.metas
      ; List state_desc.locs
      ; List state_desc.tops
      ]
  ; config = config_linear
  }
;;

let compile_fact (f : fact) : fact' =
  match f with
  | PathFact _ ->
      (* | PathFact (fid, nsp, path, el) -> (mk_my_fact_name fid ^ ! separator ^ nsp,path :: el, config_linear) *)
      assert false
  | ProcessFact _ -> assert false
  | Fact (fid, nsp, el) ->
      { name = mk_my_fact_name fid ^ !separator ^ nsp
      ; args = Param :: el
      ; config = config_linear
      }
  | ConstantFact (e1, e2) ->
      { name = "Const" ^ !separator; args = [ e1; e2 ]; config = config_persist }
  | GlobalFact (fid, el) ->
      { name = mk_my_fact_name fid; args = el; config = config_linear }
  | ChannelFact (fid, ch, el) ->
      { name = mk_my_fact_name fid; args = ch :: el; config = config_linear }
  | EqFact (e1, e2) ->
      (* linear because we will move this to tag and it wont be used as facts *)
      { name = "Eq" ^ !separator; args = [ e1; e2 ]; config = config_linear }
  | NeqFact (e1, e2) ->
      (* linear because we will move this to tag and it wont be used as facts *)
      { name = "NEq" ^ !separator; args = [ e1; e2 ]; config = config_linear }
  | AccessFact (nsp, param, target, syscall) ->
      { name = "ACP" ^ !separator
      ; args = [ List [ String nsp; param ]; target; String (Option.value ~default:"" syscall) ]
      ; config = config_persist
      }
  | AttackFact (attack, target) ->
      { name = "Attack" ^ !separator
      ; args = [ String attack; target ]
      ; config = config_persist
      }
  | FileFact (nsp, path, e) ->
      { name = "File" ^ !separator ^ nsp
      ; args = [ Param; path; e ]
      ; config = config_linear
      }
  | InitFact el -> { name = "Init" ^ !separator; args = el; config = config_linear }
  | LoopFact (nsp, tid, b) ->
      { name =
          ("Loop"
           ^ !separator
           ^ if b = 0 then "Start" else if b = 1 then "Back" else "Finish")
      ; args = [ List [ String nsp; Param ]; String (Mindex.to_string tid) ]
      ; config = config_linear
      }
  | TransitionFact (nsp, ind, e, p) ->
      { name = "Transition" ^ !separator
      ; args = [ List [ String nsp; p ]; String ind; e ]
      ; config = config_linear
      }
  | InjectiveFact (fid, nsp, id, el) ->
      { name = mk_my_fact_name fid ^ !separator ^ nsp
      ; args = [ Param; FVar id; el ]
      ; config = config_linear
      }
  | FreshFact' e -> { name = "Fr"; args = [ e ]; config = config_linear }
  | FreshFact e -> { name = "Fr"; args = [ FVar e ]; config = config_linear }
  | AccessGenFact (nsp, param) ->
      { name = "ACP" ^ !separator ^ "GEN" ^ !separator
      ; args = [ String nsp; param ]
      ; config = config_persist
      }
  | StateFact { param; state; state_desc; transition } ->
      compile_state_fact param state state_desc transition
;;

(* state consists of its identifier and numbers of variables.
    How to read: *)
type action =
  | ActionReturn of expr
  | ActionAssign of Syntax.variable_desc * expr
  | ActionSeq of action * action
  | ActionAddMeta of int
  | ActionIntro of expr list
  | ActionPopLoc of int
  | ActionPopMeta of int
  | ActionLetTop of expr list

let empty_state_desc = { ret = Unit; metas = []; locs = []; tops = [] }

let map_state_desc f s =
  { ret = f s.ret
  ; metas = List.map f s.metas
  ; locs = List.map f s.locs
  ; tops = List.map f s.tops
  }
;;

let rec action_sem
          (a : action)
          ({ ret = _; metas = meta_lst; locs = loc_lst; tops = top_lst } as state_desc)
  : state_desc
  =
  match a with
  | ActionReturn e -> { state_desc with ret = e }
  | ActionAssign (Top i, e) ->
      { state_desc with ret = Unit; tops = replace_nth top_lst i e }
  | ActionAssign (Loc i, e) ->
      { state_desc with ret = Unit; locs = replace_nth loc_lst i e }
  | ActionAssign _ -> assert false
  | ActionSeq (a, b) -> action_sem b (action_sem a state_desc)
  | ActionAddMeta k ->
      { state_desc with
        ret = Unit
      ; metas = List.map (fun i -> MetaNewVar i) (int_to_list k) @ meta_lst
      }
  | ActionIntro el -> { state_desc with ret = Unit; locs = el @ loc_lst }
  | ActionPopLoc k -> { state_desc with locs = snd (pop_n k loc_lst) }
  | ActionPopMeta k -> { state_desc with metas = snd (pop_n k meta_lst) }
  | ActionLetTop e -> { state_desc with ret = Unit; tops = e @ top_lst }
;;

type transition =
  { transition_id : int
  ; transition_namespace : string (* Seems always same as the model name *)
  ; transition_name : string
  ; transition_from : state
  ; transition_to : state
  ; transition_pre : fact list
  ; transition_post : fact list
  ; transition_action : action list option
  ; transition_state_transition : state_desc * state_desc
  ; transition_label : fact list
  ; transition_is_loop_back : bool
  }

let mk_state_transition_from_action a { meta = meta_num; loc = loc_num; top = top_num } =
  let return_var = get_return_var () in
  let meta_var = List.map (fun i -> MetaVar i) (int_to_list meta_num) in
  let loc_var = List.map (fun i -> LocVar i) (int_to_list loc_num) in
  let top_var = List.map (fun i -> TopVar i) (int_to_list top_num) in
  ( { ret = return_var; metas = meta_var; locs = loc_var; tops = top_var }
  , action_sem a { ret = return_var; metas = meta_var; locs = loc_var; tops = top_var } )
;;

let rec print_expr e =
  match e with
  | FVar e ->
      (* "~"^ *)
      print_expr e
  | Var s -> s
  | MetaVar i -> "meta" ^ !separator ^ string_of_int i
  | LocVar i -> "loc" ^ !separator ^ string_of_int i
  | TopVar i -> "top" ^ !separator ^ string_of_int i
  | Apply (s, el) -> s ^ "(" ^ String.concat ", " (List.map print_expr el) ^ ")"
  | String s -> "\'rab" ^ !separator ^ replace_string '/' !separator s ^ "\'"
  | Integer i -> "\'" ^ string_of_int i ^ "\'"
  | List el ->
      (* < .. > is not a list but a tuple *)
      (match el with
       | [] -> "\'rab" ^ !separator ^ "empty\'"
       | [ e ] -> print_expr e (* XXX Why?!?! *)
       | _ -> "<" ^ String.concat ", " (List.map print_expr el) ^ ">")
  | One -> "%1"
  | Int v -> "%" ^ v
  | AddOne e -> print_expr e ^ " %+ %1"
  | Unit -> "\'rab" ^ !separator ^ "unit\'"
  | MetaNewVar i -> "new" ^ !separator ^ string_of_int i
  | Param -> !fresh_param
;;

let rec string_of_action = function
  | ActionReturn e -> Printf.sprintf "return %s" (print_expr e)
  | ActionAssign (vd, e) -> Printf.sprintf "%s = %s" (Syntax.string_of_variable_desc vd) (print_expr e)
  | ActionSeq (a1, a2) -> string_of_action a1 ^ "; " ^ string_of_action a2
  | ActionAddMeta n -> Printf.sprintf "addMeta %d" n
  | ActionIntro es -> Printf.sprintf "intro [%s]" (String.concat "; " (List.map print_expr es))
  | ActionPopLoc n -> Printf.sprintf "popLoc %d" n
  | ActionPopMeta n -> Printf.sprintf "popMeta %d" n
  | ActionLetTop es -> Printf.sprintf "letTop [%s]" (String.concat "; " (List.map print_expr es))

let mk_state_fact ?param st desc transition : fact =
  StateFact { param; state = st; state_desc = desc; transition }
;;

let mk_transition_expr = function
  | `Loop -> AddOne (Int ("v" ^ !separator))
  | `Initial -> One
  | `None -> Int ("v" ^ !separator)
;;

type 'fact rule_ =
  { name : string
  ; role : string
  ; pre : 'fact list
  ; label : 'fact list
  ; post : 'fact list
  }

let compile_rule_ r =
  { r with
    pre = List.map compile_fact r.pre
  ; label = List.map compile_fact r.label
  ; post = List.map compile_fact r.post
  }
;;

type rule =
  | Rule of fact rule_
  | Comment of string

type model =
  { model_name : string
  ; model_states : state list
  ; model_transitions : transition list
  ; model_init_rules : rule list
  ; model_init_state : state
  ; model_transition_id_max : int
  ; model_type : string
  }

let _add_rule (mo : model) (a, b, c, d, e) =
  { mo with
    model_init_rules =
      Rule { name = a; role = b; pre = c; label = d; post = e } :: mo.model_init_rules
  }
;;

let add_state m s = { m with model_states = s :: m.model_states }

let initial_state ~namespace =
  { state_namespace = namespace
  ; state_index = Mindex.zero
  ; state_vars = { meta = 0; loc = 0; top = 0 }
  }
;;

let initial_model ~namespace ~typ =
  let st = initial_state ~namespace in
  { model_name = namespace
  ; model_states = [ st ]
  ; model_transitions = []
  ; model_type = typ
  ; model_init_rules = []
  ; model_init_state = st
  ; model_transition_id_max = 0
  }
;;

let _initial_attacker_model ~namespace ~typ =
  let st = initial_state ~namespace in
  ( { model_name = namespace
    ; model_states = [ st ]
    ; model_transitions = []
    ; model_type = typ
    ; model_init_rules =
        [ Rule
            { name = "Init" ^ namespace
            ; role = namespace
            ; pre = [ AttackFact (namespace, MetaNewVar 0) ]
            ; label = []
            ; post =
                [ mk_state_fact
                    st
                    { ret = Unit; metas = [ MetaNewVar 0 ]; locs = []; tops = [] }
                    None
                ]
            }
        ]
    ; model_init_state = st
    ; model_transition_id_max = 0
    }
  , st )
;;

let add_transition m t =
  assert (m.model_name = t.transition_namespace);
  { m with
    model_transitions = t :: m.model_transitions
  ; model_transition_id_max = m.model_transition_id_max + 1
  }
;;

(* tamarin lemma *)
type lemma =
  | PlainLemma of { name : string; desc : string }
  | ReachabilityLemma of
      { name : string
      ; global_variables : fact list
      ; facts : fact list
      }
  | CorrespondenceLemma of
      { name : string
      ; fresh_variables : string list
      ; premise : (fact list * fact)
      ; conclusion : (fact list * fact)
      }

type tamarin =
  { signature : signature
  ; models : model list
  ; rules : rule list
  ; lemmas : lemma list
  }

let add_fun tamarin f (* name * arity *) =
  let signature =
    { tamarin.signature with functions = f :: tamarin.signature.functions }
  in
  { tamarin with signature }
;;

let add_const tamarin c =
  let signature =
    { tamarin.signature with functions = (c, 0) :: tamarin.signature.functions }
  in
  { tamarin with signature }
;;

let add_eqn tamarin eq =
  let signature =
    { tamarin.signature with equations = eq :: tamarin.signature.equations }
  in
  { tamarin with signature }
;;

let add_model t m = { t with models = m :: t.models }
let add_rule t (r : _ rule_) = { t with rules = Rule r :: t.rules }

let add_comment t s = { t with rules = Comment s :: t.rules }
let add_lemma t lem = { t with lemmas = lem :: t.lemmas }

let empty_tamarin : tamarin =
  { signature = empty_signature; models = []; rules = []; lemmas = [] }
;;

let print_signature { functions = fns; equations = eqns } =
  let print_functions fns =
    (if List.length fns = 0 then "" else "functions: ")
    ^ String.concat ", " (List.map (fun (f, ar) -> f ^ "/" ^ string_of_int ar) fns)
    ^ "\n"
  in
  let print_equations eqns =
    (if List.length eqns = 0 then "" else "equations: ")
    ^ String.concat
        ", "
        (List.map (fun (e1, e2) -> print_expr e1 ^ "=" ^ print_expr e2) eqns)
    ^ "\n"
  in
  print_functions fns ^ print_equations eqns
;;

let print_fact2 { name; args; config } =
  (if config.is_persist then "!" else "")
  ^ name
  ^ "("
  ^ String.concat ", " (List.map print_expr args)
  ^ ")"
;;

let print_fact fact =
  print_fact2 fact ^
  match fact.config.priority with
  | 0 -> "[-,no_precomp]"
  | 1 -> "[-]"
  | 2 -> ""
  | 3 -> "[+]"
  | _ -> assert false
;;

let transition_to_rule (tr : transition) : rule =
  let name =
    tr.transition_namespace
    ^ !separator
    ^ tr.transition_name
    ^ !separator
    ^ state_index_to_string_aux tr.transition_from
    ^ !separator
    ^ state_index_to_string_aux tr.transition_to
    ^ !separator
    ^ string_of_int tr.transition_id
  in
  let pre = tr.transition_pre in
  let post = tr.transition_post in
  let label = tr.transition_label in
  let initial_state_fact =
    mk_state_fact tr.transition_from (fst tr.transition_state_transition) None
  in
  let final_state_fact =
    mk_state_fact tr.transition_to (snd tr.transition_state_transition) None
  in
  Rule
    { name
    ; role = tr.transition_namespace
    ; pre = initial_state_fact :: pre
    ; label
    ; post = final_state_fact :: post
    }
;;

let transition_to_transition_rule (tr : transition) : rule =
  let name =
    tr.transition_namespace
    ^ !separator
    ^ tr.transition_name
    ^ !separator
    ^ state_index_to_string_aux tr.transition_from
    ^ !separator
    ^ state_index_to_string_aux tr.transition_to
    ^ !separator
    ^ string_of_int tr.transition_id
  in
  let pre = tr.transition_pre in
  let post = tr.transition_post in
  let label =
    TransitionFact
      ( tr.transition_namespace
      , Mindex.to_string tr.transition_from.state_index (* tr.transition_id *)
      , Int ("v" ^ !separator)
      , Param )
    :: tr.transition_label
  in
  let initial_state_fact =
    mk_state_fact
      tr.transition_from
      (fst tr.transition_state_transition)
      (Some (mk_transition_expr `None))
  in
  let final_state_fact =
    mk_state_fact
      tr.transition_to
      (snd tr.transition_state_transition)
      (Some (mk_transition_expr (if tr.transition_is_loop_back then `Loop else `None)))
  in
  Rule
    { name
    ; role = tr.transition_namespace
    ; pre = initial_state_fact :: pre
    ; label
    ; post = final_state_fact :: post
    }
;;

let print_list sep f =
  Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf sep) f

let print_rule_aux ~dev ppf { name; role; pre; label; post } =
  let open Format in
  fprintf ppf "rule %s%s@.  : [ @[<v>%a@] ]@.    --[ @[<v>%a@] ]->@.    [ @[<v>%a@] ]"
    name
    (match role with "" -> "" | _ when not dev -> "" | _ -> Printf.sprintf "[role=\"%s\"]" role)
    (print_list ",@ " (fun ppf f -> fprintf ppf "%s" (print_fact f)))
    pre
    (print_list ",@ " (fun ppf f -> fprintf ppf "%s" (print_fact2 f)))
    label
    (print_list ",@ " (fun ppf f -> fprintf ppf "%s" (print_fact2 f)))
    post

let print_comment s = "\n// " ^ s ^ "\n\n"

let print_rule r ~dev =
  match r with
  | Rule r -> Format.asprintf "%a@." (print_rule_aux ~dev) (compile_rule_ r)
  | Comment s -> print_comment s
;;

let print_transition (tr : transition) ~dev =
  let r = transition_to_rule tr in
  print_rule r ~dev
;;

let print_model m ~dev =
  (* initialization rule  *)
  String.concat "\n"
  @@ List.map (fun r -> print_rule r ~dev) m.model_init_rules
    @ List.map (fun t -> print_transition t ~dev) m.model_transitions
;;

let print_transition_transition_rule (tr : transition) ~dev =
  let r = transition_to_transition_rule tr in
  print_rule r ~dev
;;

let print_model_transition_rule m ~dev =
  (* initialization rule  *)
  String.concat "\n"
  @@ List.map (fun r -> print_rule r ~dev) m.model_init_rules
     @ List.map (fun t -> print_transition_transition_rule t ~dev) m.model_transitions
;;

let print_lemma lemma =
  match lemma with
  | PlainLemma {name; desc} -> "\nlemma " ^ name ^ " : " ^ desc
  | ReachabilityLemma {name= l; global_variables= gv; facts} ->
      let var1 = List.concat_map global_fact_collect_vars facts in
      let var2 = List.concat_map global_fact_collect_vars gv in
      let var = List.sort_uniq compare (var1 @ var2) in
      "\nlemma "
      ^ l
      ^ " : exists-trace \"Ex "
      ^ String.concat " " (List.map print_expr var)
      ^ String.concat
          " "
          (fst
             (List.fold_left
                (fun (times, n) _ ->
                   (" #time" ^ !separator ^ string_of_int n) :: times, n + 1)
                ([], 0)
                facts))
      ^ String.concat
          " "
          (fst
             (List.fold_left
                (fun (times, n) _ ->
                   (" #label_time" ^ !separator ^ string_of_int n) :: times, n + 1)
                ([], 0)
                gv))
      ^ " . "
      ^ String.concat
          " & "
          (fst
             (List.fold_left
                (fun (s, n) g ->
                   ( (print_fact (compile_fact g)
                      ^ "@#label_time"
                      ^ !separator
                      ^ string_of_int n)
                     :: s
                   , n + 1 ))
                ([], 0)
                gv))
      ^ (if List.length gv = 0 then "" else " & ")
      ^ String.concat
          " & "
          (fst
             (List.fold_left
                (fun (s, n) g ->
                   ( (print_fact (compile_fact g) ^ "@#time" ^ !separator ^ string_of_int n
                     )
                     :: s
                   , n + 1 ))
                ([], 0)
                facts))
      ^ " \""
  | CorrespondenceLemma {name=l; fresh_variables= _vl; premise= (gva, a); conclusion= (gvb, b)} ->
      let var1 = List.flatten (List.map global_fact_collect_vars [ a ]) in
      let var2 = List.flatten (List.map global_fact_collect_vars gva) in
      let vara = List.sort_uniq compare (var1 @ var2) in
      let var1 = List.flatten (List.map global_fact_collect_vars [ b ]) in
      let var2 = List.flatten (List.map global_fact_collect_vars gvb) in
      let varb = List.filter (fun v -> not @@ List.mem v vara) @@ List.sort_uniq compare (var1 @ var2) in
      "\nlemma "
      ^ l
      ^ " : all-traces \"All "
      ^ String.concat " " (List.map print_expr vara)
      ^ String.concat
          " "
          (fst
             (List.fold_left
                (fun (times, n) _ ->
                   (" #label_time" ^ !separator ^ string_of_int n) :: times, n + 1)
                ([], 0)
                gva))
      ^ " #time"
      ^ !separator
      ^ "1 . "
      ^ String.concat
          " & "
          (fst
             (List.fold_left
                (fun (s, n) g ->
                   ( (print_fact (compile_fact g)
                      ^ "@#label_time"
                      ^ !separator
                      ^ string_of_int n)
                     :: s
                   , n + 1 ))
                ([], 0)
                gva))
      ^ (if List.length gva = 0 then "" else " & ")
      ^ print_fact (compile_fact a)
      ^ "@#time"
      ^ !separator
      ^ "1 ==> Ex "
      ^ String.concat " " (List.map print_expr varb)
      ^ String.concat
          " "
          (fst
             (List.fold_left
                (fun (times, n) _ ->
                   (" #label__time" ^ !separator ^ string_of_int n) :: times, n + 1)
                ([], 0)
                gvb))
      ^ " #time"
      ^ !separator
      ^ "2 . "
      ^ String.concat
          " & "
          (fst
             (List.fold_left
                (fun (s, n) g ->
                   ( (print_fact (compile_fact g)
                      ^ "@#label__time"
                      ^ !separator
                      ^ string_of_int n)
                     :: s
                   , n + 1 ))
                ([], 0)
                gvb))
      ^ (if List.length gvb = 0 then "" else " & ")
      ^ print_fact (compile_fact b)
      ^ "@#time"
      ^ !separator
      ^ "2 & #time"
      ^ !separator
      ^ "2 < #time"
      ^ !separator
      ^ "1 \""
;;

let print_tamarin
      { signature = si; models = mo_lst; rules = r_lst; lemmas = lem_lst }
      ~dev
      ~print_transition_label
  =
  "theory rabbit\n\nbegin\nbuiltins: natural-numbers\n\n"
  (* print signature *)
  ^ print_comment "The signature of our model:\n\n"
  ^ print_signature si
  (* print initializing rules *)
  ^ print_comment "Initializing the gloval constants and access policy rules:\n\n"
  ^ String.concat "\n" (List.map (fun r -> print_rule r ~dev) (List.rev r_lst))
  (* print models  *)
  ^ String.concat
      "\n"
      (List.map
         (fun m ->
            print_comment ("Model:  " ^ m.model_name ^ "\n")
            ^ (if print_transition_label then print_model_transition_rule else print_model)
                m
                ~dev)
         (List.rev mo_lst))
  (* default restrictions *)
  ^ "\nrestriction Init"
  ^ !separator
  ^ " : \" All x #i #j . Init"
  ^ !separator
  ^ "(x) @ #i & Init"
  ^ !separator
  ^ "(x) @ #j ==> #i = #j \"\n"
  ^ "restriction Equality_rule: \"All x y #i. Eq"^ !separator ^"(x,y) @ #i ==> x = y\"\n"
  ^ "restriction NEquality_rule: \"All x #i. NEq"^ !separator ^"(x,x) @ #i ==> F\"\n\n"
  ^ (if !Config.tag_transition
     then
       "lemma AlwaysStarts"
       ^ !separator
       ^ "[reuse,use_induction]:\n      \"All x p #i. Loop"
       ^ !separator
       ^ "Back(x, p) @i ==> Ex #j. Loop"
       ^ !separator
       ^ "Start(x, p) @j & j < i\"\n\n"
       ^ "lemma AlwaysStartsWhenEnds"
       ^ !separator
       ^ "[reuse,use_induction]:\n      \"All x p #i. Loop"
       ^ !separator
       ^ "Finish(x, p) @i ==> Ex #j. Loop"
       ^ !separator
       ^ "Start(x, p) @j & j < i\"\n\n"
       ^ "lemma TransitionOnce"
       ^ !separator
       ^ "[reuse,use_induction]:\n      \"All x p %i #j #k . Transition"
       ^ !separator
       ^ "(x, p, %i) @#j &\n        Transition"
       ^ !separator
       ^ "(x, p, %i) @ #k ==> #j = #k\"\n\n"
       (* (String.concat (List.map (fun mo ->
        "lemma transition"^ ! separator ^ mo.model_name ^ "[reuse,use_induction]:\n
        \"All x p %i #j #k . Transition"^ ! separator ^ mo.model_name ^ "(x, %i, p) @#j &
        Transition"^ ! separator ^ mo.model_name ^ "(x, %i, p) @ #k ==> #j = #k\"\n"
        ) (List.rev mo_lst)) "\n") *)
     else "")
  (* print lemmas *)
  ^ List.fold_left (fun l lem -> l ^ print_lemma lem) "" lem_lst
  ^ "\nend\n"
;;

let string_of_fact f = print_fact @@ compile_fact f
