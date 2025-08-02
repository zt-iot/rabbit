type transition = One | Var | Inc

let string_of_transition = function
  | One -> "%1"
  | Var -> "%v"
  | Inc -> "%v %+ %1"

type expr =
  | Unit
  | String of string
  | Integer of int
  | Ident of Ident.t
  | Tuple of expr list
  | Apply of Ident.t * expr list
  | Index of Sem.Index.t
  | Transition of transition

let rec vars_of_expr e =
  match e with
  | Unit | String _ | Integer _ | Index _ -> Ident.Set.empty
  | Ident id -> Ident.Set.singleton id
  | Tuple es | Apply (_, es) -> List.fold_left Ident.Set.union Ident.Set.empty @@ List.map vars_of_expr es
  | Transition _ -> Ident.Set.empty

let rec string_of_expr = function
  | Unit -> "'unit'"
  | String s -> "'" ^ s ^ "'"
  | Integer i -> "\'" ^ string_of_int i ^ "\'"
  | Ident id -> Ident.to_string id
  | Tuple [] -> assert false
  | Tuple [_] -> assert false
  | Tuple es -> "<" ^ String.concat ", " (List.map string_of_expr es) ^ ">"
  | Apply (s, el) -> Ident.to_string s ^ "(" ^ String.concat ", " (List.map string_of_expr el) ^ ")"
  | Index i -> "'index:" ^ Sem.Index.to_string i ^ "'"
  | Transition tr -> string_of_transition tr

let expr_of_channel id = String ("chan:" ^ Ident.to_string id)

type signature =
  { functions : (Ident.t * int) list
  ; equations : (expr * expr) list
  }

let print_list sep f =
  Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf sep) f

(*
functions: true/0, pk/1, enc/2, sign/2, dec/2, fst/1, snd/1, verify/3, h/1
equations: fst(<loc__1, loc__0>)=loc__1,
           snd(<loc__1, loc__0>)=loc__0,
           dec(enc(loc__1, loc__0), loc__0)=loc__1,
           verify(sign(loc__1, loc__0), loc__1, pk(loc__0))=true()
*)
let print_signature ppf signature =
  let open Format in
  if signature.functions <> [] then
    fprintf ppf "functions: %a@."
      (print_list ", " (fun ppf (id, arity) -> fprintf ppf "%s/%d" (Ident.to_string id) arity))
      signature.functions;
  if signature.equations <> [] then
    fprintf ppf "equations: %a@."
      (print_list ", " (fun ppf (e1, e2) -> fprintf ppf "%s=%s" (string_of_expr e1) (string_of_expr e2)))
      signature.equations

type fact =
  | Channel of
      { channel : expr
      ; name : Name.t
      ; args : expr list
      } (** Channel fact [ch :: name(args)] *)
  | Out of expr (** Attacker fact: Out *)
  | In of expr (** Attacker fact: In *)
  | Plain of Name.t * expr list
  | Eq of expr * expr
  | Neq of expr * expr
  | File of
      { path : expr
      ; contents : expr
      } (** File fact [path.contents] *)
  | Global of Name.t * expr list

  (* New additions at Sem level *)

  | Fresh of Ident.t
  | Structure of
      { name : Name.t
      ; proc_id : Subst.proc_id
      ; param : Subst.param_id option
      ; address : expr
      ; args : expr list
      } (** Structure fact [name(process, address, args)] *)
  | Loop of
      { mode : Typed.loop_mode
      ; proc_id : Subst.proc_id
      ; param : Subst.param_id option
      ; index : Sem.Index.t
      }
  | Access of
      { proc_id: Subst.proc_id
      ; param : Subst.param_id option
      ; channel: expr (** channel or file *)
      ; syscall: Ident.t option (** system call performs this access *)
      }

  (* New additions at Spthy level *)
  | Const of { id : Ident.t; param : expr option; value : expr }
  | Initing_const of { id : Ident.t; param : Subst.param_id option } (* XXX init *)
  | Initing_proc_group of Subst.proc_group_id * Subst.param_id option (* XXX init *)
  | Initing_proc_access of { proc_id : Subst.proc_id; param: Subst.param_id option } (* XXX init *)
  | Inited_proc_group of Subst.proc_group_id * Subst.param_id option (* to bind param *)
  | State of
      { proc_id : Subst.proc_id
      ; param : Subst.param_id option
      ; index : Sem.Index.t
      ; mapping : (Ident.t * expr) list
      ; transition : transition option
      }
  | Transition of
      { proc_id : Subst.proc_id
      ; param: Subst.param_id option
      ; source : Sem.Index.t
      ; transition : transition option }

type fact_config =
  { persist : bool
  (* ; priority : int; Currently this is not used in tamarin.ml *)
  }

let config_persist = { persist= true }
let config_linear = { persist= false }

type fact' =
  { name : string
  ; args : expr list
  ; config : fact_config
  }

let fact' f : fact' =
  let with_param (param : Subst.param_id option) =
    match param with
    | None -> []
    | Some p -> [Ident (p :> Ident.t)]
  in
  let pid x (param : Subst.param_id option) =
    match param with
    | None -> x
    | Some p -> Tuple [x; Ident (p :> Ident.t)]
  in
  let fix_name = String.capitalize_ascii in
  match f with
  | Channel { channel; name; args } ->
      { name= fix_name name; args= channel :: args; config= config_linear }
  | Out e ->
      { name= "Out"; args= [e]; config= config_linear }
  | In e ->
      { name= "In"; args= [e]; config= config_linear }
  | Plain (name, args) ->
      { name= fix_name name; args; config= config_linear }
  | Eq (e1, e2) ->
      (* linear because we will move this to tag and it wont be used as facts *)
      { name = "Eq"; args = [ e1; e2 ]; config = config_linear }
  | Neq (e1, e2) ->
      (* linear because we will move this to tag and it wont be used as facts *)
      { name = "NEq"; args = [ e1; e2 ]; config = config_linear }
  | File { path; contents } ->
      { name = "File" (* namespace? *); args= [ (* param?; *) path; contents ]; config = config_linear }

  | Global (name, args) ->
      { name= fix_name name; args; config = config_linear }
  | Fresh id ->
      { name= "Fr"; args= [Ident id]; config= config_linear }
  | Structure { name; proc_id; param; address; args } ->
      { name= "Structure_" ^ Ident.to_string (proc_id :> Ident.t) ^ "_" ^ name
      ; args =
          (match param with None -> [] | Some p -> [Ident (p :> Ident.t)])
          @ address :: args
      ; config = config_linear }
  | Loop { mode; proc_id; param; index } ->
      { name = "Loop_" ^ Typed.string_of_loop_mode mode
      ; args = [ pid (String (Ident.to_string (proc_id :> Ident.t))) param; Index index ]
      ; config = config_linear
      }
  | Const { id; param; value } ->
      { name= "Const"
      ; args =
          (match param with
           | None -> [String (Ident.to_string id); value]
           | Some p -> [ Tuple [String (Ident.to_string id); p]; value ])
      ; config = config_persist
      }
  | Initing_const { id; param } ->
      { name= "Init"
      ; args= [ Tuple (String "Const" :: String (Ident.to_string id) :: with_param param) ]
      ; config= config_linear }
  | Initing_proc_group (id, None) ->
      { name= "Init"
      ; args= [ Tuple [String "Proc_group"; String (Ident.to_string (id :> Ident.t))] ]
      ; config= config_linear }
  | Initing_proc_group (id, Some param) ->
      { name= "Init"
      ; args= [ Tuple [String "Proc_group";
                       Tuple [ String (Ident.to_string (id :> Ident.t));
                               Ident (param :> Ident.t) ] ] ]
      ; config= config_linear }
  | Initing_proc_access { proc_id; param } ->
      { name= "Init"
      ; args= [ Tuple (String "Proc_access" :: String (Ident.to_string (proc_id :> Ident.t)) :: with_param param) ]
      ; config= config_linear }
  | Inited_proc_group (id, param) ->
      { name= "Inited_proc_group"
      ; args= String (Ident.to_string (id :> Ident.t)) :: with_param param
      ; config= config_persist }
  | Access { proc_id; param; channel; syscall } ->
      { name= "ACP"
      ; args= [
          pid (String (Ident.to_string (proc_id :> Ident.t))) param;
          channel;
          String (match syscall with None -> "." | Some id -> Ident.to_string id)
        ]
      ; config= config_persist
      }
  | State { proc_id; param; index; mapping; transition } ->
      { name = "State_" ^ Ident.to_string (proc_id :> Ident.t)
      ; args = [ (match
                   Index index
                   :: Option.to_list (Option.map (fun p -> Ident (p : Subst.param_id :> Ident.t)) param)
                   @ Option.to_list (Option.map (fun x -> (Transition x : expr)) transition)
                  with
                  | [] -> assert false
                  | [x] -> x
                  | xs -> Tuple xs
                 );
                 match mapping with
                 | [] -> assert false
                 | [_id, e] -> e
                 | _ -> Tuple (List.map (fun (_id,e) -> e) mapping)]
      ; config = config_linear
      }
  | Transition { proc_id; param; source; transition } ->
      { name= "Transition"
      ; args = [ pid (String (Ident.to_string (proc_id :> Ident.t))) param
               ; Index source ]
               @ Option.to_list (Option.map (fun t -> (Transition t : expr)) transition)
      ; config = config_linear }

let string_of_fact' { name; args; config } =
  (if config.persist then "!" else "")
  ^ name
  ^ "("
  ^ String.concat ", " (List.map string_of_expr args)
  ^ ")"

let string_of_fact f = string_of_fact' @@ fact' f

(* It is a monad!

   Please bear with the use of the monad; it saves lots of LoCs to track down
   constant dependencies extracted during the compilation stages.
*)
type 'a compiled = { deps : fact list; result : 'a }

(* Monad bind *)
let (let*) x f =
  let { deps; result } = f x.result in
  { deps= x.deps @ deps; result }

(* Monad map *)
let (let+) x f = { x with result= f x.result }

let return ?(deps = []) result = { deps; result }

let rec mapM f = function
  | [] -> return []
  | x::xs ->
      let* y = f x in
      let+ ys = mapM f xs in
      y :: ys

let rec compile_expr (e : Typed.expr) : expr compiled =
  match e.desc with
  | Boolean _ -> assert false
  | Float _ -> assert false
  | Integer z -> return @@ Integer z
  | Ident { id; param= None; desc= Const false } ->
      return ~deps:[Const { id; param= None; value= Ident id }] @@ Ident id
  | Ident { id; param= Some p; desc= Const true } ->
      (* [c<p>] and [c<(p,p)>] must be compiled to different facts and identifiers!

         [c<p>]     => [Const { id; param= Some p;              value= Ident c__1}, c__1]
         [c<(p,p)>] => [Const { id; param= Some (Tuple [p; p]); value= Ident c__2}, c__2]
      *)
      let id' = Ident.local (fst id) in
      let* p = compile_expr p in
      return ~deps:[Const { id; param= Some p; value= Ident id' }] @@ Ident id'
  | Ident { id; param= None; desc= ExtConst } ->
      return @@ Apply (id, [])
  | Ident { id; param= None; desc= Var | Param | Rho } ->
      return @@ Ident id
  | Ident { id; param= None; desc= Channel (false, _cty) } ->
      return @@ expr_of_channel id
  | Ident { id; param= Some p; desc= Channel (true, _cty) } ->
      let* p = compile_expr p in
      return @@ Tuple [expr_of_channel id; p]
  | Ident { id; param= None; desc } ->
      Format.eprintf "Error %s : %t@." (Ident.to_string id) (Env.print_desc desc);
      assert false
  | Ident { id; param= Some _p; desc } ->
      Format.eprintf "Error %s : %t@." (Ident.to_string id) (Env.print_desc desc);
      assert false
  | String s ->
      return @@ String ("str:" ^ s)
  | Apply (f, es) ->
      let+ es = mapM compile_expr es in
      Apply (f, es)
  | Tuple es ->
      let+ es = mapM compile_expr es in
      Tuple es
  | Unit -> return Unit

let expr_of_chan_arg ({ channel; parameter; _ } : Typed.chan_arg) =
  match parameter with
  | None ->
      return @@ expr_of_channel channel
  | Some (Some e) ->
      let* e = compile_expr e in
      return @@ Tuple [expr_of_channel channel; e]
  | Some None ->
      return @@ Tuple [expr_of_channel channel; Ident (Ident.local "any")]

let compile_signature (sg : Sem.signature) =
  let compile_expr e =
    let { deps; result= e } = compile_expr e in
    assert (deps = []);
    e
  in
  { functions = sg.functions
  ; equations = List.map (fun (e1,e2) -> compile_expr e1, compile_expr e2) sg.equations
  }

let compile_fact (f : Sem.fact) : fact compiled =
  match f.desc with
  | Channel { channel; name; args } ->
      let* channel = compile_expr channel in
      let+ args = mapM compile_expr args in
      Channel { channel; name; args }
  | Out e ->
      let+ e = compile_expr e in
      Out e
  | In e ->
      let+ e = compile_expr e in
      In e
  | Plain (n, es) ->
      let+ es = mapM compile_expr es in
      Plain (n, es)
  | Eq (e1, e2) ->
      let* e1 = compile_expr e1 in
      let+ e2 = compile_expr e2 in
      Eq (e1, e2)
  | Neq (e1, e2) ->
      let* e1 = compile_expr e1 in
      let+ e2 = compile_expr e2 in
      Neq (e1, e2)
  | File { path; contents } ->
      let* path = compile_expr path in
      let+ contents = compile_expr contents in
      File { path; contents }
  | Global (n, es) ->
      let+ es = mapM compile_expr es in
      Global (n, es)
  | Fresh id -> return @@ Fresh id
  | Structure { name; proc_id; param; address; args } ->
      let* address = compile_expr address in
      let+ args = mapM compile_expr args in
      Structure { name; proc_id; param; address; args }
  | Loop { mode; proc_id; param; index } -> return @@ Loop { mode; proc_id; param; index }
  | Access { proc_id; param; channel; syscall } ->
      let+ channel = compile_expr channel in
      Access { proc_id; param; channel; syscall }

let compile_facts (fs : Sem.fact list) : fact list compiled =
  let fs_f_list = List.map compile_fact fs in
  let deps = List.concat_map (fun x -> x.deps) fs_f_list in
  let fs = List.map (fun x -> x.result) fs_f_list in
  { deps; result= fs }

type lemma =
  | Plain of string
  | Reachability of fact list compiled
  | Correspondence of
      { premise : fact compiled
      ; conclusion : fact compiled
      }

let vars_of_global_fact = function
  | Global (_name, es) ->
      List.fold_left Ident.Set.union Ident.Set.empty @@ List.map vars_of_expr es
  | Const { id; param; value } ->
      Ident.Set.add id
      @@ Ident.Set.union
        (Option.value ~default:Ident.Set.empty @@ Option.map vars_of_expr param)
        (vars_of_expr value)
  | _ -> assert false

let print_lemma ppf (id, lemma) =
  let open Format in
  match lemma with
  | Plain desc ->
      fprintf ppf "lemma %s :@.  %s@." (Ident.to_string id) desc
  | Reachability {deps= gv; result= facts} ->
      let vars = List.fold_left Ident.Set.union Ident.Set.empty @@ List.map vars_of_global_fact (gv @ facts) in
      fprintf ppf "lemma %s :@." (Ident.to_string id);
      fprintf ppf "  exists-trace@.    \"Ex ";
      fprintf ppf "%s" @@ String.concat " " (List.map Ident.to_string (Ident.Set.elements vars));
      fprintf ppf "%s" @@ String.concat " "
        (List.mapi (fun n _ -> " #time_" ^ string_of_int n) facts);
      fprintf ppf "%s" @@ String.concat " "
        (List.mapi (fun n _ -> " #label_time_" ^ string_of_int n) gv);
      fprintf ppf " . ";
      fprintf ppf "%s" @@ String.concat " & "
        (List.mapi (fun n g -> string_of_fact g ^ "@#label_time_" ^ string_of_int n) gv
         @ List.mapi (fun n fact -> string_of_fact fact ^ "@#time_" ^ string_of_int n) facts);
      fprintf ppf " \"@.@."

  | Correspondence {premise; conclusion} ->
      let vars_of_correspondnce_unit c =
        List.fold_left Ident.Set.union Ident.Set.empty
        @@ List.map vars_of_global_fact
        @@ c.result :: c.deps
      in
      let vara = vars_of_correspondnce_unit premise in
      let varb = Ident.Set.diff (vars_of_correspondnce_unit conclusion) vara in
      fprintf ppf "lemma %s :@." (Ident.to_string id);
      fprintf ppf "  all-traces@.    \"All ";
      fprintf ppf "%s" @@ String.concat " " (List.map Ident.to_string (Ident.Set.elements vara));
      fprintf ppf "%s" @@ String.concat " "
        (List.mapi (fun n _ -> " #label_time_" ^ string_of_int n) premise.deps);
      fprintf ppf " #time_1 . ";
      fprintf ppf "%s" @@ String.concat " & "
        (List.mapi (fun n g ->
             string_of_fact g
             ^ "@#label_time_" ^ string_of_int n) premise.deps);
      if premise.deps <> [] then fprintf ppf " & ";
      fprintf ppf "%s" @@ string_of_fact premise.result;
      fprintf ppf "@@#time_1 ==> Ex ";
      fprintf ppf "%s" @@ String.concat " " (List.map Ident.to_string (Ident.Set.elements varb));
      fprintf ppf "%s" @@ String.concat " "
        (List.mapi (fun n _ -> " #label_time_" ^ string_of_int n) conclusion.deps);
      fprintf ppf " #time_2 . ";
      fprintf ppf "%s" @@ String.concat " & "
        (List.mapi (fun n g ->
             string_of_fact g
             ^ "@#label_time_" ^ string_of_int n) conclusion.deps);
      if conclusion.deps <> [] then fprintf ppf " & ";
      fprintf ppf "%s" @@ string_of_fact conclusion.result;
      fprintf ppf "@@#time_2 & #time_2 < #time_1 \"@."


let compile_lemma (lem : Typed.lemma) : lemma =
  match lem.desc with
  | Plain s -> Plain s
  | Reachability { fresh=_; facts } ->
      let facts = List.map Sem.fact_of_typed facts in
      Reachability (compile_facts facts)
  | Correspondence { fresh=_; premise; conclusion } ->
      let premise = compile_fact @@ Sem.fact_of_typed premise in
      let conclusion = compile_fact @@ Sem.fact_of_typed conclusion in
      Correspondence { premise; conclusion }

type rule =
  { id : Ident.t
  ; role : Ident.t option (* proc_id or proc_id or both? *)
  ; pre : fact list
  ; label : fact list
  ; post : fact list
  ; comment : string option
  }

let print_rule ppf rule =
  let open Format in
  Option.iter (fprintf ppf "// %s@.") rule.comment;
  fprintf ppf "rule %s%s@.  : [ @[<v>%a@] ]@.    --[ @[<v>%a@] ]->@.    [ @[<v>%a@] ]"
    (Ident.to_string rule.id)
    (match rule.role with None -> "" | Some id -> Printf.sprintf "[role=\"%s\"]" (Ident.to_string id))
    (print_list ",@ " (fun ppf f -> fprintf ppf "%s" (string_of_fact f)))
    rule.pre
    (print_list ",@ " (fun ppf f -> fprintf ppf "%s" (string_of_fact f)))
    rule.label
    (print_list ",@ " (fun ppf f -> fprintf ppf "%s" (string_of_fact f)))
    rule.post

(* move equality and inequality facts from precondition to tags because Tamarin cannot handle
   (N)Eq fact generation rules correctly for fresh values *)
let facts_of_edge (e : Sem.edge) =
  let pre_eq_neq, pre_others =
    List.partition (function
        | ({ desc= (Eq _ | Neq _); _ } : Sem.fact) -> true
        | _ -> false) e.pre
  in
  pre_others,
  e.tag @ pre_eq_neq,
  e.post

(*
rule Client_ta__guarded_guarded_...._____4_____4__0_1__90[role="Client_ta"]
  : [State__Client_ta(<'rab_____4', param, %v__>,
                      return__var__8,
                      'rab__', 'rab__', t__0__8),
     !ACP__(<'rab__Client_ta', param>, 'rab__rpc', 'rab__'),
     Fr(n__0__15),
     ...]
  --[Transition__(<'rab__Client_ta', param>, 'rab_____4', %v__),
     Eq__(n__0__23, n__0__30),
     ...]
  ->[State__Client_ta(<'rab_____4__0_1', param, %v__>,
                      'rab__',
                      <n__0__8, n__1__8, n__2__8>,
                      'rab__',
                      t__0__8),
     File__Client_ta(param, loc__0, n__0__14),
     Returned('rab__rpc', sign(n__1__8, dec(n__0__23, t__0__8)))
    ]
*)
let rule_of_edge (proc_id : Subst.proc_id) (param : Subst.param_id option) (edge : Sem.edge) =
  let role = Some (proc_id :> Ident.t) in
  let state_pre : fact =
    let vars = edge.update.rho :: edge.source_vars in
    let mapping = List.map (fun id -> id, Ident id) vars in
    let transition = if !Config.tag_transition then Some Var else None in
    State { proc_id; param; index= edge.source; mapping; transition }
  in
  let { deps= post_consts; result= state_post } =
    let* mapping =
      mapM (fun id ->
          let* res =
            match List.assoc_opt id edge.update.items with
            | None -> return @@ Ident id (* no change *)
            | Some (New e | Update e) -> compile_expr e
            | Some Drop -> assert false
          in
          return (id, res)
        ) edge.target_vars
    in
    let+ mapping =
      let* rho_expr = compile_expr edge.update.register in
      return @@ (edge.update.rho, rho_expr) :: mapping
    in
    let transition =
      if !Config.tag_transition then
        if edge.loop_back then Some Inc
        else Some Var
      else None in
    State { proc_id; param; index= edge.target; mapping; transition }
  in
  (* move equality and inequality facts from precondition to tags because Tamarin cannot handle
     (N)Eq fact generation rules correctly for fresh values *)
  let pre, label, post = facts_of_edge edge in
  let { deps= pre_deps; result= pre } = compile_facts pre in
  let { deps= label_deps; result= label } = compile_facts label in
  let { deps= post_deps; result= post } = compile_facts post in
  let label =
    if !Config.tag_transition then
      Transition { proc_id; param; source=edge.source; transition= Some Var } :: label
    else label
  in
  let pre = state_pre :: pre @ pre_deps @ post_deps @ post_consts @ label_deps in
  let post = state_post :: post in
  let comment =
    Some (Printf.sprintf
            "Edge %s/%s : %s"
            (Ident.to_string (proc_id :> Ident.t))
            (Ident.to_string (edge.id :> Ident.t))
            (Sem.Update.to_string edge.update)
         )
  in
  { id= (edge.id :> Ident.t); role; pre; label; post; comment }

(* rule Init__system[role="system"]
    : []
    --[Init__('rab__system')]
    ->[!ACP__GEN__('rab__system__', 'rab__rab_str'),
       State__Server(<'rab_____0', 'rab__rab_str', %1>,
                     'rab__unit',                         <--- return
                     'rab__empty', 'rab__empty', 'rab__empty'  <-- mutable vars
                    )]

   # Processes quantified together must be initialized together
   rule Init__system1[role="system1"]
    : [Fr(param)]
    --[Init__(<'rab__system1', param>)]
    ->[!ACP__GEN__('rab__system1__', param),
       State__Client_ta(<'rab_____0', param, %1>,
                        'rab__unit',         <--- return
                        'rab__empty', 'rab__empty', 'rab__empty'), <-- mutable vars
       State__Client(<'rab_____0', param, %1>,
                     'rab__unit',
                     'rab__empty', 'rab__empty', 'rab__empty')]
*)

let proc_group_init ((proc_group_id : Subst.proc_group_id), (p : Sem.proc_group_desc)) =
  let comment = Some (Printf.sprintf "Proc group initialization %s" (Ident.to_string (proc_group_id :> Ident.t))) in
  match p with
  | Unbounded proc ->
      assert (proc.param = None);
      let pre = [] in
      let label = [ Initing_proc_group (proc_group_id, None) ] in
      let rho = Ident.local "rho" in
      let state = State
          { proc_id= proc.id
          ; param= None
          ; index= Sem.Index.zero (* ? *)
          ; mapping= [ rho, Unit ]
          ; transition= if !Config.tag_transition then Some One else None
          }
      in
      let post = [ Inited_proc_group (proc_group_id, None); state ] in
      { id = Ident.prefix "Init_" (proc_group_id :> Ident.t)
      ; role = Some (proc_group_id :> Ident.t)
      ; pre
      ; label
      ; post
      ; comment
      }
  | Bounded (param, procs) ->
      let pre = [ Fresh (param :> Ident.t) ] in
      let label = [ Initing_proc_group (proc_group_id, Some param) ] in
      let states =
        List.map (fun (proc : Sem.proc) ->
            assert (proc.param <> None);
            let rho = Ident.local "rho" in
            State
              { proc_id= proc.id
              ; param= Some param
              ; index= Sem.Index.zero (* ? *)
              ; mapping = [ rho, Unit ] (* no need of param in the mapping since it is not mutable *)
              ; transition= if !Config.tag_transition then Some One else None
              }
          ) procs
      in
      let post = Inited_proc_group (proc_group_id, Some param) :: states in
      { id = Ident.prefix "Init_" (proc_group_id :> Ident.t)
      ; role = Some (proc_group_id :> Ident.t)
      ; pre
      ; label
      ; post
      ; comment
      }

let rule_of_const (id : Ident.t) (init_desc : Typed.init_desc) : rule =
  let rule_id = Ident.prefix "Const_" id in
  match init_desc with
  | Fresh -> (* const fresh c *)
      let const = Const { id; param= None; value= Ident id } in
      { id= rule_id
      ; role= None
      ; pre= [Fresh id]
      ; label= [Initing_const {id; param= None}; const]
      ; post= [const]
      ; comment = Some (Printf.sprintf "const fresh %s" (Ident.to_string id))
      }
  | Value e -> (* const c = e *)
      let { deps= const_deps; result= e' } = compile_expr e in
      let const = Const { id; param= None; value= e' } in
      { id= rule_id
      ; role= None
      ; pre= const_deps
      ; label= [Initing_const {id; param= None}; const]
      ; post= [const]
      ; comment = Some (Printf.sprintf "const %s = %s" (Ident.to_string id) (Typed.string_of_expr e))
      }
  | Fresh_with_param -> (* const fresh c<> *)
      (* rule Const_c
          : [Fr(c)]
            --[Init_(<'rab_c', param>), !Const_(<'rab_c', param>, c)]->
            [!Const_(<'rab_c', param>, c)]
      *)
      let p = Subst.param_id @@ Ident.local "param" in
      let const = Const { id; param= Some (Ident (p :> Ident.t)); value= Ident id } in
      { id= rule_id
      ; role= None
      ; pre= [Fresh (id :> Ident.t)]
      ; label= [Initing_const {id; param= Some p}; const]
      ; post= [const]
      ; comment = Some (Printf.sprintf "const fresh %s<>" (Ident.to_string id))
      }
  | Value_with_param (p, e) -> (* const c<p> = e *)
      let { deps= const_deps; result= e' } = compile_expr e in
      let const = Const { id; param= Some (Ident p); value= e' } in
      { id= rule_id
      ; role = None
      ; pre = const_deps
      ; label= [Initing_const {id; param= Some (Subst.param_id p)}; const]
      ; post= [const]
      ; comment = Some (Printf.sprintf "const %s<%s> = %s" (Ident.to_string id) (Ident.to_string p) (Typed.string_of_expr e))
      }

let compile_access_controls
    (proc_group_id, proc_group_desc : Sem.proc_group)
    proc_id_elems_list =
  let param =
    match proc_group_desc with
    | Unbounded _ -> None
    | Bounded (param, _) -> Some param
  in
  let compile_proc_id_elems ((proc_id : Subst.proc_id), elems) =
    if elems = [] then None
    else
      let rule_id = Ident.prefix "Access_" (proc_id :> Ident.t) in
      let comment =
        Some (Printf.sprintf "Access control for proc %s of group %s"
                (Ident.to_string (proc_id :> Ident.t))
                (Ident.to_string (proc_group_id :> Ident.t)))
      in
      let pre = [ Inited_proc_group (proc_group_id, param) ] in
      let label = [ Initing_proc_access { proc_id; param } ] in
      let { deps; result= post } =
        mapM (fun ((chan_arg : Typed.chan_arg), syscall_opt) ->
            let* channel= expr_of_chan_arg chan_arg in
            return @@ Access {
              proc_id;
              param;
              channel;
              syscall= syscall_opt
            }) elems
      in
      assert (deps = []); (* XXX ??? *)
      match post with
      | [] -> None
      | _ ->
          Some { id= rule_id
               ; role = Some (proc_id :> Ident.t)
               ; pre
               ; label
               ; post
               ; comment
               }
  in
  match List.filter_map compile_proc_id_elems proc_id_elems_list with
  | [] -> None
  | rules -> Some rules

type t =
  { signature : signature
  ; constants : rule list
  ; proc_group_inits : rule list
  ; access_controls : rule list
  ; models : (Subst.proc_id * rule list) list
  ; lemmas : (Ident.t * lemma) list
  }

let print_midamble ppf =
  Format.pp_print_string ppf
    {|//// Midamble

restriction Init : " All x #i #j . Init(x) @ #i & Init(x) @ #j ==> #i = #j "
restriction Equality_rule: "All x y #i. Eq(x,y) @ #i ==> x = y"
restriction NEquality_rule: "All x #i. NEq(x,x) @ #i ==> F"

lemma AlwaysStarts[reuse,use_induction]:
      "All x p #i. Loop_Back(x, p) @i ==> Ex #j. Loop_In(x, p) @j & j < i"

lemma AlwaysStartsWhenEnds[reuse,use_induction]:
      "All x p #i. Loop_Out(x, p) @i ==> Ex #j. Loop_In(x, p) @j & j < i"

lemma TransitionOnce[reuse,use_induction]:
      "All x p %i #j #k . Transition(x, p, %i) @#j & Transition(x, p, %i) @#k ==> #j = #k"
|}

let print ppf t =
  let open Format in
  fprintf ppf "theory rabbit@.";
  fprintf ppf "begin@.";
  fprintf ppf "builtins: natural-numbers@.";

  fprintf ppf "@.//// Signature@.@.";
  print_signature ppf t.signature;

  fprintf ppf "@.//// Constants@.@.";
  List.iter (fprintf ppf "%a@.@." print_rule) t.constants;

  fprintf ppf "@.//// Proc group initialization@.@.";
  List.iter (fprintf ppf "%a@.@." print_rule) t.proc_group_inits;

  fprintf ppf "@.//// Access control@.@.";
  List.iter (fprintf ppf "%a@.@." print_rule) t.access_controls;

  fprintf ppf "//// Proc models@.@.";
  List.iter (fun ((proc_id : Subst.proc_id), rules) ->
      fprintf ppf "// Model of proc %s@.@." (Ident.to_string (proc_id :> Ident.t));
      List.iter (fprintf ppf "%a@.@." print_rule) rules) t.models;

  if !Config.tag_transition then print_midamble ppf;

  fprintf ppf "@.//// Lemmas@.@.";
  List.iter (print_lemma ppf) t.lemmas;

  fprintf ppf "@.end@."


let compile_sem ({ signature; proc_groups; constants; lemmas; access_controls } : Sem.t) =
  let signature = compile_signature signature in
  let constants = List.map (fun (id, init_desc) -> rule_of_const id init_desc) constants in
  let models =
    List.map (fun ({ id; edges; param } : Sem.proc) -> (id, List.map (rule_of_edge id param) edges))
    @@ List.concat_map (function
        | _procid, Sem.Unbounded m -> [m]
        | _procid, Bounded (_, ms) -> ms) proc_groups
  in
  let proc_group_inits = List.map proc_group_init proc_groups in
  let lemmas = List.map (fun (id, l) -> id, compile_lemma l) lemmas in
  let access_controls = List.concat @@ List.filter_map (fun (proc_group_id, ac) ->
      compile_access_controls (proc_group_id, List.assoc proc_group_id proc_groups) ac)
      access_controls
  in
  { signature; constants; models; proc_group_inits; lemmas; access_controls }
