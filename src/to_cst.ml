
open Sets 
open Maps


exception CstConversionException of string

type syscall_effect = 
  | Read 
  | Provide 
  | ReadProvide


type syscall_effect_map = (syscall_effect) string_map 

type cst_access_policy = ((proc_ty_set * proc_ty_set) * bool) list


let syscall_effect_map = 
  StringMap.empty
  |> StringMap.add "recv" Read 
  |> StringMap.add "send" Provide
  |> StringMap.add "invoke_rpc" ReadProvide



(* A map from SecurityType (=string) to ProcTySet.t, which tells us which security type is allowed to be read by which process *)
type access_map = (proc_ty_set) security_type_map

(* For all security_typ in target_typs, register the connection (target_typ, proc_ty) in map *)
let update_access_map map target_typs proc_ty = 
  List.fold_left (fun acc_map security_typ ->
    (* check if there is already a binding for security_typ *)
    let proc_tys_of_security_typ = 
      match SecurityTypeMap.find_opt security_typ acc_map with 
      | Some set -> set
      | None -> ProcTySet.empty
    in
    (* create the new value of security_typ in read_access *)
    let new_proc_tys_of_security_typ = ProcTySet.add proc_ty proc_tys_of_security_typ in
    (* update the binding of security_typ with its new value *)
    SecurityTypeMap.add security_typ new_proc_tys_of_security_typ acc_map
  ) map target_typs


(* return corresponding secrecy lvl of if need_integrity_lvl=false else return corresponding integrity lvl *)
(* let access_map_to_lvl access_map need_integrity_lvl = 
  if not need_integrity_lvl then  *)









(* Create read access map and provide access map from a list of `Typed.Allow` declarations *)
let create_access_maps (decls : Typed.decl list) : access_map * access_map =
  List.fold_left (fun (acc_read_access, acc_provide_access) decl -> match decl.Typed.desc with 
    | Typed.Allow{process_typ = proc_ty; target_typs; syscalls} ->
      (* check if there is a syscall in the provided syscall list that gives a read effect *)
      let is_read_effect = 
        match syscalls with
        | None -> true
        | Some(syscalls_ids) -> 
          (not (List.is_empty (List.filter 
            (fun syscall -> match StringMap.find_opt syscall syscall_effect_map with 
              | Some (Read | ReadProvide) -> true
              | _ -> false 
            ) (List.map fst syscalls_ids)))) in
      let is_provide_effect = 
        match syscalls with 
        | None -> true 
        | Some(syscalls_ids) -> 
          (not (List.is_empty (List.filter 
            (fun syscall -> match StringMap.find_opt syscall syscall_effect_map with 
              | Some (Provide | ReadProvide) -> true
              | _ -> false 
            ) (List.map fst syscalls_ids)))) in

      
      let target_typs_simplified = List.map fst target_typs in 

      let read_access' = begin
        if (is_read_effect) then 
          (update_access_map acc_read_access target_typs_simplified (fst proc_ty))
        else 
          acc_read_access
        end in 
      let provide_access' = begin
        if (is_provide_effect) then 
          (update_access_map acc_provide_access target_typs_simplified (fst proc_ty))
        else 
          acc_provide_access
      end in 
      
      (read_access', provide_access')
   | _ -> (acc_read_access, acc_provide_access)
  ) (SecurityTypeMap.empty, SecurityTypeMap.empty) decls







(* Get all process strings from procs *)
let extract_proc_strings procs =
  let extract_pproc_str (pproc : Typed.pproc) = match pproc.Location.data with 
  | {id; _} -> Ident.string_part id
  in 
  let extract = function
    | Typed.Unbounded p -> [extract_pproc_str p]
    | Typed.Bounded (_, ps) -> List.map extract_pproc_str ps
  in
  List.flatten (List.map extract procs)


(* Find the corresponding Process decl and return its type *)
let find_process_typ decls name =
  let is_matching_process_decl = function
    | Typed.Process { id; _ } when (Ident.string_part id) = name -> true
    | _ -> false
  in
  match List.find_opt is_matching_process_decl decls with
  | Some Process { typ; _ } -> Some (Ident.string_part typ)
  | _ -> None




(* Main function: from procs and decls, return list of all found typ fields *)
let extract_process_typs_from_decls procs decls =
  let proc_strs = extract_proc_strings procs in 
  let add_typ_to_set acc proc_str = 
   let typ_opt = find_process_typ decls proc_str in 
   match typ_opt with 
     | Some typ_str -> ProcTySet.add typ_str acc 
     | None -> acc 
  in
  (* return a set of all unique process types *)
  List.fold_left add_typ_to_set ProcTySet.empty proc_strs
  


(* returns a map from SecurityType to secrecy lvl *)
let read_access_map_to_secrecy_lvls_map read_access_map all_process_typs = 
  SecurityTypeMap.map (fun set -> 
    if all_process_typs = set then 
      Cst_env.Public 
    else 
      Cst_env.SNode set
    ) read_access_map


let provide_access_map_to_integrity_lvls_map provide_access_map all_process_typs = 
  SecurityTypeMap.map (fun proc_ty_set -> 
    if all_process_typs = proc_ty_set then 
      Cst_env.Untrusted
    else 
      Cst_env.INode proc_ty_set
    ) provide_access_map


(* Takes an access_map : access_map and proc_ty : string and returns the set of security types that include the given proc_ty *)

let accessing_labels (access_map : access_map) (proc_ty : string) : SecurityTypeSet.t =
  (* 1. Find the set of security labels that allow access to a given process type *)
  SecurityTypeMap.fold (fun key allowed_set acc ->
    if ProcTySet.mem proc_ty allowed_set then
      SecurityTypeSet.add key acc
    else
      acc
  ) access_map SecurityTypeSet.empty

(* 2. Define "a × b" based on access coverage *)
let proc_ty_set_rel (access_map : access_map)
                    (a : proc_ty_set)
                    (b : proc_ty_set) : bool =
  ProcTySet.for_all (fun a_ty ->
    ProcTySet.for_all (fun b_ty ->
      let a_labels = accessing_labels access_map a_ty in
      let b_labels = accessing_labels access_map b_ty in
      SecurityTypeSet.subset b_labels a_labels
    ) b
  ) a

(* 3. Iterate over all ordered pairs (a, b) of proc_ty_sets and evaluate whether "a × b" *)
let compute_access_relation (access_map : access_map) : cst_access_policy =
  (* first get the list of unique proc_ty_sets in access_map values *)
  let proc_ty_sets = SecurityTypeMap.bindings access_map |> List.map snd |> List.sort_uniq ProcTySet.compare in 
  List.flatten (
    List.map (fun a ->
      List.map (fun b ->
        let geq = proc_ty_set_rel access_map a b in
        ((a, b), geq)
      ) proc_ty_sets
    ) proc_ty_sets
  )





let rec convert_instantiated_ty_to_core (read_access_map : access_map) 
  (provide_access_map : access_map) (all_process_typs : proc_ty_set)
  (secrecy_lattice : cst_access_policy) (integrity_lattice : cst_access_policy)
  (t : Env.instantiated_ty) 
   : (Cst_env.core_security_type) = 
   let convert_instantiated_ty_to_core_rec = (convert_instantiated_ty_to_core 
    read_access_map provide_access_map all_process_typs secrecy_lattice integrity_lattice)
  
   in 
   match t with
    | Env.TySecurity (sec_ty_name, simple_ty_name, simple_ty_instantiated_tys) ->
      
      
        let converted_simple_ty_params = List.map convert_instantiated_ty_to_core_rec simple_ty_instantiated_tys in
        let ct = Cst_env.TSimple (simple_ty_name, converted_simple_ty_params) in 

        let readers = SecurityTypeMap.find sec_ty_name read_access_map in 
        let providers = SecurityTypeMap.find sec_ty_name provide_access_map in 

        let secrecy_lvl = Cst_env.proc_ty_set_to_secrecy_lvl readers all_process_typs in 
        let integrity_lvl = Cst_env.proc_ty_set_to_integrity_lvl providers all_process_typs in 

        ct, (secrecy_lvl, integrity_lvl)

        (* ct, (secrecy_lvl, integrity_lvl) *)
        
    | Env.TySimple (ty_name, param_list) ->
        (* Convert parameter list recursively *)
        let converted_params = List.map convert_instantiated_ty_to_core_rec param_list in
        let ct = Cst_env.TSimple (ty_name, converted_params) in 
        
        (* A simple type is always (Public, Untrusted) as every party has read/provide access to it *)
        ct, (Cst_env.Public, Cst_env.Untrusted)
        
    | Env.TyProduct (ty1, ty2) ->
        let converted_ty1 = convert_instantiated_ty_to_core_rec ty1 in
        let converted_ty2 = convert_instantiated_ty_to_core_rec ty2 in
        (* the secrecy lvl of a product is the greatest lower bound *)
        let ct = Cst_env.TProd (converted_ty1, converted_ty2) in

        failwith "TODO: implement proper calculation of secrecy and integrity levels for products"
        
    | Env.TyChan param_list ->
        (* Convert channel parameter list *)
        let converted_params = 
          List.map convert_instantiated_ty_to_core_rec param_list in 
        let ct = Cst_env.TChan converted_params in 
        (* We ignore the security level of a channel type for now *)
        ct, (Cst_env.Public, Cst_env.Untrusted)



let convert_function_param_to_core (read_access_map : access_map) 
  (provide_access_map : access_map) (all_process_typs : proc_ty_set)
  (secrecy_lattice : cst_access_policy) (integrity_lattice : cst_access_policy) 
  (env_fun_param : Env.function_param) : (Cst_env.core_function_param) = 
    match env_fun_param with 
    | Env.FParamSecurity(sec_ty_name) -> 

        let ct = failwith "TODO: The information of which simple type the security type was created on should be present here, but it isn't" in 

        let readers = SecurityTypeMap.find sec_ty_name read_access_map in 
        let providers = SecurityTypeMap.find sec_ty_name provide_access_map in 
        
        failwith "TODO"

    | Env.FParamSimple(name, f_param_ty_params) -> failwith "TODO"
    | Env.FParamProduct(f_param1, f_param2) -> failwith "TODO"
    | Env.FParamChannel(f_param_ty_params) -> failwith "TODO"
    | Env.FParamPoly(id) -> failwith "TODO"




let convert_env_desc (read_access_map : access_map) 
  (provide_access_map : access_map) (all_process_typs : proc_ty_set)
  (secrecy_lattice : cst_access_policy) (integrity_lattice : cst_access_policy) 
  (env_desc : Env.desc) : Cst_env.desc =
  let convert_function_param_to_core_rec = 
    (convert_function_param_to_core read_access_map provide_access_map all_process_typs secrecy_lattice
      integrity_lattice
    ) in 
  let convert_instantiated_ty_to_core_rec = 
    (convert_instantiated_ty_to_core read_access_map provide_access_map all_process_typs secrecy_lattice
      integrity_lattice) in 
  match env_desc with
  | SimpleTypeDef name_list -> SimpleTypeDef name_list
  | Var var_desc -> Var var_desc
  | ExtFun (DesugaredArity _) -> raise (CstConversionException "Cannot convert ExtFun without type information to Cst_env.desc")
  | ExtFun (DesugaredTypeSig function_params) -> 
      ExtFun (List.map convert_function_param_to_core_rec function_params)
  | ExtSyscall (DesSMFunUntyped _) -> raise (CstConversionException "Cannot convert ExtSyscall without type information to Cst_env.desc")
  | ExtSyscall (DesSMFunTyped (_, function_params, _)) ->
      ExtSyscall (List.map convert_function_param_to_core_rec function_params)
  | Function (DesSMFunUntyped _) -> raise (CstConversionException "Cannot convert ExtSyscall without type information to Cst_env.desc")
  | Function (DesSMFunTyped (_, function_params, _)) ->
      MemberFunc (List.map convert_function_param_to_core_rec function_params)
  | Const (is_param, None) -> 
      raise (CstConversionException "Cannot convert Const without type information to Cst_env.desc")
  | Const (is_param, Some instantiated_ty) ->
      Const (is_param, convert_instantiated_ty_to_core_rec instantiated_ty)
  | ChannelDecl (is_param, ident) -> ChannelDecl (is_param, ident)
  | Attack -> Attack
  | ProcTypeDef -> ProcTypeDef
  | FilesysTypeDef -> FilesysTypeDef
  | ChanTypeDef instantiated_ty_list ->
      ChanTypeDef (List.map convert_instantiated_ty_to_core_rec instantiated_ty_list)
  | SecurityTypeDef (name, instantiated_ty_list) ->
      SecurityTypeDef (name, List.map convert_instantiated_ty_to_core_rec instantiated_ty_list)
  | Process -> Process






let convert_env (read_access_map : access_map) 
    (provide_access_map : access_map) (all_process_typs : proc_ty_set)
    (secrecy_lattice : cst_access_policy) (integrity_lattice : cst_access_policy)
  (env : Env.t) : Cst_env.t = 
  let convert_env_desc_rec = convert_env_desc read_access_map provide_access_map all_process_typs secrecy_lattice integrity_lattice in
  let cst_vars = 
    List.map (fun (id, env_desc) -> (id, (convert_env_desc_rec env_desc))) env.vars in
  let cst_facts = env.facts in 
  Env.{vars = cst_vars ; facts = cst_facts}














let rec convert_expr (read_access_map : access_map) 
    (provide_access_map : access_map) (all_process_typs : proc_ty_set)
    (secrecy_lattice : cst_access_policy) (integrity_lattice : cst_access_policy) 
    (e : Typed.expr) : Cst_syntax.expr = 
    let convert_expr_rec = convert_expr read_access_map provide_access_map all_process_typs secrecy_lattice integrity_lattice in

    let converted_desc = match e.desc with
    | Typed.Ident { id; desc; param } ->
        let converted_desc = convert_env_desc read_access_map provide_access_map all_process_typs secrecy_lattice integrity_lattice desc in
        let converted_param = Option.map convert_expr_rec param in
        Cst_syntax.Ident { id; desc = converted_desc; param = converted_param }
    
    | Typed.Boolean b -> Cst_syntax.Boolean b
    
    | Typed.String s -> Cst_syntax.String s
    
    | Typed.Integer i -> Cst_syntax.Integer i
    
    | Typed.Float f -> Cst_syntax.Float f
    
    | Typed.Apply (id, exprs) -> 
        Cst_syntax.Apply (id, List.map convert_expr_rec exprs)
    
    | Typed.Tuple exprs -> 
        Cst_syntax.Tuple (List.map convert_expr_rec exprs)
    
    | Typed.Unit -> Cst_syntax.Unit
  in
  
  { desc = converted_desc
  ; loc = e.loc
  ; env = convert_env read_access_map provide_access_map all_process_typs secrecy_lattice integrity_lattice e.env
  }


let rec convert_cmd (read_access_map : access_map) 
    (provide_access_map : access_map) (all_process_typs : proc_ty_set)
    (secrecy_lattice : cst_access_policy) (integrity_lattice : cst_access_policy)
    (cmd : Typed.cmd) : Cst_syntax.cmd =
  
  (* short-hand for recursion, so we don't have give the entire list of 6 arguments every time *)
  let convert_expr_rec = convert_expr read_access_map provide_access_map all_process_typs secrecy_lattice integrity_lattice in
  let convert_fact_rec = convert_fact read_access_map provide_access_map all_process_typs secrecy_lattice integrity_lattice in
  let convert_cmd_rec = convert_cmd read_access_map provide_access_map all_process_typs secrecy_lattice integrity_lattice in
  
  let convert_env_rec = convert_env read_access_map provide_access_map all_process_typs secrecy_lattice integrity_lattice in 
  
  (* Helper function to convert case statements inside of a cmd *)
  let convert_case (case : Typed.case) : Cst_syntax.case =
    { fresh = case.fresh
    ; facts = List.map convert_fact_rec case.facts
    ; cmd = convert_cmd_rec case.cmd
    }
  in
  
  let converted_cmd' = match cmd.desc with
    | Typed.Skip -> Cst_syntax.Skip
    
    | Typed.Sequence (c1, c2) -> 
        Cst_syntax.Sequence (convert_cmd_rec c1, convert_cmd_rec c2)
    
    | Typed.Put facts -> 
        Cst_syntax.Put (List.map convert_fact_rec facts)
    
    | Typed.Let (id, expr, c) -> 
        Cst_syntax.Let (id, convert_expr_rec expr, convert_cmd_rec c)
    
    | Typed.Assign (id_opt, expr) -> 
        Cst_syntax.Assign (id_opt, convert_expr_rec expr)
    
    | Typed.Case cases -> 
        Cst_syntax.Case (List.map convert_case cases)
    
    | Typed.While (cases1, cases2) -> 
        Cst_syntax.While (List.map convert_case cases1, List.map convert_case cases2)
    
    | Typed.Event facts -> 
        Cst_syntax.Event (List.map convert_fact_rec facts)
    
    | Typed.Return expr -> 
        Cst_syntax.Return (convert_expr_rec expr)
    
    | Typed.New (id, ty_opt, name_expr_opt, c) -> 
        (match ty_opt with
         | None -> raise (CstConversionException "New constructor requires a type annotation for CST conversion")
         | Some instantiated_ty -> 

             let core_security_type = convert_instantiated_ty_to_core 
               read_access_map provide_access_map all_process_typs
               secrecy_lattice integrity_lattice instantiated_ty in

             (* XXX why is name_expr_opt an Option and not a List? *)
             let converted_name_expr_opt = Option.map (fun (name, exprs) -> 
               (name, List.map convert_expr_rec exprs)) name_expr_opt in

             Cst_syntax.New (id, core_security_type, converted_name_expr_opt, convert_cmd_rec c))
    
    | Typed.Get (ids, expr, name, c) -> 
        Cst_syntax.Get (ids, convert_expr_rec expr, name, convert_cmd_rec c)
    
    | Typed.Del (expr, name) -> 
        Cst_syntax.Del (convert_expr_rec expr, name)
  in
  
  { desc = converted_cmd'
  ; loc = cmd.loc
  ; env = convert_env_rec cmd.env 
  }

and convert_fact (read_access_map : access_map) 
    (provide_access_map : access_map) (all_process_typs : proc_ty_set)
    (secrecy_lattice : cst_access_policy) (integrity_lattice : cst_access_policy)
    (fact : Typed.fact) : Cst_syntax.fact =
  
  let convert_expr_rec = convert_expr read_access_map provide_access_map all_process_typs secrecy_lattice integrity_lattice in
  let convert_env_rec = convert_env read_access_map provide_access_map all_process_typs secrecy_lattice integrity_lattice in 

  
  let converted_desc = match fact.desc with
    | Typed.Channel { channel; name; args } -> 
        Cst_syntax.Channel 
          { channel = convert_expr_rec channel
          ; name = name
          ; args = List.map convert_expr_rec args
          }
    
    | Typed.Out expr -> Cst_syntax.Out (convert_expr_rec expr)
    
    | Typed.In expr -> Cst_syntax.In (convert_expr_rec expr)
    
    | Typed.Plain (name, exprs) -> 
        Cst_syntax.Plain (name, List.map convert_expr_rec exprs)
    
    | Typed.Eq (e1, e2) -> 
        Cst_syntax.Eq (convert_expr_rec e1, convert_expr_rec e2)
    
    | Typed.Neq (e1, e2) -> 
        Cst_syntax.Neq (convert_expr_rec e1, convert_expr_rec e2)
    
    | Typed.File { path; contents } -> 
        Cst_syntax.File 
          { path = convert_expr_rec path
          ; contents = convert_expr_rec contents
          }
    
    | Typed.Global (name, exprs) -> 
        Cst_syntax.Global (name, List.map convert_expr_rec exprs)
  in
  
  { desc = converted_desc
  ; loc = fact.loc
  ; env = convert_env_rec fact.env
  }


let make_loc_env_for_decl  (read_access_map : access_map) 
    (provide_access_map : access_map) (all_process_typs : proc_ty_set)
    (secrecy_lattice : cst_access_policy) (integrity_lattice : cst_access_policy)
    loc env desc : 'a Cst_syntax.loc_env =
  let convert_env_rec = convert_env read_access_map provide_access_map all_process_typs secrecy_lattice integrity_lattice in 
  { desc; loc; 
  env = convert_env_rec env }


(* Boilerplate, but necessary if Cst_syntax.chan_param is ever going to be different 
  from Typed.chan_param *)
let convert_chan_param (p : Typed.chan_param) : Cst_syntax.chan_param =
  { channel = p.channel; param = p.param; typ = p.typ }



let convert_decl (read_access_map : access_map) 
    (provide_access_map : access_map) (all_process_typs : proc_ty_set)
    (secrecy_lattice : cst_access_policy) (integrity_lattice : cst_access_policy)
  (td : Typed.decl) : Cst_syntax.decl list =

  let convert_expr_rec = convert_expr read_access_map provide_access_map all_process_typs secrecy_lattice integrity_lattice in 
  let convert_cmd_rec = (convert_cmd read_access_map provide_access_map all_process_typs 
          secrecy_lattice integrity_lattice) in 
  let { Typed.loc; env; desc } = td in
  let make_loc_env_for_decl_rec = 
    make_loc_env_for_decl read_access_map provide_access_map all_process_typs secrecy_lattice integrity_lattice loc env in   
  match desc with
  | Typed.Syscall { id; fun_sig; cmd } ->

      let args = Env.syscall_member_fun_desc_to_ident_list fun_sig in 
      let cst_cmd = (convert_cmd_rec cmd) in 
      let cst_decl = Cst_syntax.Syscall{id ; args ; cmd = cst_cmd} in 

      [make_loc_env_for_decl_rec cst_decl]

  | Typed.Attack { id; syscall; args; cmd } ->
    
      let cst_cmd = convert_cmd_rec cmd in 
      let cst_decl = Cst_syntax.Attack{id ; syscall ; args ; cmd = cst_cmd} in 

      [make_loc_env_for_decl_rec cst_decl]

  | Typed.Process { id; param; args; typ; files; vars; funcs; main } ->
      let converted_args = List.map convert_chan_param args in 
      let converted_files = List.map (fun (x, y, z) -> 
        (convert_expr_rec x, y, convert_expr_rec z)) files in 
      let converted_vars = List.map (fun (x, _, z) -> 
        (x, convert_expr_rec z)) vars in 
      let converted_funcs = List.map (fun (x, y, z) -> 
        (x, Env.syscall_member_fun_desc_to_ident_list y, convert_cmd_rec z)
        ) funcs in 
      let converted_main = convert_cmd_rec main in 
      let cst_decl = 
        Cst_syntax.Process{
          id 
          ; param
          ; args = converted_args
          ; typ 
          ; files = converted_files
          ; vars = converted_vars
          ; funcs = converted_funcs
          ; main = converted_main
        } in 
      [make_loc_env_for_decl_rec cst_decl]

  | Typed.System (procs, _) ->
      let cst_decl = Cst_syntax.System(procs) in 
      [make_loc_env_for_decl_rec cst_decl]
  | _ -> []




(* return: 
- A list of Cst_syntax.decl : core syntax with annotated core security types
- A cst_access_policy for secrecy levels a, b
- A cst_access_policy for integrity levels a, b
*)
let convert (decls : Typed.decl list) 
  : (Cst_syntax.decl list) * cst_access_policy * cst_access_policy = 
  
  let decls' = List.map (fun decl -> decl.Typed.desc) decls in 
  (* check that the last declaration is a `Typed.System` declaration *)
  match List.rev decls' with
  | [] ->
      raise (CstConversionException "Expected a System declaration at the end, but the list is empty")
  | Typed.System(procs, _) :: decls_rev ->

    let (read_access_map, provide_access_map) = create_access_maps decls in 
    let all_process_typs = extract_process_typs_from_decls procs decls_rev in

    (* The method to compute the relation is the same for both reading/providing *)
    let secrecy_lattice = compute_access_relation read_access_map in (* the relation is '>=' *)
    let integrity_lattice = compute_access_relation provide_access_map in (* the relation is '<=' *)


    let converted_decls = List.fold_left (fun acc decl -> 
        acc @ (convert_decl read_access_map provide_access_map
          all_process_typs secrecy_lattice integrity_lattice decl)
      ) [] decls in 

    converted_decls, secrecy_lattice, integrity_lattice
  | _ -> raise (CstConversionException "Expected a System declaration at the the end, but there is a different declaration")
