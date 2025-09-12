
open Sets 
open Maps

exception CstConversionException of string




let raise_conv_exception_with_location msg loc = 
    Location.print loc Format.std_formatter;
    Format.pp_print_newline Format.std_formatter ();
    raise (CstConversionException msg)













type syscall_effect = 
  | Read 
  | Provide 
  | ReadProvide


type syscall_effect_map = (syscall_effect) string_map


let syscall_effect_map = 
  StringMap.empty
  |> StringMap.add "recv" Read
  |> StringMap.add "send" Provide
  |> StringMap.add "invoke_rpc" ReadProvide


type proc_ty = Ident.t 
type sec_ty = Ident.t
type syscall_desc = Typed.syscall_desc


let induces_read_effect (syscall_desc : Typed.syscall_desc) : bool = match syscall_desc with 
  | Typed.Read -> true 
  | Typed.Provide -> false 
  | Typed.DirectInteraction -> true 
  | Typed.SyscallId id -> match StringMap.find_opt (fst id) syscall_effect_map with 
      | Some (Read | ReadProvide) -> true
      | _ -> false

let induces_provide_effect (syscall_desc : Typed.syscall_desc) : bool = match syscall_desc with 
  | Typed.Read -> false 
  | Typed.Provide -> true 
  | Typed.DirectInteraction -> true 
  | Typed.SyscallId id -> match StringMap.find_opt (fst id) syscall_effect_map with 
      | Some (Provide | ReadProvide) -> true
      | _ -> false

      
(* A map from SecurityType (=string) to ProcTySet.t, which tells us which security type is allowed to be accessed by which process *)
type access_map = (proc_ty_set) SecurityTypeMap.t

let pp_access_map fmt map = 
  Format.fprintf fmt "%s" "{";
  Maps.SecurityTypeMap.iter (fun sec_ty proc_ty_set -> 
      Format.fprintf fmt "%s" "(";
      Format.fprintf fmt "%s" (Ident.to_string sec_ty);
      Format.fprintf fmt "%s" ", ";
      Sets.pp_proc_ty_set fmt proc_ty_set;
      Format.fprintf fmt "%s" "); ";
    ) map;
  Format.fprintf fmt "%s\n" "}";

type conversion_context = {
  read_access_map : access_map   
  ; provide_access_map : access_map
  ; all_process_typs : proc_ty_set
  ; secrecy_lattice : Lattice_util.cst_access_policy
  ; integrity_lattice : Lattice_util.cst_access_policy 
  ; env : Env.t
}



(* For all target_typ in target_typs, register the connection (target_typ, proc_ty) in map *)
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

(* Create read_access_map and provide_access_map from a list of `Typed.Allow` declarations *)
let create_access_maps (decls : Typed.decl list) : access_map * access_map =
  List.fold_left (fun (acc_read_access, acc_provide_access) decl -> match decl.Typed.desc with 
    | Typed.Allow{process_typ = proc_ty; target_typs; syscall_descs} ->
      (* check if there is a syscall in the provided syscall list that gives a read effect *)
      let is_read_effect = (List.exists induces_read_effect syscall_descs) in 
      let is_provide_effect = (List.exists induces_provide_effect syscall_descs) in

      let read_access' = begin
        if (is_read_effect) then 
          (update_access_map acc_read_access target_typs (Ident.string_part proc_ty))
        else 
          acc_read_access
        end in 
      let provide_access' = begin
        if (is_provide_effect) then 
          (update_access_map acc_provide_access target_typs (Ident.string_part proc_ty))
        else 
          acc_provide_access
      end in 
      
      (read_access', provide_access')
   | _ -> (acc_read_access, acc_provide_access)
  ) (SecurityTypeMap.empty, SecurityTypeMap.empty) decls


(* for each security_ty, register the pairs of (proc, syscall_desc) which are allowed to have access to that security_ty *)
let tripartite_access (decls : Typed.decl list) : (ProcSyscallSet.t) SecurityTypeMap.t = 
  List.fold_left (fun acc_map decl -> match decl.Typed.desc with 
    | Typed.Allow{process_typ = proc_ty; target_typs; syscall_descs} -> 
      (* add binding for all syscall_desc \in syscall_descs *)
      List.fold_left (fun acc_map_2 target_typ -> 
        List.fold_left (fun acc_map_3 syscall_desc -> 

            (* Query for current security type 
            key = security_typ
            value = (proc_ty * syscall_desc) list
            *)
            let syscalls_in_access_opt = SecurityTypeMap.find_opt target_typ acc_map_3 in 
            let old_set = begin match syscalls_in_access_opt with 
            | None -> ProcSyscallSet.empty
            | Some (s) -> s
            end in 
            let new_set = ProcSyscallSet.add (proc_ty, syscall_desc) old_set in 
            SecurityTypeMap.add target_typ new_set acc_map_3
          ) acc_map_2 syscall_descs
      ) acc_map target_typs
    | _ -> acc_map
  ) SecurityTypeMap.empty decls

(* 
(* transforms the SecurityTypeMap to a ProcTyMap instead, which contains the same information *)
let compute_proc_ty_to_syscalls_set_map (tripartite_access : (ProcSyscallSet.t) SecurityTypeMap.t) : (SecSyscallSet.t) ProcTyMap.t = 
  (* for each pair (proc_ty, syscall) occuring throughout tripartite_access, register that 'proc_ty' is allowed to call 'syscall' *) 
  Maps.SecurityTypeMap.fold (fun sec_ty proc_syscall_set acc_proc_ty_map_1 -> 
      Sets.ProcSyscallSet.fold (fun (proc_ty, syscall_desc) acc_proc_ty_map_2 -> 
          let old_set = match Maps.ProcTyMap.find_opt proc_ty acc_proc_ty_map_2 with 
            | None -> SecSyscallSet.empty
            | Some s -> s 
          in 
          let new_set = SecSyscallSet.add (sec_ty, syscall_desc) old_set in 
          Maps.ProcTyMap.add proc_ty new_set acc_proc_ty_map_2
        ) proc_syscall_set acc_proc_ty_map_1
    ) tripartite_access Maps.ProcTyMap.empty *)

let syscall_per_proc_ty_from_allow_rules (decls : Typed.decl list) : (SyscallDescSet.t ProcTyMap.t) = 
  List.fold_left (fun acc_map decl -> match decl.Typed.desc with 
    | Typed.Allow{process_typ = proc_ty; syscall_descs; _} -> 
      List.fold_left (fun acc_map_2 syscall_desc -> 
        let syscalls_in_access_opt = Maps.IdentMap.find_opt proc_ty acc_map_2 in  
        let old_set = begin match syscalls_in_access_opt with 
            | None -> SyscallDescSet.empty
            | Some (s) -> s
            end in 
       let new_set = Sets.SyscallDescSet.add syscall_desc old_set in 
       Maps.IdentMap.add proc_ty new_set acc_map
      ) acc_map syscall_descs
    | _ -> acc_map
  ) ProcTyMap.empty decls


(* COMPUTING a <= b FOR EACH PAIR OF ELEMENTS OF `all_process_typs` *)
(* Takes an access_map : access_map and proc_ty : string and returns the set of security types that include the given proc_ty *)
(* 1. Find the set of security labels that allow access to a given process type *)
let accessing_labels (access_map : access_map) (proc_ty : string) : SecurityTypeSet.t =
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
let compute_access_relation (access_map : access_map) : ((proc_ty_set * proc_ty_set) * bool) list =
  (* first get the list of unique proc_ty_sets in access_map values *)
  let proc_ty_sets = SecurityTypeMap.bindings access_map |> List.map snd |> List.sort_uniq ProcTySet.compare in 
  (* Then compute whether a \rel b for all ordered pairs (a, b) of proc_ty_sets *)
  List.flatten (
    List.map (fun a ->
      List.map (fun b ->
        let geq = proc_ty_set_rel access_map a b in
        ((a, b), geq)
      ) proc_ty_sets
    ) proc_ty_sets
  )


(*****
Converter functions from typed.ml and env.ml to cst_syntax.ml
*)
let rec convert_instantiated_ty_to_core (ctx : conversion_context) (t : Env.instantiated_ty) 
   : (Cst_syntax.core_security_ty) = 


  let read_access_map = ctx.read_access_map in
  let provide_access_map = ctx.provide_access_map in
  let all_process_typs = ctx.all_process_typs in
  let secrecy_lattice = ctx.secrecy_lattice in
  let integrity_lattice = ctx.integrity_lattice in
  let env = ctx.env in

   match t with
    | Env.TySecurity (sec_ty_name, simple_ty_id, simple_ty_instantiated_tys) ->
        
        let converted_simple_ty_params = List.map (convert_instantiated_ty_to_core ctx) simple_ty_instantiated_tys in
        let ct = Cst_syntax.TSimple (simple_ty_id, converted_simple_ty_params) in 

        let readers = begin match SecurityTypeMap.find_opt sec_ty_name read_access_map with 
          | (Some s) -> s
          | None -> ProcTySet.empty
        end in 


        let providers = begin match SecurityTypeMap.find_opt sec_ty_name provide_access_map with
          | (Some s) -> s 
          | None -> ProcTySet.empty
        end in 

        let secrecy_lvl = Lattice_util.proc_ty_set_to_secrecy_lvl readers all_process_typs in 
        let integrity_lvl = Lattice_util.proc_ty_set_to_integrity_lvl providers all_process_typs in 

        ct, (secrecy_lvl, integrity_lvl)
        
    | Env.TySimple (ty_name, param_list) ->
        (* Convert parameter list recursively *)
        let converted_params = List.map (convert_instantiated_ty_to_core ctx) param_list in
        let ct = Cst_syntax.TSimple (ty_name, converted_params) in 
        
        (* A simple type is always (Public, Untrusted) as every party has read/provide access to it *)
        ct, (Lattice_util.Public, Lattice_util.Untrusted)
        
    | Env.TyProduct (ty1, ty2) ->
        let converted_ty1 = convert_instantiated_ty_to_core ctx ty1 in
        let converted_ty2 = convert_instantiated_ty_to_core ctx ty2 in
        let ct = Cst_syntax.TProd (converted_ty1, converted_ty2) in

        (* the secrecy lvl of a product is the greatest lower bound, i.e. the meet of the two secrecy levels *)
        let (_, (secrecy_lvl1, _)) = converted_ty1 in 
        let (_, (secrecy_lvl2, _)) = converted_ty2 in 
        let (_, (_, integrity_lvl1)) = converted_ty1 in 
        let (_, (_, integrity_lvl2)) = converted_ty2 in 

        let secrecy_lvl = Lattice_util.join_of_secrecy_lvls ctx.all_process_typs secrecy_lattice secrecy_lvl1 secrecy_lvl2 in 
        let integrity_lvl = Lattice_util.meet_of_integrity_lvls ctx.all_process_typs integrity_lattice integrity_lvl1 integrity_lvl2 in 

        begin match (secrecy_lvl, integrity_lvl) with 
          | (Some s, Some i) -> ct, (s, i)
          (* XXX TODO : Don't know what to do if there is no join or meet *)
          | (_, _) -> ct, (secrecy_lvl1, integrity_lvl1)
        end


    | Env.TyChanPlain(param_list) -> 
      let converted_params = List.map (convert_instantiated_ty_to_core ctx ) param_list in 
      let ct = Cst_syntax.TChan converted_params in 
      ct, (Lattice_util.Public, Lattice_util.Untrusted)
        
    | Env.TyChan (chan_ty_ident) ->
      
        (* look up the security type *)
        let param_list = match Env.find_opt_by_id env chan_ty_ident with 
          | Some Env.ChanTypeDef(instantiated_tys) -> instantiated_tys
          | _ -> raise (CstConversionException "There is a an Env.TyChan declared which does not point to a channel type definition: this should not be possible")
        in

        (* Convert channel parameter list *)
        let converted_params = 
          List.map (convert_instantiated_ty_to_core ctx) param_list in 
        let ct = Cst_syntax.TChan converted_params in 

        (* compute secrecy and integrity level in the same manner as for Env.TySecurity *)

        let readers = begin match SecurityTypeMap.find_opt chan_ty_ident read_access_map with 
          | (Some s) -> s
          | None -> ProcTySet.empty
        end in 

        let providers = begin match SecurityTypeMap.find_opt chan_ty_ident provide_access_map with
          | (Some s) -> s 
          | None -> ProcTySet.empty
        end in 

        let secrecy_lvl = Lattice_util.proc_ty_set_to_secrecy_lvl readers all_process_typs in 
        let integrity_lvl = Lattice_util.proc_ty_set_to_integrity_lvl providers all_process_typs in 

        ct, (secrecy_lvl, integrity_lvl)

    (* this case is impossible *)
    | Env.TyPoly _ -> .

let convert_function_param_to_core (ctx : conversion_context) (param : Env.function_param) : Cst_syntax.core_security_function_param = match param with 
    | Env.TyPoly str -> (Cst_syntax.TPoly str, (Lattice_util.Public, Lattice_util.Untrusted))
    | p -> 
        let cst = 
          (convert_instantiated_ty_to_core ctx (Env.function_param_to_inst_ty p)) in
        Cst_syntax.core_sec_ty_to_core_sec_f_param cst




let rec convert_expr (ctx : conversion_context) (e : Typed.expr) : Cst_syntax.expr = 

    let read_access_map = ctx.read_access_map in
    let provide_access_map = ctx.provide_access_map in
    let all_process_typs = ctx.all_process_typs in
    let secrecy_lattice = ctx.secrecy_lattice in
    let integrity_lattice = ctx.integrity_lattice in
    let env = ctx.env in

(*     let _ = print_endline "Converting expr" in *)

    let converted_desc = match e.desc with
    | Typed.Ident { id ; param ; _ } ->
        let converted_param = Option.map (convert_expr ctx) param in
        Cst_syntax.Ident { id; param = converted_param }
    
    | Typed.IdentWithChanIndex {id ; chan_param_index ; _ } -> 
        Cst_syntax.IdentWithChanIndex {id; chan_index = chan_param_index }

    | Typed.Boolean b -> Cst_syntax.Boolean b
    
    | Typed.String s -> Cst_syntax.String s
    
    | Typed.Integer i -> Cst_syntax.Integer i
    
    | Typed.Float f -> Cst_syntax.Float f
    
    | Typed.Apply (id, exprs) -> 

        Cst_syntax.Apply (id, List.map (convert_expr ctx) exprs)
    
    | Typed.Tuple exprs -> 
        Cst_syntax.Tuple (List.map (convert_expr ctx) exprs)
    
    | Typed.Unit -> Cst_syntax.Unit
  in
  converted_desc, e.loc


let rec convert_cmd (ctx : conversion_context)
    (cmd : Typed.cmd) : Cst_syntax.cmd =

  let read_access_map = ctx.read_access_map in
  let provide_access_map = ctx.provide_access_map in
  let all_process_typs = ctx.all_process_typs in
  let secrecy_lattice = ctx.secrecy_lattice in
  let integrity_lattice = ctx.integrity_lattice in
  let env = ctx.env in    
  
  (* Helper function to convert case statements inside of a cmd *)
  let convert_case (case : Typed.case) : Cst_syntax.case =
    { fresh = case.fresh
    ; facts = List.map (convert_fact ctx) case.facts
    ; cmd = (convert_cmd ctx) case.cmd
    }
  in

(*   let _ = print_endline "Converting cmd" in *)
  
  let converted_cmd' = match cmd.desc with
    | Typed.Skip -> Cst_syntax.Skip
    
    | Typed.Sequence (c1, c2) -> 
        Cst_syntax.Sequence ((convert_cmd ctx) c1, (convert_cmd ctx) c2)
    
    | Typed.Put facts -> 
        Cst_syntax.Put (List.map (convert_fact ctx) facts)
    
    | Typed.Let (id, expr, c) -> 
        Cst_syntax.Let (id, (convert_expr ctx) expr, (convert_cmd ctx) c)
    
    | Typed.Assign (id_opt, expr) -> 
        Cst_syntax.Assign (id_opt, (convert_expr ctx) expr)
    
    | Typed.Case cases -> 
        Cst_syntax.Case (List.map convert_case cases)
    
    | Typed.While (cases1, cases2) -> 
        Cst_syntax.While (List.map convert_case cases1, List.map convert_case cases2)
    
    | Typed.Event facts -> 
        Cst_syntax.Event (List.map (convert_fact ctx) facts)
    
    | Typed.Return expr -> 
        Cst_syntax.Return ((convert_expr ctx) expr)
    
    | Typed.New (id, instantiated_ty_opt, name_expr_opt, c) -> 
        let core_security_ty_opt = Option.map (convert_instantiated_ty_to_core ctx) instantiated_ty_opt in



        (* TODO: I'm not sure if I need to do anything with the 'name_expr_opt' here *)
        let converted_name_expr_opt = Option.map (fun (name, exprs) -> 
          (name, List.map (convert_expr ctx) exprs)) name_expr_opt in

        

        Cst_syntax.New (id, core_security_ty_opt, converted_name_expr_opt, (convert_cmd ctx) c)
    
    | Typed.Get (ids, expr, name, c) -> 
        Cst_syntax.Get (ids, (convert_expr ctx) expr, name, (convert_cmd ctx) c)
    
    | Typed.Del (expr, name) -> 
        Cst_syntax.Del ((convert_expr ctx) expr, name)
  in
  converted_cmd', cmd.loc 

and convert_fact (ctx : conversion_context) (fact : Typed.fact) : Cst_syntax.fact =

  let read_access_map = ctx.read_access_map in
  let provide_access_map = ctx.provide_access_map in
  let all_process_typs = ctx.all_process_typs in
  let secrecy_lattice = ctx.secrecy_lattice in
  let integrity_lattice = ctx.integrity_lattice in
  let env = ctx.env in 

(*   let _ = print_endline "Converting fact" in *)
  
  let converted_desc = match fact.desc with
    | Typed.Channel { channel; name; args } -> 
        Cst_syntax.Channel 
          { channel = (convert_expr ctx) channel
          ; name = name
          ; args = List.map (convert_expr ctx) args
          }
    
    | Typed.Out expr -> Cst_syntax.Out ((convert_expr ctx) expr)
    
    | Typed.In expr -> Cst_syntax.In ((convert_expr ctx) expr)
    
    | Typed.Plain (name, exprs) -> 
        Cst_syntax.Plain (name, List.map (convert_expr ctx) exprs)
    
    | Typed.Eq (e1, e2) -> 
        Cst_syntax.Eq ((convert_expr ctx) e1, (convert_expr ctx) e2)
    
    | Typed.Neq (e1, e2) -> 
        Cst_syntax.Neq ((convert_expr ctx) e1, (convert_expr ctx) e2)
    
    | Typed.File { path; contents } -> 
        Cst_syntax.File 
          { path = (convert_expr ctx) path
          ; contents = (convert_expr ctx) contents
          }
    
    | Typed.Global (name, exprs) -> 
        Cst_syntax.Global (name, List.map (convert_expr ctx) exprs)
  in
  
  converted_desc, fact.loc



(* conversion of the paramteres of a process template *)
let convert_proc_template_param (ctx : conversion_context) (p : Typed.chan_param) : Cst_syntax.core_process_param =

  let read_access_map = ctx.read_access_map in
  let provide_access_map = ctx.provide_access_map in
  let all_process_typs = ctx.all_process_typs in
  let secrecy_lattice = ctx.secrecy_lattice in
  let integrity_lattice = ctx.integrity_lattice in
  let env = ctx.env in 

  (* XXX: This is based on the assumption that process template parameters are always channel parameters, 
  which is not necessarily going to be the case in the future *)
  let function_param = Env.TyChan(p.typ) in 
    let converted_proc_param_typ = 
      (convert_function_param_to_core ctx function_param) in  
  { proc_param_id = p.channel ; proc_param_typ = converted_proc_param_typ} 






(* Get all process strings from (procs : Typed.proc list) *)
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


(* Return the set of all process types that are present in some given Typed.decl' list *)
let extract_process_typs_from_decls procs decls =
  let proc_strs = extract_proc_strings procs in 
  let add_typ_to_set acc proc_str = 
   let typ_opt = find_process_typ decls proc_str in 
   match typ_opt with 
     | Some typ_str -> ProcTySet.add typ_str acc
     (* raise exception when user tries to use a non-existing process in the system declaration *)
     | None -> raise (CstConversionException "There is a non-existing process in the system declaration") 
  in
  (* the attacker_ty needs to be explicitly added as a process type, because it does not have a `process` declaration *)
  let all_process_typs_initial = ProcTySet.empty |> ProcTySet.add "attacker_ty" in 

  (* return a set of all unique process types *)
  List.fold_left add_typ_to_set all_process_typs_initial proc_strs



let convert_env_desc (ctx : conversion_context) (desc : Env.desc) (loc : Location.t) : Cst_syntax.t_env_typ option = match desc with 
  | ExtFun (DesugaredArity _) -> raise (CstConversionException "Cannot convert Env.ExtFun without type information ")
  | ExtFun (DesugaredTypeSig function_params) -> 
      let typ = Cst_syntax.EqThyFunc (List.map (convert_function_param_to_core ctx) function_params) in
      Some typ
  | Const (_, ty_opt) -> begin match ty_opt with 
      | Some instantiated_ty -> 
          let converted_ty = (convert_instantiated_ty_to_core ctx instantiated_ty) in 
          Some (CST (converted_ty))
      | None -> 
          (raise_conv_exception_with_location "Each global constant has to have an annotated type in order to typecheck a Rabbit program" loc)
      end
  | Env.Channel (is_parameterized, chan_type_id) ->
    (* XXX: Why is chan_type_id not of type instantiated_ty here? *)
    (* for now, let the argument's type be 'TyChan(ch_param.typ)',
    although creating new nodes like this is bad practice
    *)
    let inst_ch_ty = (Env.TyChan chan_type_id) in 
    let converted_ty = (convert_instantiated_ty_to_core ctx inst_ch_ty) in 

    Some (CST (converted_ty))
  (* For all of the following Env.desc constructs : we do _not_ need to add them to our typing_env here *)

  (* We do not need to do anything with ExtSyscall, since we have added all syscalls to our environment in the 
  'initial_typing_env function, as all the information is already in a Typed.Syscall declaration
  *)
  | ExtSyscall _-> None
  (* A member function cannot occur in a system environment, so we do not process it *)
  | Function _ ->
      raise_conv_exception_with_location "A member function cannot be present in a system environment" loc
  (* A Var desc cannot occur in the system environment anyway, so we do not process it now *)
  | Var _ -> None
  (* We do not need any of the following information in our typing_env *)
  | Process | SimpleTypeDef _ | SecurityTypeDef _ | ChanTypeDef _ | FilesysTypeDef | ProcTypeDef | Attack ->
      None



let convert_process ctx id param (args : Typed.chan_param list) typ files vars funcs main = 
  (* convert args *)
  let chan_param_to_core_process_param (ch_param : Typed.chan_param) = (
    
    (* TODO: Why is ch_param not of type function_param here? *)
    (* for now, let the argument's type be 'TyChan(ch_param.typ)',
    although creating new nodes like this is bad practice
    *)
    let ch_param_ident = ch_param.channel in
    let core_function_param_typ = 
      convert_function_param_to_core ctx (Env.TyChan ch_param.typ)
    in
    (ch_param_ident, core_function_param_typ)
  ) in


  let converted_args = List.map (chan_param_to_core_process_param) args in 

  (* convert files *)
  let converted_files = List.map (fun (file_path, file_ident, file_contents) -> 
      (convert_expr ctx file_path), file_ident, (convert_expr ctx file_contents)
    ) files 
  in

  (* convert vars *)
  let converted_vars = List.map (fun (var_id, _, var_contents) -> 
      (var_id, (convert_expr ctx var_contents))
    ) vars in 
  
  (* convert member funcs *)
  let converted_member_funcs = List.map (fun (member_fun_ident, member_fun_sig, cmd) -> 
    begin match member_fun_sig with 
      | Env.DesSMFunUntyped _ -> 
        (raise_conv_exception_with_location 
          (Format.sprintf "Member function %s cannot be typechecked if it does not have a typing annotation" (Ident.string_part member_fun_ident))
          cmd.Typed.loc)
      | Env.DesSMFunTyped (idents_x_params, ret_ty) -> 
          
          let idents_x_core_f_params = List.map (fun (id, param) -> 
            (id, (convert_function_param_to_core ctx param))) idents_x_params in

          let converted_ret_ty = (convert_function_param_to_core ctx ret_ty) in 

          let core_cmd = (convert_cmd ctx cmd) in 

          let converted_member_func = 
            (member_fun_ident, idents_x_core_f_params, converted_ret_ty, core_cmd) in
          
          converted_member_func
    end
  ) funcs in 

  (* convert main function *)
  let converted_main = (convert_cmd ctx main) in 

  (* add converted process to environment *)
  let binding_value = Cst_syntax.Process{
    id = id
    ; param = param
    ; process_params = converted_args
    ; typ = typ 
    ; files = converted_files
    ; vars = converted_vars
    ; funcs = converted_member_funcs
    ; main = converted_main
  } in
  binding_value


(* the initial typing environment for all process declarations and the single system declaration *)
let initial_typing_env (proc_and_syscall_decls : Typed.decl list) 
  (ctx : conversion_context) (system_loc : Location.t) : Cst_syntax.typing_env = 
  let system_env = ctx.env in 

  (* First, we add all the process and syscalls declarations *)
  let initial_env' = List.fold_left (fun acc_t_env decl -> begin match decl.Typed.desc with 
      | Typed.Syscall { is_passive_attack = false ; id = syscall_id ; fun_sig ; cmd } -> begin match fun_sig with 
            (* every syscall has to have explicit typing information in order to apply the typechecker *)
            | Env.DesSMFunUntyped _ -> 
              (raise_conv_exception_with_location 
                (Format.sprintf "System call %s cannot be typechecked if it does not have a typing annotation" (Ident.string_part syscall_id))
                decl.loc)
            | Env.DesSMFunTyped(ids_x_params, ret_ty) -> 
              let (_, f_params) = (List.map fst ids_x_params, List.map snd ids_x_params) in 

              let core_ids_x_f_params = List.map (fun (id, param_ty) -> 
                (id, (convert_function_param_to_core ctx param_ty))) ids_x_params in
              let core_ret_ty = (convert_function_param_to_core ctx ret_ty) in 

              let core_cmd = (convert_cmd ctx cmd) in 
              let binding_value = Cst_syntax.Syscall(core_ids_x_f_params, core_ret_ty, core_cmd) in 
              
              Maps.IdentMap.add syscall_id binding_value acc_t_env
            end
      (* we only need to translate a passive attack, to ensure that the name is bound when typechecking *)
      | Typed.Syscall { is_passive_attack = true ; id = syscall_id ; _ } -> 
          let binding_value = Cst_syntax.PassiveAttack in 

          Maps.IdentMap.add syscall_id binding_value acc_t_env
        
      | Typed.Process { id; param; args; typ; files; vars; funcs; main } -> 
        let converted_process = convert_process ctx id param args typ files vars funcs main in 

        Maps.IdentMap.add id converted_process acc_t_env
      (* it is not necessary to add any other Typed.decl to our typing_env *)
      | _ -> acc_t_env
      end
    ) Maps.IdentMap.empty proc_and_syscall_decls in 

    (* Then, we add all bindings within the Env.t to our typing_env *)
    let initial_env'' = List.fold_left (fun acc_t_env (ident, env_desc) -> 
      match (convert_env_desc ctx env_desc system_loc) with 
        | None -> acc_t_env 
        | Some (converted_to_t_env_typ) -> 
          Maps.IdentMap.add ident converted_to_t_env_typ acc_t_env
      ) initial_env' system_env.vars 
    in 
    initial_env''


(* For a process instantiation pproc, return the Ident.t of the process and the Ident.t's of the arguments given to the process *)
let convert_pproc (pproc : Typed.pproc) : (Ident.t * Ident.t list) = 
  let args_idents = List.map (fun ch_arg -> 
    ch_arg.Typed.channel) pproc.Location.data.args in 
  (pproc.Location.data.id, args_idents) 

let convert (decls : Typed.decl list)
  : Cst_syntax.core_rabbit_prog = 
  
  (* check that the last declaration is a `Typed.System` declaration *)
  match List.rev decls with
  | [] ->
      raise (CstConversionException "Expected a System declaration at the end, but the list is empty")
  | {desc = System(procs, _) ; loc = system_location ; env = system_env } as sys_decl :: decls_rev ->

    (* check that there is only a _single_ system declaration in our entire Rabbit program *)
    (List.iter (fun decl -> match decl.Typed.desc with 
      | Typed.System _ -> 
        raise (CstConversionException "There can only be a single system declaration in a Rabbit program")
      | _ -> ()
    )) decls_rev;



    let system_proc_idents = List.fold_left (fun acc proc -> match proc with 
      | Typed.Unbounded(pproc) -> 
          (convert_pproc pproc) :: acc
      | Typed.Bounded(_, pprocs) -> 
          (List.map (convert_pproc) pprocs) @ acc
    ) [] procs in 

    let sys = (system_proc_idents, system_location) in 

    (* Based on all Typed.Allow declarations, create the read_access_map and provide_access_map *)
    let allow_decls = List.filter (fun decl -> match decl.Typed.desc with 
      | Typed.Allow _ -> true 
      | _ -> false 
    ) decls in 
    let (read_access_map, provide_access_map) = create_access_maps allow_decls in 

    let syscall_per_proc_ty = syscall_per_proc_ty_from_allow_rules allow_decls in 

    (* Compute the secrecy lattice and integrity lattice, from the read_access_map and provide_access_map *)
    (* The method to compute the relation is the same for both reading/providing *)
    let secrecy_lattice = ((compute_access_relation read_access_map), Lattice_util.GreaterThanOrEqual) in (* the relation is '>=' *)
    let integrity_lattice = ((compute_access_relation provide_access_map), Lattice_util.LessThanOrEqual) in (* the relation is '<=' *)

    (* To be able to insert 'Public' or 'Untrusted' at every security type, we need to know the set of all process types in our Rabbit program *)
    let all_process_typs = extract_process_typs_from_decls procs (List.map (fun (d : Typed.decl) -> d.desc) decls_rev) in

    (* we will only convert the process templates which are actually occurring in the system declaration, 
    because we do not need to typecheck any process code that is not being executed *)
    let system_proc_strings = extract_proc_strings procs in
    let proc_and_syscall_decls = List.filter (fun decl -> match decl.Typed.desc with 
      | Typed.Process { id ; _} -> 
        let proc_name = Ident.string_part id in 
        List.mem proc_name system_proc_strings
      | Typed.Syscall _ -> true 
      | _ -> false 
    ) decls in 

    let conversion_ctx = 
      { read_access_map = read_access_map   
      ; provide_access_map = provide_access_map
      ; all_process_typs = all_process_typs
      ; secrecy_lattice = secrecy_lattice
      ; integrity_lattice = integrity_lattice 
      ; env = system_env
      }  
    in

    let init_typing_env = (initial_typing_env proc_and_syscall_decls conversion_ctx system_location) in  

    let core_rabbit_prog = {
      Cst_syntax.system = sys
      ; Cst_syntax.typing_env = init_typing_env
      ; Cst_syntax.all_process_typs = all_process_typs
      ; Cst_syntax.secrecy_lattice = secrecy_lattice 
      ; Cst_syntax.integrity_lattice = integrity_lattice
      ; Cst_syntax.syscall_per_proc_ty = syscall_per_proc_ty
    } in 
    core_rabbit_prog
  | _ -> raise (CstConversionException "Expected a System declaration at the the end, but there is a different declaration")
