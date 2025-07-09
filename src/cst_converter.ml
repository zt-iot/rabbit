
open Sets 
open Maps


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





(* Extract ident name as string *)
let ident_name (id : Ident.t) = fst id

(* Get all process identifiers from procs *)
let extract_proc_ids procs =
  let extract_pproc_id (pproc : Typed.pproc) = match pproc.Location.data with 
  | {id; _} -> id
  in 
  let extract = function
    | Typed.Unbounded p -> [extract_pproc_id p]
    | Typed.Bounded (_, ps) -> List.map extract_pproc_id ps
  in
  List.flatten (List.map extract procs)




(* Find the corresponding Process decl and return its .typ *)
let find_process_typ decls proc_id =
  let name = ident_name proc_id in
  let is_matching_process_decl = function
    | Typed.Process { id; _ } when ident_name id = name -> true
    | _ -> false
  in
  match List.find_opt is_matching_process_decl decls with
  | Some Process { typ; _ } -> Some typ
  | _ -> None




(* Main function: from procs and decls, return list of all found typ fields *)
let extract_process_typs_from_decls procs decls =
  extract_proc_ids procs
  |> List.filter_map (find_process_typ decls)


(* Supplying an environment is not necessary: 
the global environment is 
simply the environment from the Cst_syntax.decl.System declaration
*)
let rec convert (decls : Typed.decl list) : (Cst_syntax.decl list) = 
  
  let (read_access_map, provide_access_map) = create_access_maps decls in 

  let decls' = List.map (fun decl -> decl.Typed.desc) decls in 
  match List.rev decls' with
  | [] ->
      failwith "Expected a System declaration at the end, but the list is empty"
  | Typed.System(procs, _) :: decls_rev ->
    let all_process_typs = extract_process_typs_from_decls procs decls_rev in
    failwith "TODO"
  | _ -> failwith "TODO"
