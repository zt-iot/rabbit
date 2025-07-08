
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

let generate_secrecy_levels (sec_ty : string) : Sets.proc_ty_set = failwith "TODO"



let update_access_map map target_typs proc_ty = 
  List.fold_left (fun acc_map security_typ ->
    (* check if there is already a binding for security_typ *)
    let proc_tys_of_security_typ = 
      match SecurityTypeMap.find_opt security_typ acc_map with 
      | Some set -> set
      | None -> ProcTySet.empty
    in
    (* create the new value of security_typ in read_access*)
    let new_proc_tys_of_security_typ = ProcTySet.add proc_ty proc_tys_of_security_typ in
    (* update the binding of security_typ with its new value *)
    SecurityTypeMap.add security_typ new_proc_tys_of_security_typ acc_map
  ) map target_typs

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


(* Supplying an environment is not necessary: 
the global environment is 
simply the environment from the Cst_syntax.decl.System declaration
*)
let rec convert (decls : Typed.decl list) : (Cst_syntax.decl list) = 
  
  let (read_access_map, provide_access_map) = create_access_maps decls in 

  failwith "TODO"

  (* match List.rev decls with
  | [] ->
      failwith "Expected a System declaration at the end, but the list is empty"
  | last_decl :: _ ->
      match last_decl.desc with
      | Typed.System (procs, _) ->
          let proc_names = List.fold_left (fun (acc_names, proc) -> 
            let new_names = begin match proc with 
              | Typed.Unbounded(pproc_located) -> 
                [fst pproc_located.data.id]
              | Typed.Bounded(_, pproc_located_list) ->
                List.map (fun pproc_located -> fst pproc_located.data.id) pproc_located_list
              end in 
            new_names @@ acc_names
          ) [] procs in ()
      | _ ->
          failwith "The last declaration must be a `system` declaration" *)