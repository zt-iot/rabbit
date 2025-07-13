
open Sets 
open Maps


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






(* You must implement this function to convert environments *)
let convert_env (env : Env.t) : Cst_env.t =
  failwith "convert_env not implemented"

let make_loc_env loc env desc : 'a Cst_syntax.loc_env =
  { desc; loc; env = convert_env env }


let convert_decl (td : Typed.decl) : Cst_syntax.decl list =
  let { Typed.loc; env; desc } = td in
  match desc with
  | Typed.Syscall { id; fun_sig; cmd } ->
      (* TODO: convert syscall *)
      [make_loc_env loc env @@
      failwith "Syscall conversion not implemented"]

  | Typed.Attack { id; syscall; args; cmd } ->
      (* TODO: convert attack *)
      [make_loc_env loc env @@
      failwith "Attack conversion not implemented"]

  | Typed.AllowAttack { process_typs; attacks } ->
      (* TODO: convert allow-attack rule *)
      [make_loc_env loc env @@
      failwith "AllowAttack conversion not implemented"]

  | Typed.Process { id; param; args; typ; files; vars; funcs; main } ->
      (* TODO: convert process definition *)
      [make_loc_env loc env @@
      failwith "Process conversion not implemented"]

  | Typed.System (procs, lemmas) ->
      (* TODO: convert lemmas if necessary *)
      [make_loc_env loc env @@
      failwith "TODO"]

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
      failwith "Expected a System declaration at the end, but the list is empty"
  | Typed.System(procs, _) :: decls_rev ->

    let (read_access_map, provide_access_map) = create_access_maps decls in 
    let all_process_typs = extract_process_typs_from_decls procs decls_rev in

    (* The method to compute the relation is the same for both reading/providing *)
    let secrecy_lattice = compute_access_relation read_access_map in (* the relation is '>=' *)
    let integrity_lattice = compute_access_relation provide_access_map in (* the relation is '<=' *)

    
    let security_type_to_secrecy_lvl = read_access_map_to_secrecy_lvls_map read_access_map all_process_typs in 
    let security_type_to_integrity_lvl = provide_access_map_to_integrity_lvls_map provide_access_map all_process_typs in
    
    failwith "TODO"
  | _ -> failwith "TODO"
