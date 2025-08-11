
open Sets 
open Maps

exception CstConversionException of string


let rec coerce_fun_param (param : Cst_syntax.core_security_function_param) : Cst_syntax.core_security_type =
  match param with
  | (CFP_Unit, lvl) -> (TUnit, lvl)
  | (CFP_Chan ps, lvl) ->
      let tys = List.map coerce_fun_param ps in
      (TChan tys, lvl)
  | (CFP_Simple (id, ps), lvl) ->
      let tys = List.map coerce_fun_param ps in
      (TSimple (id, tys), lvl)
  | (CFP_Product (p1, p2), lvl) ->
      let t1 = coerce_fun_param p1 in
      let t2 = coerce_fun_param p2 in
      (TProd (t1, t2), lvl)
  (* currently fails if the function parameter is polymorphic. Eventually, we'd want to implement proper conversion *)
  | (CFP_Poly _, _) ->
      raise (CstConversionException "CFP_Poly cannot be coerced to core_security_type")



type relation = 
  | LessThanOrEqual
  | GreaterThanOrEqual


type cst_access_policy = ((proc_ty_set * proc_ty_set) * bool) list * relation

let raise_conv_exception_with_location msg loc = 
    Location.print loc Format.std_formatter;
    Format.pp_print_newline Format.std_formatter ();
    raise (CstConversionException msg)




(* reads whether lvl_a is less than or equal to lvl_b *)
let leq_secrecy (secrecy_lattice : cst_access_policy) (lvl_a : Cst_syntax.secrecy_lvl) (lvl_b : Cst_syntax.secrecy_lvl) = 
  match lvl_a, lvl_b with 
  (* Public is smaller than every secrecy lvl *)
  | Cst_syntax.Public, _ -> true 
  | Cst_syntax.SNode(a_set), Cst_syntax.SNode(b_set) -> 
    let comparison, rel = secrecy_lattice in
    begin match rel with 
    | GreaterThanOrEqual -> 
      (* This is a sub-optimal way to compute, but for now we need it due to the way that secrecy_lattice is built *)
      let eq = ProcTySet.equal a_set b_set in 
      let a_set_geq_b_set = (List.assoc (a_set, b_set) comparison) in 
      (not a_set_geq_b_set) || eq
    | LessThanOrEqual -> (raise (CstConversionException "cannot call leq_secrecy on an integrity lattice"))
    end 
  | _, _ -> false 


(* reads whether integrity lvl a is less than or equal to integrity lvl b *)
let leq_integrity (integrity_lattice : cst_access_policy) (lvl_a : Cst_syntax.integrity_lvl) (lvl_b : Cst_syntax.integrity_lvl) = 
  match lvl_a, lvl_b with 
  (* Every element is less than or equal to Untrusted *)
  | _, Cst_syntax.Untrusted -> true 


  | Cst_syntax.INode(a_set), Cst_syntax.INode(b_set) -> 
    let comparison, rel = integrity_lattice in 

    begin match rel with 
    | LessThanOrEqual -> 
      (List.assoc (a_set, b_set) comparison)
    | GreaterThanOrEqual -> 
      (raise (CstConversionException "cannot call leq_integrity on a secrecy lattice"))
    end
  | _, _ -> false



(* Whether two `core_security_type`'s hold the same data, ignoring any (secrecy_lvl * integrity_lvl) *)
let rec equals_datatype (ty1 : Cst_syntax.core_security_type) (ty2 : Cst_syntax.core_security_type) (loc : Location.t) : bool =
  let (ct1, _) = ty1 in
  let (ct2, _) = ty2 in
  match ct1, ct2 with
  | TUnit, TUnit -> true
  | Dummy, Dummy -> true
  | TChan lst1, TChan lst2 -> 
      let same_length = (List.length lst1 = List.length lst2) in 
      if not same_length then
        (raise_conv_exception_with_location "channels do not have the same amount of type parameters" loc);
      let same_typ_params = List.for_all2 (fun typ1 typ2 -> equals_datatype typ1 typ2 loc) lst1 lst2 in 
      same_length && same_typ_params
  | TSimple (id1, lst1), TSimple (id2, lst2) ->
      let same_type = Ident.equal id1 id2 in 
      let same_length = (List.length lst1 = List.length lst2) in 
      if not same_length then
        (raise_conv_exception_with_location "simple types do not have the same amount of type parameters" loc);
      let same_typ_params = List.for_all2 (fun typ1 typ2 -> equals_datatype typ1 typ2 loc) lst1 lst2 in 
      same_type && same_length && same_typ_params
  | TProd (a1, b1), TProd (a2, b2) ->
      equals_datatype a1 a2 loc && equals_datatype b1 b2 loc
  | _, _ -> false



(* Determines whether security type t1 is a subtype of security type t2 (i.e. whether t1 <: t2) *)
let is_subtype (secrecy_lattice : cst_access_policy) (integrity_lattice : cst_access_policy) 
  (t1 : Cst_syntax.core_security_type) (t2 : Cst_syntax.core_security_type) (loc : Location.t) : bool = 
  (* for t1 to be a subtype of t2, it must hold that: 
    1.) t1 is of the same datatype as t2, and:
    2.) t1's secrecy level is smaller than or equal to the secrecy level of t2, and:
    3.) t1's integrity level is smaller than or equal to the integrity level of t2
  *)

  let (_, (t1_secrecy, t1_integrity)) = t1 in 
  let (_, (t2_secrecy, t2_integrity)) = t2 in 
  let same_datatype = equals_datatype t1 t2 loc in 
  let secrecy_cnd = begin match (t1, t2) with 
    (* For channel types, we currently do not care about secrecy levels *)
    | ((TChan _, _), (TChan _, _)) -> true 
    (* For the Dummy constructor, we do not care about secrecy levels *)
    | ((Dummy, _), (Dummy, _)) -> true
    | _ -> leq_secrecy secrecy_lattice t1_secrecy t2_secrecy 
  end in 
  let integrity_cnd = begin match (t1, t2) with 
    (* For channel types, we currently do not care about integrity levels *)
    | ((TChan _, _), (TChan _, _)) -> true 
    (* For the Dummy constructor, we do not care about integrity levels *)
    | ((Dummy, _), (Dummy, _)) -> true
    | _ -> leq_integrity integrity_lattice t1_integrity t2_integrity
  end in 
  same_datatype && secrecy_cnd && integrity_cnd





(* Given an `u : proc_ty_set`, return 'vs', a set of all `proc_ty_set`s such that for each v \in vs, v <= u *)
let elements_less_than_or_equal_to_u (pol : cst_access_policy) (u : proc_ty_set) : ProcTySetSet.t =
  if (snd pol) = LessThanOrEqual then   
    List.fold_left (fun acc ((v, u'), rel_holds) ->
      if ProcTySet.equal u u' && rel_holds then
        ProcTySetSet.add v acc
      else
        acc
    ) ProcTySetSet.empty (fst pol)
   else
    List.fold_left (fun acc ((u', v), rel_holds) ->
      if ProcTySet.equal u u' && rel_holds then
        ProcTySetSet.add v acc
      else
        acc
    ) ProcTySetSet.empty (fst pol)


(* Given an `a : proc_ty_set`, return bs, a set of all `proc_ty_set`s such that for each b \in bs, b >= a *)
let elements_greater_than_or_equal_to_u (pol : cst_access_policy) (u : proc_ty_set) : ProcTySetSet.t =
  if (snd pol) = GreaterThanOrEqual then   
    List.fold_left (fun acc ((v, u'), rel_holds) ->
      if ProcTySet.equal u u' && rel_holds then
        ProcTySetSet.add v acc
      else
        acc
    ) ProcTySetSet.empty (fst pol)
   else
    List.fold_left (fun acc ((u', v), rel_holds) ->
      if ProcTySet.equal u u' && rel_holds then
        ProcTySetSet.add v acc
      else
        acc
    ) ProcTySetSet.empty (fst pol)



    



(****
FUNCTIONS TO COMPUTE LEAST UPPER BOUND AND GREATEST LOWER BOUND
****)
let find_extremum_in_intersect
    ~(find_max : bool)
    (pol : cst_access_policy)
    (intersect : ProcTySetSet.t) : proc_ty_set option =

  let (rel, relation_kind) = pol in

  let rel_holds a b =
    List.exists (fun ((x, y), holds) ->
       ProcTySet.equal x a && ProcTySet.equal y b && holds
    ) rel
  in

  let is_extremum candidate =
    (* check if candidate is _relation_ for all `other \in intersect` *)
    ProcTySetSet.for_all (fun other ->
      (* the relation always holds on the candidate itself *)
      if ProcTySet.equal candidate other then true

      (* otherwise, check if `rel` holds depending on `relation_kind` *)
      else match (find_max, relation_kind) with
        | (true, LessThanOrEqual) -> rel_holds other candidate  (* other <= candidate <-> candidate is max *)
        | (false, LessThanOrEqual) -> rel_holds candidate other  (* candidate <= other <-> candidate is min *)
        | (true, GreaterThanOrEqual) -> rel_holds candidate other (* candidate >= other <-> candidate is max *)
        | (false, GreaterThanOrEqual) -> rel_holds other candidate (* other >= candidate <-> candidate is min *)
    ) intersect
  in

  let extremums = Seq.filter is_extremum (ProcTySetSet.to_seq intersect) in 
  let extremum_opt = Seq.uncons extremums in
  match extremum_opt with
  | Some (proc_ty_set, _) -> Some proc_ty_set
  | None -> None 


(* Given two secrecy levels a and b: 
- return the secrecy lvl which is the least upper bound of a and b, if it exists
- otherwise, return None
*)
let join_of_secrecy_lvls (pol : cst_access_policy) (a : Cst_syntax.secrecy_lvl) (b : Cst_syntax.secrecy_lvl) : Cst_syntax.secrecy_lvl option = 
  match (a, b) with
  | Cst_syntax.S_Ignore, _ -> None 
  | _, Cst_syntax.S_Ignore -> None 
  (* If one secrecy_lvl is Public, the least upper bound is the other secrecy_lvl *)
  | Cst_syntax.Public, _ -> Some b 
  | _, Cst_syntax.Public -> Some a 
  | Cst_syntax.SNode(a_set), Cst_syntax.SNode(b_set) -> 
    
    let elements_greater_than_a = elements_greater_than_or_equal_to_u pol a_set in 
    let elements_greater_than_b = elements_greater_than_or_equal_to_u pol b_set in 

    (* find the maximum element in the set of elements greater than both a and b *)
    let intersect = ProcTySetSet.inter elements_greater_than_a elements_greater_than_b in 
    let candidate = find_extremum_in_intersect ~find_max:true pol intersect in 

    match candidate with 
    | Some res -> Some (SNode res)
    | None -> None 
    

(* Given two integrity levels a and b:
- return the integrity lvl which is the greatest lower bound of a and b, if it exists
- otherwsie, return None
*)
let meet_of_integrity_lvls (pol : cst_access_policy) (a : Cst_syntax.integrity_lvl) (b : Cst_syntax.integrity_lvl) : Cst_syntax.integrity_lvl option = 
  match (a, b) with 
  | Cst_syntax.I_Ignore, _ -> None
  | _, Cst_syntax.I_Ignore -> None
  (* if one integrity_lvl is Untrusted, the greatest lower bound is the other integrity_lvl *)
  | Cst_syntax.Untrusted, _ -> Some b
  | _, Cst_syntax.Untrusted -> Some a 
  | Cst_syntax.INode(a_set), Cst_syntax.INode(b_set) -> 
    
    let elements_less_than_or_equal_to_a = elements_less_than_or_equal_to_u pol a_set in 
    let elements_less_than_or_equal_to_b = elements_less_than_or_equal_to_u pol b_set in 

    (* find the minimum element in the set of elements less than both a and b *)
    let intersect = ProcTySetSet.inter elements_less_than_or_equal_to_a elements_less_than_or_equal_to_b in 

    let candidate = find_extremum_in_intersect ~find_max:false pol intersect in 

    match candidate with 
    | Some (res) -> Some (INode res)
    | None -> None
(****
****)


let proc_ty_set_to_secrecy_lvl readers all_process_typs = 
  if readers = all_process_typs then 
    Cst_syntax.Public 
  else
    Cst_syntax.SNode readers  


let proc_ty_set_to_integrity_lvl providers all_process_typs = 
  if providers = all_process_typs then
    Cst_syntax.Untrusted
  else 
    Cst_syntax.INode providers




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


module MapAccessTable = struct
  module Key = struct
    type t = proc_ty * sec_ty * syscall_desc
    let compare = compare
  end

  module MapTable = Map.Make(Key)

  type t = bool MapTable.t

  let empty = MapTable.empty
  
  let add proc sec_ty syscall value table = 
    MapTable.add (proc, sec_ty, syscall) value table
  let find proc sec_ty syscall table = 
    MapTable.find_opt (proc, sec_ty, syscall) table
  
  let bindings table = MapTable.bindings table
end




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

      
(* A map from SecurityType (=string) to ProcTySet.t, which tells us which security type is allowed to be read by which process *)
type access_map = (proc_ty_set) security_type_map

type access_map_two = ProcSyscallSet.t security_type_map

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
      let target_typs_names = List.map fst target_typs in 

      let read_access' = begin
        if (is_read_effect) then 
          (update_access_map acc_read_access target_typs_names (Ident.string_part proc_ty))
        else 
          acc_read_access
        end in 
      let provide_access' = begin
        if (is_provide_effect) then 
          (update_access_map acc_provide_access target_typs_names (Ident.string_part proc_ty))
        else 
          acc_provide_access
      end in 
      
      (read_access', provide_access')
   | _ -> (acc_read_access, acc_provide_access)
  ) (SecurityTypeMap.empty, SecurityTypeMap.empty) decls







let create_access_map_2 (decls : Typed.decl list) : access_map_two = 
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
      ) acc_map (List.map (fun target_typ -> Ident.string_part target_typ) target_typs)
    | _ -> acc_map
  ) SecurityTypeMap.empty decls




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





  
let rec convert_instantiated_ty_to_core (read_access_map : access_map) 
  (provide_access_map : access_map) (all_process_typs : proc_ty_set)
  (secrecy_lattice : cst_access_policy) (integrity_lattice : cst_access_policy)
  (t : Env.instantiated_ty) 
   : (Cst_syntax.core_security_type) = 


(*    let _ = print_endline "Converting instantiated_ty" in *)

   let convert_instantiated_ty_to_core_rec = (convert_instantiated_ty_to_core 
    read_access_map provide_access_map all_process_typs secrecy_lattice integrity_lattice)
   in 
   match t with
    | Env.TySecurity (sec_ty_name, simple_ty_id, simple_ty_instantiated_tys) ->
      
      
        let converted_simple_ty_params = List.map convert_instantiated_ty_to_core_rec simple_ty_instantiated_tys in
        let ct = Cst_syntax.TSimple (simple_ty_id, converted_simple_ty_params) in 

        let readers = begin match SecurityTypeMap.find_opt sec_ty_name read_access_map with 
          | (Some s) -> s
          | None -> ProcTySet.empty
        end in 


        let providers = begin match SecurityTypeMap.find_opt sec_ty_name provide_access_map with
          | (Some s) -> s 
          | None -> ProcTySet.empty
        end in 


        let secrecy_lvl = Cst_syntax.proc_ty_set_to_secrecy_lvl readers all_process_typs in 
        let integrity_lvl = Cst_syntax.proc_ty_set_to_integrity_lvl providers all_process_typs in 

        ct, (secrecy_lvl, integrity_lvl)
        
    | Env.TySimple (ty_name, param_list) ->
        (* Convert parameter list recursively *)
        let converted_params = List.map convert_instantiated_ty_to_core_rec param_list in
        let ct = Cst_syntax.TSimple (ty_name, converted_params) in 
        
        (* A simple type is always (Public, Untrusted) as every party has read/provide access to it *)
        ct, (Cst_syntax.Public, Cst_syntax.Untrusted)
        
    | Env.TyProduct (ty1, ty2) ->
        let converted_ty1 = convert_instantiated_ty_to_core_rec ty1 in
        let converted_ty2 = convert_instantiated_ty_to_core_rec ty2 in
        let ct = Cst_syntax.TProd (converted_ty1, converted_ty2) in

        (* the secrecy lvl of a product is the greatest lower bound, i.e. the meet of the two secrecy levels *)
        let (_, (secrecy_lvl1, _)) = converted_ty1 in 
        let (_, (secrecy_lvl2, _)) = converted_ty2 in 
        let (_, (_, integrity_lvl1)) = converted_ty1 in 
        let (_, (_, integrity_lvl2)) = converted_ty2 in 

        let secrecy_lvl = join_of_secrecy_lvls secrecy_lattice secrecy_lvl1 secrecy_lvl2 in 
        let integrity_lvl = meet_of_integrity_lvls integrity_lattice integrity_lvl1 integrity_lvl2 in 

        begin match (secrecy_lvl, integrity_lvl) with 
          | (Some s, Some i) -> ct, (s, i)
          (* XXX : Don't know what to do if there is no join or meet *)
          | (_, _) -> ct, (secrecy_lvl1, integrity_lvl1)
        end
        
    | Env.TyChan (_, param_list) ->
        (* Convert channel parameter list *)
        let converted_params = 
          List.map convert_instantiated_ty_to_core_rec param_list in 
        let ct = Cst_syntax.TChan converted_params in 
        (* We ignore the security level of a channel type for now when typechecking *)
        ct, (Cst_syntax.S_Ignore, Cst_syntax.I_Ignore)

  


(* Boilerplate conversion necesary for `convert_function_param_to_core(Env.FParamSecurity(...)) *)
let rec cst_to_csfp (cst : Cst_syntax.core_security_type) : Cst_syntax.core_security_function_param = 
  let (core_ty, security_info) = cst in
  let converted_core_function_param = match core_ty with
    | TUnit -> Cst_syntax.CFP_Unit
    | TChan core_security_types -> 
        CFP_Chan (List.map cst_to_csfp core_security_types)
    | TSimple (ident, core_security_types) -> 
        CFP_Simple (ident, List.map cst_to_csfp core_security_types)
    | TProd (cst1, cst2) -> 
        CFP_Product (cst_to_csfp cst1, cst_to_csfp cst2)
    | Dummy -> Cst_syntax.CFP_Dummy
    
  in
  (converted_core_function_param, security_info)

let rec convert_function_param_to_core (read_access_map : access_map) 
  (provide_access_map : access_map) (all_process_typs : proc_ty_set)
  (secrecy_lattice : cst_access_policy) (integrity_lattice : cst_access_policy) 
  (env_fun_param : Env.function_param) : (Cst_syntax.core_security_function_param) = 
(*   let _ = print_endline "Converting function_param" in *)
  let convert_instantiated_ty_to_core_rec = (convert_instantiated_ty_to_core 
    read_access_map provide_access_map all_process_typs secrecy_lattice integrity_lattice) in 
  let convert_function_param_to_core_rec = (convert_function_param_to_core 
    read_access_map provide_access_map all_process_typs secrecy_lattice integrity_lattice) in
    match env_fun_param with 
    | Env.FParamChan(f_param_ty_params) -> 
(*       let _ = print_endline "Converting FParamChan" in *)
      (* Convert channel parameter list *)
        let converted_params = 
          List.map convert_function_param_to_core_rec f_param_ty_params in 
        let ct = Cst_syntax.CFP_Chan converted_params in 
        (* We ignore the security level of a channel type for now when type-checking *)
        ct, (Cst_syntax.S_Ignore, Cst_syntax.I_Ignore)
    | Env.FParamSecurity(sec_ty_name, simpletyp_name, simple_ty_instantiated_tys) -> 

(*         let _ = print_endline "Converting FParamSecurity" in *)

        let cst_simple_ty_params = List.map convert_instantiated_ty_to_core_rec simple_ty_instantiated_tys in
        let csfp_simple_ty_params = List.map Cst_syntax.cst_to_csfp cst_simple_ty_params in 
        let ct = Cst_syntax.CFP_Simple (simpletyp_name, csfp_simple_ty_params) in 

        let readers = begin match SecurityTypeMap.find_opt sec_ty_name read_access_map with 
          | (Some s) -> s
          | None -> ProcTySet.empty
        end in 
        

        let providers = begin match SecurityTypeMap.find_opt sec_ty_name provide_access_map with
          | (Some s) -> s 
          | None -> ProcTySet.empty
        end in 

        

        let secrecy_lvl = Cst_syntax.proc_ty_set_to_secrecy_lvl readers all_process_typs in 
        let integrity_lvl = Cst_syntax.proc_ty_set_to_integrity_lvl providers all_process_typs in 

        ct, (secrecy_lvl, integrity_lvl)

    | Env.FParamSimple(simple_ty_name, f_param_ty_params) -> 

(*       let _ = print_endline "Converting FParamSimple" in *)
      (* Convert parameter list recursively *)
        let converted_params = List.map convert_function_param_to_core_rec f_param_ty_params in
        let ct = Cst_syntax.CFP_Simple (simple_ty_name, converted_params) in 
        
        (* A simple type is always (Public, Untrusted) as every party has read/provide access to it *)
        ct, (Cst_syntax.Public, Cst_syntax.Untrusted)

    | Env.FParamProduct(f_param1, f_param2) -> 

(*         let _ = print_endline "Converting FParamProduct" in *)
      
        let converted_ty1 = convert_function_param_to_core_rec f_param1 in
        let converted_ty2 = convert_function_param_to_core_rec f_param2 in
        let ct = Cst_syntax.CFP_Product (converted_ty1, converted_ty2) in 


        (* the secrecy lvl of a product is the greatest lower bound, i.e. the meet of the two secrecy levels *)
        let (_, (secrecy_lvl1, _)) = converted_ty1 in 
        let (_, (secrecy_lvl2, _)) = converted_ty2 in 
        let (_, (_, integrity_lvl1)) = converted_ty1 in 
        let (_, (_, integrity_lvl2)) = converted_ty2 in 

        let secrecy_lvl = join_of_secrecy_lvls secrecy_lattice secrecy_lvl1 secrecy_lvl2 in 
        let integrity_lvl = meet_of_integrity_lvls integrity_lattice integrity_lvl1 integrity_lvl2 in 

        begin match (secrecy_lvl, integrity_lvl) with 
          | (Some s, Some i) -> ct, (s, i)

          (* XXX : Don't know what to do if there is no join or meet *)
          | (_, _) -> ct, (secrecy_lvl1, integrity_lvl1)
        end 

    | Env.FParamPoly(id) -> 
(*         let _ = print_endline "Converting FParamPoly" in *)
        (* Ignore this secrecy/integrity level when type-checking *)
        CFP_Poly(id), (Cst_syntax.S_Ignore, Cst_syntax.I_Ignore)




let convert_env_desc (read_access_map : access_map) 
  (provide_access_map : access_map) (all_process_typs : proc_ty_set)
  (secrecy_lattice : cst_access_policy) (integrity_lattice : cst_access_policy) 
  (env_desc : Env.desc) : Cst_syntax.desc =

(*   let _ = print_endline "Converting env_desc" in *)
  let convert_function_param_to_core_rec = 
    (convert_function_param_to_core read_access_map provide_access_map all_process_typs secrecy_lattice
      integrity_lattice
    ) in 
  let convert_instantiated_ty_to_core_rec = 
    (convert_instantiated_ty_to_core read_access_map provide_access_map all_process_typs secrecy_lattice
      integrity_lattice) in 
  match env_desc with
  | SimpleTypeDef name_list -> SimpleTypeDef name_list
  | Var (var_desc, ty_opt) -> 

    Var(var_desc, Option.map (convert_instantiated_ty_to_core_rec) ty_opt)
    
    (* ExtFuns without typing information are only allowed if no typechecking happens *)
  | ExtFun (DesugaredArity _) -> raise (CstConversionException "Cannot convert ExtFun without type information to Cst_syntax.desc")
  | ExtFun (DesugaredTypeSig function_params) -> 
      ExtFun (List.map convert_function_param_to_core_rec function_params)

  (* ExtSyscalls without typing information are only allowed if no typechecking happens *)
  | ExtSyscall (DesSMFunUntyped _) -> raise (CstConversionException "Cannot convert ExtSyscall without type information to Cst_syntax.desc")
  | ExtSyscall (DesSMFunTyped (_, function_params)) ->
      ExtSyscall (List.map convert_function_param_to_core_rec function_params)
  (* Functions without typing information are only allowed if no typechecking happens *)
  | Function (DesSMFunUntyped _) -> raise (CstConversionException "Cannot convert Function without type information to Cst_syntax.desc")
  | Function (DesSMFunTyped (_, function_params)) ->
      MemberFunc (List.map convert_function_param_to_core_rec function_params)

  (* Const without typing information is only allowed if no typechecking happens *)
  | Const (_, None) -> 
      raise (CstConversionException "Cannot convert Const without type information to Cst_syntax.desc")
  | Const (is_param, Some instantiated_ty) ->
      Const (is_param, convert_instantiated_ty_to_core_rec instantiated_ty)
  | Channel (is_param, ident) -> ChannelDecl (is_param, ident)
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
  (env : Env.t) : Cst_syntax.t = 

  let convert_env_desc_rec = convert_env_desc read_access_map provide_access_map all_process_typs secrecy_lattice integrity_lattice in
  let cst_vars = 
    List.map (fun (id, env_desc) -> (id, (convert_env_desc_rec env_desc))) env.vars in
  let cst_facts = env.facts in 
  {vars = cst_vars ; facts = cst_facts}






let rec convert_expr (read_access_map : access_map) 
    (provide_access_map : access_map) (all_process_typs : proc_ty_set)
    (secrecy_lattice : cst_access_policy) (integrity_lattice : cst_access_policy) (e : Typed.expr) : Cst_syntax.expr = 
    let convert_expr_rec = convert_expr read_access_map provide_access_map all_process_typs secrecy_lattice integrity_lattice in

(*     let _ = print_endline "Converting expr" in *)

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
        (* we need to check whether the process type calling this function has the permission to call this system call *)

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

(*   let _ = print_endline "Converting cmd" in *)
  
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
    
    | Typed.New (id, instantiated_ty_opt, name_expr_opt, c) -> 
        let core_security_type_opt = Option.map (convert_instantiated_ty_to_core 
          read_access_map provide_access_map all_process_typs
          secrecy_lattice integrity_lattice) instantiated_ty_opt in

        (* XXX why is name_expr_opt an Option? *)
        let converted_name_expr_opt = Option.map (fun (name, exprs) -> 
          (name, List.map convert_expr_rec exprs)) name_expr_opt in

        Cst_syntax.New (id, core_security_type_opt, converted_name_expr_opt, convert_cmd_rec c)
    
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


(*   let _ = print_endline "Converting fact" in *)
  
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
  (* return a set of all unique process types *)
  List.fold_left add_typ_to_set ProcTySet.empty proc_strs


  

let convert_env_to_typing_env (read_access_map : access_map) (provide_access_map : access_map) (all_process_typs : proc_ty_set) 
  (secrecy_lattice : cst_access_policy) (integrity_lattice : cst_access_policy) (env : Env.t) (other_decls : Typed.decl list) : Cst_syntax.typing_env = 
  let convert_instantiated_ty_to_core_rec = (convert_instantiated_ty_to_core 
    read_access_map provide_access_map all_process_typs secrecy_lattice integrity_lattice) in 
  let convert_function_param_to_core_rec = 
    (convert_function_param_to_core read_access_map provide_access_map all_process_typs secrecy_lattice integrity_lattice) in 
  let resulting_typing_env = List.fold_left (fun acc_t_env (ident, desc) -> match desc with 
    | Env.SimpleTypeDef param_list -> 
        let typ = Cst_syntax.SimpleTypeDef param_list in 
        Maps.IdentMap.add ident typ acc_t_env
    (* Env.Var is not relevant, because the environment for each process will not contain such Env.Var *)
    | Env.Var _ -> acc 
    | Env.ExtFun (DesugaredArity _) -> raise (CstConversionException "Cannot convert Env.ExtFun without type information ")
    | Env.ExtFun (DesugaredTypeSig function_params) -> 
        let typ = Cst_syntax.EqThyFunc (List.map (convert_function_param_to_core_rec) function_params) in 
        Maps.IdentMap.add ident typ acc_t_env
    | Env.ExtSyscall (DesSMFunTyped (_, f_params)) -> 
        let core_f_params = List.map (convert_function_param_to_core_rec f_params) in 
        (* we need to find the syscall's command by searching through our list of declarations *)
        let syscall_decl_opt = List.find_opt (fun decl -> match decl with 
          | Typed.Syscall {id = syscall_id ; _ } -> 
            (ident == syscall_id)
          | _ -> false 
        ) in 
        let syscall_cmd = begin match syscall_decl_opt with 
        | Some (syscall_decl) -> match syscall_decl with 
          | Typed.Syscall { cmd ; _ } -> cmd 
          | _ -> raise (CstConversionException "This should not be reachable")
        end in
        let typ = Cst_syntax.Syscall(core_f_params, syscall_cmd) in 
        Maps.IdentMap.add ident typ acc_t_env
    | Env.Function _ ->
        raise (CstConversionException "An Env.Function should not be present in an Env.t, if the Env.t is the environment of a process declaration")
    | Env.Const (_, instantiated_ty) -> 
        let converted_ty = (convert_instantiated_ty_to_core_rec instantiated_ty) in 
        Maps.IdentMap.add ident (Cst_syntax.CST converted_ty) acc_t_env

    (* TODO I don't understand how to convert an Env.Channel *)
    | Env.Channel _ -> failwith "TODO"

    (* For now, we are not going to add Attacks to the typing environment *)
    | Env.Attack -> acc_t_env

    | Env.ProcTypeDef -> 
        Maps.IdentMap.add ident Cst_syntax.ProcTypeDef acc_t_env
    | Env.FilesysTypeDef -> 
        Maps.IdentMap.add ident Cst_syntax.FilesysTypeDef acc_t_env
    | Env.ChanTypeDef (instantiated_tys) -> 
        let converted_tys = List.map (convert_instantiated_ty_to_core_rec) instantiated_tys in 
        Maps.IdentMap.add ident (Cst_syntax.CST (Cst_syntax.ChanTypeDef converted_tys)) acc_t_env
    | Env.SecurityTypeDef (simple_ty_name, instantied_tys) -> 
        let converted_tys = List.map (convert_instantiated_ty_to_core_rec) instantiated_tys in 
        let typ = (Cst_syntax.SecurityTypeDef (simple_ty_name, converted_tys)) in 
        Maps.IdentMap.add ident typ acc_t_env
    ) Maps.IdentMap.empty env.vars in 
    resulting_typing_env


let convert_proc_decls (read_access_map : access_map) (provide_access_map : access_map) (all_process_typs : proc_ty_set) 
  (secrecy_lattice : cst_access_policy) (integrity_lattice : cst_access_policy)
  (process_decls : Typed.decl list) (other_decls : Typed.decl list) : Cst_syntax.core_rabbit_prog = 
    let convert_expr_rec = convert_expr read_access_map provide_access_map all_process_typs secrecy_lattice integrity_lattice in 
    let convert_cmd_rec = (convert_cmd read_access_map provide_access_map all_process_typs 
          secrecy_lattice integrity_lattice) in 
    let convert_function_param_to_core_rec = (convert_function_param_to_core read_access_map provide_access_map all_process_typs secrecy_lattice integrity_lattice) in

    let converted_procs_and_envs = List.map (fun (decl, loc) -> match decl.Typed.desc with 
      | Typed.Process { id; param; args; typ; files; vars; funcs; main } ->
        let converted_args = List.map convert_chan_param args in 
        let converted_files = List.map (fun (x, y, z) -> 
          (convert_expr_rec x, y, convert_expr_rec z)) files in 
        let converted_vars = List.map (fun (x, _, z) -> 
          (x, convert_expr_rec z)) vars in 

        let convert_func_sig (member_fun_id : Ident.t) (y : Env.syscall_member_fun_sig) : (Ident.t * Cst_syntax.core_security_function_param) list = 
          begin match y with 
          | DesSMFunTyped(ids, fun_params) ->   
            let converted_fun_params = List.map convert_function_param_to_core_rec fun_params in 

            (* I'm assuming the arity check has already happened *)
            List.combine ids converted_fun_params 
          | _ -> 
            (raise_conv_exception_with_location 
              (Format.sprintf "Member function %s cannot be typechecked if it does not have a typing annotation" (Ident.string_part member_fun_id))
              loc
            )
          end in 
      
      let converted_funcs = List.map (fun (x, y, z) -> 
        (x, (convert_func_sig x y), convert_cmd_rec z)
        ) funcs in 

      let converted_main = convert_cmd_rec main in 

      let converted_process = Cst_syntax.Process{
          id 
          ; param
          ; args = converted_args
          ; typ 
          ; files = converted_files
          ; vars = converted_vars
          ; funcs = converted_funcs
          ; main = converted_main
        } in 

        let converted_env = convert_env_to_typing_env decl.Typed.env other_decls in 

        converted_process, converted_env
      | _ -> (raise_conv_exception_with_location "This should be a Process declaration" loc)
    ) process_decls in 
    converted_procs_and_envs


(* let convert_decl (read_access_map : access_map) 
    (provide_access_map : access_map) (all_process_typs : proc_ty_set)
    (secrecy_lattice : cst_access_policy) (integrity_lattice : cst_access_policy)
  (td : Typed.decl) : Cst_syntax.decl list =

  let convert_expr_rec = convert_expr read_access_map provide_access_map all_process_typs secrecy_lattice integrity_lattice in 
  let convert_cmd_rec = (convert_cmd read_access_map provide_access_map all_process_typs 
          secrecy_lattice integrity_lattice) in 

  let convert_function_param_to_core_rec = (convert_function_param_to_core read_access_map provide_access_map all_process_typs secrecy_lattice integrity_lattice) in 
  let { Typed.loc; env; desc; _ } = td in
  let make_loc_env_for_decl_rec = 
    make_loc_env_for_decl read_access_map provide_access_map all_process_typs secrecy_lattice integrity_lattice loc env in   
  match desc with
  | Typed.Syscall { id; fun_sig; cmd } ->

      (* let _ = print_endline (Format.sprintf "convert_decl syscall with id: %s" (fst id)) in *)

      let args = Env.syscall_member_fun_desc_to_ident_list fun_sig in
      let non_converted_function_params = begin match fun_sig with 
        | Env.DesSMFunUntyped(_) -> (raise_conv_exception_with_location "A syscall must have typing information in order to be typechecked" loc)
        | Env.DesSMFunTyped(_, fps) -> fps
      end in 
      
      let converted_function_params = List.map (convert_function_param_to_core_rec) non_converted_function_params in 
      
      let cst_cmd = (convert_cmd_rec cmd) in 
      let cst_decl = Cst_syntax.Syscall{id ; args ; fun_params = converted_function_params ; cmd = cst_cmd} in 

      [make_loc_env_for_decl_rec cst_decl]

  | Typed.Attack { id; syscall; args; cmd } ->
      (* let _ = print_endline (Format.sprintf "convert_decl attack with id: %s" (fst id)) in  *)
    
      let cst_cmd = convert_cmd_rec cmd in 
      let cst_decl = Cst_syntax.Attack{id ; syscall ; args ; cmd = cst_cmd} in 

      [make_loc_env_for_decl_rec cst_decl]

  | Typed.Process { id; param; args; typ; files; vars; funcs; main } ->
      (* let _ = print_endline (Format.sprintf "convert_decl process with id: %s" (fst id)) in  *)
      let converted_args = List.map convert_chan_param args in 
      let converted_files = List.map (fun (x, y, z) -> 
        (convert_expr_rec x, y, convert_expr_rec z)) files in 
      let converted_vars = List.map (fun (x, _, z) -> 
        (x, convert_expr_rec z)) vars in 



      let convert_func_sig (member_fun_id : Ident.t) (y : Env.syscall_member_fun_sig) : 
        (Ident.t * Cst_syntax.core_security_function_param) list = 
        begin match y with 
        | DesSMFunTyped(ids, fun_params) ->   
          let converted_fun_params = List.map convert_function_param_to_core_rec fun_params in 

          (* I'm assuming the arity check has already happened *)
          List.combine ids converted_fun_params 
        | _ -> 
          (raise_conv_exception_with_location 
            (Format.sprintf "Member function %s cannot be typechecked if it does not have a typing annotation" (Ident.string_part member_fun_id))
            td.loc   
          )
        end in 
      
      let converted_funcs = List.map (fun (x, y, z) -> 
        (x, (convert_func_sig x y), convert_cmd_rec z)
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
      (* let _ = print_endline (Format.sprintf "convert_decl system") in  *)

      (* we will only need the process names when typechecking *)


      let proc_strs = extract_proc_strings(procs) in 

      let cst_decl = Cst_syntax.System(proc_strs) in 
      [make_loc_env_for_decl_rec cst_decl]
  (* we do not give a corresponding Cst_syntax.decl for the following Typed.decl: *)
  | Typed.Equation _ -> []
  | Typed.Type _ -> []
  | Typed.Allow _ -> []
  | Typed.AllowAttack _ -> []
  | Typed.Init _ -> []
  | Typed.Channel _ -> []
  | Typed.Load _ -> [] *)







let convert (decls : Typed.decl list) 
  : Cst_syntax.core_rabbit_prog * cst_access_policy * cst_access_policy = 
  
  (* check that the last declaration is a `Typed.System` declaration *)
  match List.rev decls with
  | [] ->
      raise (CstConversionException "Expected a System declaration at the end, but the list is empty")
  | {desc = System(procs, _) ; _ } as sys_decl :: decls_rev ->

    (* check that there is only a _single_ system declaration in our entire Rabbit program *)
    (List.iter (fun decl -> match decl.Typed.desc with 
      | Typed.System _ -> 
        raise (CstConversionException "There can only be a single system declaration in a Rabbit program")
      | _ -> ()
    )) decls_rev;

    (* Based on all Typed.Allow declarations, create the read_access_map and provide_access_map *)
    let allow_decls = List.filter (fun decl -> match decl with 
      | Typed.Allow _ -> true 
      | _ -> false 
    ) decls in 
    let (read_access_map, provide_access_map) = create_access_maps allow_decls in 

    (* Compute the secrecy lattice and integrity lattice, from the read_access_map and provide_access_map *)
    (* The method to compute the relation is the same for both reading/providing *)
    let secrecy_lattice = ((compute_access_relation read_access_map), GreaterThanOrEqual) in (* the relation is '>=' *)
    let integrity_lattice = ((compute_access_relation provide_access_map), LessThanOrEqual) in (* the relation is '<=' *)


    (* To be able to insert 'Public' or 'Untrusted' at every security type, we need to know the set of all process types in our Rabbit program *)
    let all_process_typs = extract_process_typs_from_decls procs (List.map (fun (d : Typed.decl) -> d.desc) decls_rev) in

    (* we will only convert the process templates which are actually occurring in the system declaration, 
    because we do not need to typecheck any process code that is not being executed *)
    let system_proc_strings = extract_proc_strings procs in

    let proc_decls = List.filter (fun decl -> match decl with 
      | Typed.Process { id ; _} -> 
        let proc_name = Ident.string_part id in 
        List.mem proc_name system_proc_strings
      | _ -> false 
    ) in 
    let other_decls = List.filter (fun decl -> match decl with 
        | Typed.Process _ -> false 
        | _ -> true 
    ) in 

    (* Convert our Rabbit program from `typed.ml` to a core Rabbit program *)
    (** - The 'access_map's are necessary to insert the correct secrecy/integrity level at every typing information location 
        - The 'lattice's are necessary to compute the least-upper bound and greatest-lower bound for product types
    *)
    let converted_rabbit_prog = convert_proc_decls read_access_map provide_access_map all_process_typs 
      secrecy_lattice integrity_lattice proc_decls other_decls in 

    converted_rabbit_prog, secrecy_lattice, integrity_lattice
  | _ -> raise (CstConversionException "Expected a System declaration at the the end, but there is a different declaration")
