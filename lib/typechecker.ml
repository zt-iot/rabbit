open Sets
open Maps

exception TypeException of string


type typechecking_context = 
{
  all_process_typs : Sets.proc_ty_set
  ; secrecy_lattice : Lattice_util.cst_access_policy
  ; integrity_lattice : Lattice_util.cst_access_policy
  ; allowed_syscalls : SyscallDescSet.t
}

let raise_type_exception_with_location msg loc = 
    Location.print loc Format.std_formatter;
    Format.pp_print_newline Format.std_formatter ();
    raise (TypeException msg)

(* OCaml provides no easy way to retrieve the last element of a list, so this has to be done *)
let init_and_last generic_list loc =
    let rec aux acc = function
        | [] -> raise_type_exception_with_location "A construct at this location caused `init_and_last` to be called with an empty list" loc
        | [x] -> (List.rev acc, x)
        | x :: xs -> aux (x :: acc) xs
    in
    aux [] generic_list


let rec convert_product_type_to_list_of_types (prod_type : Cst_syntax.core_security_ty) (loc : Location.t) : Cst_syntax.core_security_ty list = begin match prod_type with 
  | (Cst_syntax.TProd(t1, t2), (_, _)) -> 
    let t1_tys = convert_product_type_to_list_of_types t1 loc in 
    let t2_tys = convert_product_type_to_list_of_types t2 loc in 
    t1_tys @ t2_tys
  | t -> [t]
  end


let check_all_types_equal (secrecy_lattice : Lattice_util.cst_access_policy) (integrity_lattice : Lattice_util.cst_access_policy) 
(ts_and_locs : (Cst_syntax.core_security_ty * Location.t) list) : Cst_syntax.core_security_ty = 
  begin match ts_and_locs with 
  | [] -> 
      raise (TypeException "empty case or repeat statement") 
  | (ty1, _) :: ts' -> 
    (List.iter (fun (ty', loc') -> 
        (* For now, ty' must be a subtype of ty1, but we can _probably_ be more relaxed *)
        if not (Cst_syntax.is_subtype secrecy_lattice integrity_lattice ty' ty1 loc') then 
          (raise_type_exception_with_location "All branches of a case/repeat statement must return the same type" loc')
      ) ts');
    (* return ty1 after we concluded all types are equal *)
    ty1
  end




(* typeof_expr, typeof_cmd, typecheck_fact, typeof_case and typecheck_fact are all mutually recursive in terms of each other *)
let rec typeof_expr (ctx : typechecking_context)
  (expr : Cst_syntax.expr) (t_env : Cst_syntax.typing_env) : Cst_syntax.core_security_ty = 
  let secrecy_lattice = ctx.secrecy_lattice in
  let integrity_lattice = ctx.integrity_lattice in
  let allowed_syscalls = ctx.allowed_syscalls in

  let typeof_expr_rec = typeof_expr ctx in 
  let (expr_desc, expr_loc) = expr in 
  match expr_desc with
    | Unit ->
        (Cst_syntax.TUnit, (Public, Untrusted))
    (* Need to look up type in `t_env` *)
    | Ident { id; param } ->
        (* Look up the type of `id` in the typing environment t_env *)
         begin match IdentMap.find_opt id t_env with 
          | Some t -> (Cst_syntax.coerce_tenv_typ t expr_loc) 
          | None -> (raise_type_exception_with_location (Format.sprintf "No entry for the following Ident.t: %s" (Ident.name id)) expr_loc)
         end
    (* Return type bool for both options IF it was declared as simple type *)
    | Boolean _ -> 
        let bool_ident = (Cst_syntax.t_env_lookup_by_name "bool" t_env) in 
        (Cst_syntax.TSimple(bool_ident, []), (Public, Untrusted))
    
    (* Return type string for both options IF it was declared as a simple type *)
    | String _ ->
        let string_ident = (Cst_syntax.t_env_lookup_by_name "string" t_env) in 

        (Cst_syntax.TSimple(string_ident, []), (Public, Untrusted))

    (* Return type int for both options IF it was declared as a simple type *)
    | Integer _ ->
        let int_ident = (Cst_syntax.t_env_lookup_by_name "int" t_env) in 

        (Cst_syntax.TSimple(int_ident, []), (Public, Untrusted))

    (* Return type float for both options IF it was declared as a simple type *)
    | Float _ ->
        let float_ident = (Cst_syntax.t_env_lookup_by_name "float" t_env) in 
        (Cst_syntax.TSimple(float_ident, []), (Public, Untrusted))
    | Apply (id, args) ->
        (* if id points to a (Cst_syntax.PassiveAttack), immediately return, 
            as we do not care about typechecking an application of a passive attack *)
        begin match IdentMap.find_opt id t_env with 
        | Some (Cst_syntax.PassiveAttack ) ->
            (Cst_syntax.TUnit, (Lattice_util.Public, Lattice_util.Untrusted))
        | _ -> (
          (* obtain the list of function parameters that `id` takes *)
          let function_input_params, ret_ty, idents_cmd_opt = begin match IdentMap.find_opt id t_env with 
            | Some (Cst_syntax.EqThyFunc(params)) -> 
                let input_params, ret_ty = init_and_last params expr_loc in 
                input_params, ret_ty,  None
            | Some (Cst_syntax.Syscall(idents_x_param_tys, ret_ty, cmd)) -> 
                (* we additionally need to check that this process type is allowed to call this system call `id` *)
                if (not (Sets.SyscallDescSet.mem (Typed.SyscallId id) allowed_syscalls)) then 
                  raise_type_exception_with_location (Format.sprintf 
                  "syscall '%s' is not allowed to be called by this process type" (Ident.string_part id)) expr_loc;


                let param_idents = List.map (fst) idents_x_param_tys in 
                let input_params = List.map (snd) idents_x_param_tys in 
                input_params, ret_ty, Some (param_idents, cmd)
            | Some (Cst_syntax.MemberFunc(idents_x_param_tys, ret_ty, cmd)) -> 
                let param_idents = List.map (fst) idents_x_param_tys in 
                let input_params = List.map (snd) idents_x_param_tys in 
                input_params, ret_ty, Some (param_idents, cmd)
              (* there is no need to typecheck applications of passive attacks, as they are not considered part of the type system *) 
            | _ -> raise (TypeException (Format.sprintf "The symbol %s cannot be applied ; 
                          because it is not an equational theory function syscall or member function" (Ident.name id)))
          end in

          (* arity check *)
          let arity_expected = (List.length function_input_params) in 
          let arity_actual = List.length args in 
          if (arity_expected <> arity_actual) then
              raise (TypeException (Format.sprintf "symbol %s is expected to receive %i arguments but it received %i arguments" (Ident.string_part id) arity_expected arity_actual));
          
          (* Check whether each argument is a subtype of the function parameter type, modulo the return type of function params *)
          let types_of_args = List.map (fun e -> (typeof_expr_rec e t_env)) args in 

          (* for now, we coerce the function parameters to `Cst_syntax.core_security_ty`'s *)
          let input_params_cst = List.map (Cst_syntax.core_sec_f_param_to_core_sec_ty) function_input_params in 

          let args_x_f_params = List.combine types_of_args input_params_cst in
          let all_subtypes = List.for_all (fun (x, y) -> 
            (* print_endline (Cst_syntax.show_Cst_syntax.core_security_ty x);
            print_endline (Cst_syntax.show_Cst_syntax.core_security_ty y); *)
            Cst_syntax.is_subtype secrecy_lattice integrity_lattice x y expr_loc) args_x_f_params in

          if all_subtypes then
            begin match idents_cmd_opt with 
                (* in the case of an equational theory function, simply return the return type *)
                (* TODO infer the return type of a function if it happens to be polymorphic *)
                (* for now, we coerce the return type to `Cst_syntax.core_security_ty` *)
              | None -> Cst_syntax.core_sec_f_param_to_core_sec_ty ret_ty
              | Some (idents, cmd) -> 
                (* we need to add the list of param_idents zipped with the list of types to our environment *)
                (* and then typecheck the cmd under that environment *)

                let t_env' = List.fold_left (fun acc_env (ident, f_param_typ) -> 
                  IdentMap.add ident (Cst_syntax.CST f_param_typ) acc_env
                ) t_env (List.combine idents input_params_cst) in 
                (typeof_cmd ctx cmd t_env')
            end
          else
              (raise_type_exception_with_location 
                (Format.sprintf "some arguments of function application of %s cannot be coerced to the function's parameters" (Ident.string_part id))
                expr_loc)
      )
      end
    | Tuple exprs ->
        if (List.length exprs < 2) then
            (raise_type_exception_with_location "A tuple expression must have at least two expressions" expr_loc);

        let es_typs = List.map (fun e -> (typeof_expr_rec e t_env)) exprs in 

        let (_, (secrecy_lvl1, integrity_lvl1)) = List.hd es_typs in 
        let (_, (secrecy_lvl2, integrity_lvl2)) = List.hd (List.tl es_typs) in 

        (* TODO: _it is really not that ideal that we are computing this information again here_. 
            Ideally, we should just be able to look it up after the pass `To_cst` *)
        (* TODO: don't know what to do in case there is no upper/lower bound *)
        let init_secrecy_lvl = Option.value ~default:secrecy_lvl1 (Lattice_util.join_of_secrecy_lvls ctx.all_process_typs secrecy_lattice secrecy_lvl1 secrecy_lvl2) in 
        let init_integrity_lvl = Option.value ~default:integrity_lvl1 (Lattice_util.meet_of_integrity_lvls ctx.all_process_typs integrity_lattice integrity_lvl1 integrity_lvl2) in 

        let init_tuple_typ = (Cst_syntax.TProd(List.hd es_typs, List.hd (List.tl es_typs)), (init_secrecy_lvl, init_integrity_lvl)) in 

        (* we need to ensure that "(((w * x) * y) * z)" and "(w * (x * (y * z)))"  are interpreted as the same type when typechecking *)
        let resulting_tuple_type = List.fold_left (fun acc_tup_type e_typ -> 
                let (_, (secrecy_lvl_acc, integrity_lvl_acc)) = acc_tup_type in 
                let (_, (e_typ_secrecy_lvl, e_typ_integrity_lvl)) = e_typ in 

                let secrecy_lvl' = Option.value ~default:secrecy_lvl_acc (Lattice_util.join_of_secrecy_lvls ctx.all_process_typs secrecy_lattice secrecy_lvl_acc e_typ_secrecy_lvl) in 
                let integrity_lvl' = Option.value ~default:integrity_lvl_acc (Lattice_util.meet_of_integrity_lvls ctx.all_process_typs integrity_lattice integrity_lvl_acc e_typ_integrity_lvl) in 

                (Cst_syntax.TProd(acc_tup_type, e_typ), (secrecy_lvl', integrity_lvl'))
            ) init_tuple_typ (List.tl (List.tl es_typs)) in 
        resulting_tuple_type



and typeof_cmd (ctx : typechecking_context) (cmd : Cst_syntax.cmd) (t_env : Cst_syntax.typing_env) : Cst_syntax.core_security_ty = 
  let secrecy_lattice = ctx.secrecy_lattice in
  let integrity_lattice = ctx.integrity_lattice in
  let allowed_syscalls = ctx.allowed_syscalls in

  let typeof_expr_rec = (typeof_expr ctx) in 
  let typeof_cmd_rec = (typeof_cmd ctx) in 

  let (cmd_desc, cmd_loc) = cmd in 

  (* lookup msg_with_sig in environment, and print its type if it exists in the environment *)
  
  
    
  (* begin match (IdentMap.find_first_opt (fun ident -> (Ident.string_part ident) == "msg_with_sig") t_env) with 
    | None -> print_endline "msg_with_sig not in environment"
    | Some (_, typ) -> print_endline (Cst_syntax.show_t_env_typ typ)
  end; *)


  match cmd_desc with 

    (* Both options: (unit, (Public, Untrusted)) *)
    | Skip -> (TUnit, (Public, Untrusted))

    (* Both options: typecheck first and then the return type of the second *)
    | Sequence (c1, c2) -> 
        let _ = (typeof_cmd_rec c1 t_env) in 
        (typeof_cmd_rec c2 t_env)
    
    (* Both options: need to check that no "ill-typed" channel facts are `put` *)
       (* need to check that no ill-typed `out` fact exists *)
    | Put facts -> 
      let _ = List.map (fun fact -> 
        typecheck_fact ctx fact t_env ~is_case_fact:false ~fresh_idents:[]) facts
      in
      (TUnit, (Public, Untrusted))

    (* add binding (id, typeof_expr(e)) to t_env, 
        and typecheck cmd with updated t_env *)
    | Let (id, e, c) -> 

        (* if the variable we are assigning to is `msg` *)
        let cst_type = (typeof_expr_rec e t_env) in
  
        let t_env' = IdentMap.add id (Cst_syntax.CST cst_type) t_env in 

        (typeof_cmd ctx c t_env')
    (* Look up `id` in `t_env` and check if typeof_expr(e) = the same *)
    (* then return unit *)
    | Assign (Some id, e) -> 
        let (_, e_loc) = e in 
        let cst_typ = (typeof_expr_rec e t_env) in 
        let looked_up_typ = match IdentMap.find_opt id t_env with 
          | Some typ -> Cst_syntax.coerce_tenv_typ typ cmd_loc
          | None -> raise (TypeException (Format.sprintf "Identifier %s was not present in typing environment t_env" (Ident.string_part id)))
        in
        (* cst_typ must be a subtype of the looked_up_typ *)
        if not (Cst_syntax.is_subtype secrecy_lattice integrity_lattice cst_typ looked_up_typ e_loc) then
            (raise_type_exception_with_location "The type being assigned does not match the type of the variable being assigned" cmd_loc);
        (TUnit, (Public, Untrusted))
    (*  typecheck e 
        THEN return unit IF Ok(...)
    *)
    | Assign (None, e) -> 
        let _ = (typeof_expr_rec e t_env) in 
        (TUnit, (Public, Untrusted))
    (* both cases: typecheck all branches to see that they are well-typed and return the same type *)
    | Case cases -> 

        let types_of_each_branch = List.map (fun (c : Cst_syntax.case) -> (typeof_case ctx c t_env)) cases in 
        let types_of_each_branch_with_locs = List.combine types_of_each_branch (List.map (fun (c : Cst_syntax.case) -> 
          let (_, cmd_loc) = c.cmd in
          cmd_loc
        ) cases) in 
        
        (check_all_types_equal secrecy_lattice integrity_lattice types_of_each_branch_with_locs)

    (* both for "guards" and "untils" : typecheck all branches to see that they are well-typed and return the same result *)
    | While (guards, untils) -> 

      let types_of_each_guard = List.map (fun g -> (typeof_case ctx g t_env)) guards in 
      let types_of_each_guard_with_locs = List.combine types_of_each_guard (List.map (fun (g : Cst_syntax.case) -> 
        let (_, g_cmd_loc) = g.cmd in 
        g_cmd_loc) guards) in 

      let _ = (check_all_types_equal secrecy_lattice integrity_lattice types_of_each_guard_with_locs) in 

      let types_of_each_until = List.map (fun u -> (typeof_case ctx u t_env)) untils in 
      let types_of_each_until_with_locs = List.combine types_of_each_until (List.map (fun (u : Cst_syntax.case) -> 
        let (_, u_cmd_loc) = u.cmd in 
        u_cmd_loc) untils) in 

      check_all_types_equal secrecy_lattice integrity_lattice types_of_each_until_with_locs 


    (* - need to check that no "ill-typed" channel facts are `put`
       - need to check that no ill-typed `out` fact exists *)
    | Event facts ->  
        let _ = List.iter (fun fact -> 
          let _ = typecheck_fact ctx fact t_env ~is_case_fact:false ~fresh_idents:[] in 
          ()
          ) facts in 
        (TUnit, (Public, Untrusted))
    (*  need to return the type of e *)
    | Return e -> 
        (typeof_expr_rec e t_env)
    | New (id, sec_ty_opt, constr_opt, body) ->  
        (* XXX I don't know at this point if I need to do anything at all with `constr_opt` *)
        let sec_ty = match sec_ty_opt with
          | Some ty -> Cst_syntax.CST ty 
          | None -> raise_type_exception_with_location "Any `new` statement must have a typing annotation in order to typecheck sucessfully" cmd_loc 
        in 
        let t_env' = IdentMap.add id sec_ty t_env in 
        typeof_cmd_rec body t_env'

    | Get (ids, e, name, body) ->
        (* XXX do I need to do anything at all with `name`? Such as: register it in my environment? *)
        let (_, e_loc) = e in 
        let tys = (convert_product_type_to_list_of_types (typeof_expr_rec e t_env) e_loc) in 
        if (List.length ids <> List.length tys) then
            raise_type_exception_with_location "Cannot unpack this structure because an incorrect amount of resulting identifiers are given" e_loc;
        
        (* add each new binding to environment *)
        let t_env' = List.fold_left (fun acc_env (id_ord, ty) -> 
            let tenv_ty = Cst_syntax.CST ty in 
            IdentMap.add id_ord tenv_ty acc_env) t_env (List.combine ids tys) in 
        typeof_cmd_rec body t_env' 

    (* Both options: simply need to typecheck `e` and return `unit` *)
    | Del (e, name) ->
        (* XXX do I need to do anything at all with `name`? Such as: check whether it exists or not? *)
        let _ = (typeof_expr_rec e t_env) in 
        (TUnit, (Public, Untrusted))

and typeof_case  (ctx : typechecking_context) (case : Cst_syntax.case) (t_env : Cst_syntax.typing_env) : Cst_syntax.core_security_ty = 
    let secrecy_lattice = ctx.secrecy_lattice in
    let integrity_lattice = ctx.integrity_lattice in
    let allowed_syscalls = ctx.allowed_syscalls in

    let branch_bindings = (List.fold_left (fun acc_bindings fact -> 
      let fact_bindings = (typecheck_fact ctx fact t_env ~is_case_fact:true ~fresh_idents:case.fresh) in 
      acc_bindings @ fact_bindings
    ) [] case.facts) in 

    (* create the updated environment for this particular branch *)
    let branch_env = List.fold_left (fun acc_t_env (fresh_ident, typ) -> 
        IdentMap.add fresh_ident typ acc_t_env
    ) t_env branch_bindings in 

    (* typecheck case.cmd under branch_env *)
    (typeof_cmd ctx case.cmd branch_env)



(* typecheck_fact returns a list of new bindings of (Ident.t * t_env_typ) *)
and typecheck_fact (ctx : typechecking_context) (fact : Cst_syntax.fact) 
  (t_env : Cst_syntax.typing_env) ~(is_case_fact : bool) ~(fresh_idents : Ident.t list) : (Ident.t * Cst_syntax.t_env_typ) list = 
  let secrecy_lattice = ctx.secrecy_lattice in
  let integrity_lattice = ctx.integrity_lattice in
  let allowed_syscalls = ctx.allowed_syscalls in

  let (fact_desc, fact_loc) = fact in 
  match fact_desc with 
  (* E.G. ch::store(arg_1, ..., arg_n) *)
  | Channel {channel = ch ; name ; args} -> begin match (typeof_expr ctx ch t_env) with 
    | (Cst_syntax.TChan(chan_type_params), (_, _)) -> 
      (* arity check ; although we should also have checked this in typer.ml *)
      if (List.length args != List.length chan_type_params) then
        (raise_type_exception_with_location "Channel fact is used with incorrect amount of arguments" fact_loc); 
      let ch_params_x_ch_args = List.combine chan_type_params args in

      if is_case_fact then 
        (* we need to check that: 
        - Any identifiers used `args` are:  
          -- either declared as fresh in `fact.fresh`, or:
          -- are bound in t_env
        - Any other expressions passed from argument to channel are of the correct type
        *)
        (*
        we need to create: 
        - new bindings (<ident>, <type>) for each fresh identifier declared in the fact
        *)
        let bindings = List.fold_left (fun acc_bindings (ch_param_ty, ch_arg) -> 
          let (ch_desc, _) = ch_arg in 
          match ch_desc with 
          | Cst_syntax.Ident { id; param } when List.mem id fresh_idents -> 
            (* if `id` is not in the list of fresh identifiers, AND is not present in the `t_env`, THEN it is unbound *)
            let new_binding = (id, Cst_syntax.CST (ch_param_ty)) in 
            new_binding :: acc_bindings
          | _ -> 
            let type_of_arg = (typeof_expr ctx ch_arg t_env) in 
            if not (Cst_syntax.is_subtype secrecy_lattice integrity_lattice type_of_arg ch_param_ty fact_loc) then 
              (raise_type_exception_with_location "An argument type is not a subtype of the type of the channel" fact_loc);
            acc_bindings
          ) [] ch_params_x_ch_args in 
          bindings
        else
          (* we only need to check that the type of each expression matches the write type of the channel *) 
          let _ = List.iter (fun (ch_param_ty, ch_arg) -> 
              let type_of_arg = (typeof_expr ctx ch_arg t_env) in 

              if not (Cst_syntax.is_subtype secrecy_lattice integrity_lattice type_of_arg ch_param_ty fact_loc) then 
                (raise_type_exception_with_location "An argument type is not a subtype of the type of the channel" fact_loc);
            ) ch_params_x_ch_args in 
          []
    | _ -> (raise_type_exception_with_location "a non-channel expression was used in a channel fact" fact_loc)
    end

  (* I do not know if the `Out` fact actually needs to be typechecked, I think it's safe to ignore *)
  | Out(e) -> failwith "TODO"
  (* In(e) is always well-typed *)
  | In(e) -> []
  (* Plain facts are always well-typed *)
  | Plain(name, es) -> []

  (* Eq and Neq facts are always well-typed *)
  | Eq(e1, e2) -> []
  | Neq(e1, e2) -> []
  (* A File fact [path.contents] is always well-typed *)
  | File{ path ; contents } -> []
  (* A global fact <name>::<es> is always well-typed *)
  | Global(name, es) -> []




let typecheck_process all_process_typs secrecy_lattice integrity_lattice syscall_per_proc_ty vars funcs typ main env : unit = 
  (* add all vars to the environment *)
  let ctx = {
    all_process_typs
    ; secrecy_lattice 
    ; integrity_lattice
    ; allowed_syscalls = match (Maps.IdentMap.find_opt typ syscall_per_proc_ty) with 
      | Some res -> res 
      | None -> Sets.SyscallDescSet.empty
  } in 
  let env' = List.fold_left (fun acc_t_env (var_ident, var_expr) -> 
      let type_of_var = (Cst_syntax.CST (typeof_expr ctx var_expr acc_t_env)) in 
      IdentMap.add var_ident type_of_var acc_t_env
    ) env vars in 

  (* add all member funcs to the environment *)
  let env'' = List.fold_left (fun acc_t_env (fun_ident, idents_x_params, ret_param, cmd) -> 
      (* We do not typecheck the body cmd here, but only typecheck it when the 
      process code calls it
      *)
      let member_func_t_env_typ = Cst_syntax.MemberFunc(idents_x_params, ret_param, cmd) in 
      IdentMap.add fun_ident member_func_t_env_typ acc_t_env
    ) env' funcs in
  
  (* typecheck the cmd of the process under the update env'' *)
  let _ = typeof_cmd ctx main env'' in 
  ()


let typecheck_sys (prog : Cst_syntax.core_rabbit_prog) : unit = 

  (* print_endline "secrecy lattice for this typechecking problem:";
  Lattice_util.pp_cst_access_policy (Format.get_std_formatter ()) secrecy_lattice;

  print_endline "integrity lattice for this typechecking problem:";
  Lattice_util.pp_cst_access_policy (Format.get_std_formatter ()) integrity_lattice;     *)

  let (proc_instantiations, system_loc) = prog.system in 

  
  let (proc_instantiations, system_loc) = prog.system in 
  let system_env = prog.typing_env in 
  let all_process_typs = prog.all_process_typs in 
  let secrecy_lattice = prog.secrecy_lattice in 
  let integrity_lattice = prog.integrity_lattice in 
  let syscall_per_proc_ty = prog.syscall_per_proc_ty in 

  List.iter (fun proc_instantiation -> 
    let (proc_ident, arg_idents) = proc_instantiation in 
    
    (* lookup proc_ident in environment *)
    match IdentMap.find_opt proc_ident system_env with
      | Some (Cst_syntax.Process { id ; process_params ; typ ; vars ; funcs ; main ; _ }) -> 
          if (List.length arg_idents != List.length process_params) then
            (raise_type_exception_with_location 
              (Format.sprintf "The amount of arguments supplied to process %s does not match the amount of process parameters" (Ident.string_part id)) system_loc);
          let args_idents_x_proc_params = List.combine arg_idents process_params in
          
          (* for each ident \in arg_idents, we need to check that its type is a subtype of the parameter type of the process *)
          let env' = List.fold_left (fun acc_env (arg_ident, (proc_param_ident, proc_param_typ)) ->  
              begin match (IdentMap.find_opt arg_ident system_env) with 
                | Some (arg_ident_typ) -> 

                  (* check that arg_ident_typ is a subtype of proc_param_typ *)
                  let proc_param_cst = 
                    Cst_syntax.core_sec_f_param_to_core_sec_ty proc_param_typ in 
                  let arg_ident_typ_cst = Cst_syntax.coerce_tenv_typ arg_ident_typ system_loc in 

                  if not (Cst_syntax.is_subtype secrecy_lattice integrity_lattice arg_ident_typ_cst proc_param_cst system_loc) then 
                    (raise_type_exception_with_location "An argument type is not a subtype of the type of the channel" system_loc);
                  IdentMap.add proc_param_ident (Cst_syntax.CST proc_param_cst) acc_env

                | None -> raise (TypeException "An argument in the system declaration was not found in the system_env")
              end
            ) system_env args_idents_x_proc_params in 
          (typecheck_process all_process_typs secrecy_lattice integrity_lattice syscall_per_proc_ty vars funcs typ main env');
      | _ -> (raise_type_exception_with_location "This proc_ident does not exist in the system environment" system_loc)
  ) proc_instantiations;