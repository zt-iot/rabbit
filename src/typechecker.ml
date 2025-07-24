open Cst_util

exception TypeException of string


let raise_type_exception_with_location msg loc = 
    Location.print loc Format.std_formatter;
    Format.pp_print_newline Format.std_formatter ();
    raise (TypeException msg)



type t_env_typ = 
  | CST of Cst_env.core_security_type
  | FunT of Cst_env.core_security_type list (* Just to be able to have bindings in `t_env` whose value is a function type, possibly with `cmd` code. This should never be actually returned from 
    typechecker.ml, because Rabbit does not support higher-order functions *)


(* a Map from Ident.t to Cst_env.core_security_type *)
(* because we Map from Ident.t to t_env_typ, we should not encounter any problems with name shadowing *)
type typing_env = t_env_typ Maps.IdentMap.t


let cst_to_tenv_typ (typ : Cst_env.core_security_type) : t_env_typ =
  CST typ

let coerce_tenv_typ (typ : t_env_typ) : Cst_env.core_security_type =
  match typ with
  | CST t -> t
  | FunT _ -> raise (TypeException "FunT cannot be converted to core_security_type")




let rec coerce_fun_param (param : Cst_env.core_security_function_param) : Cst_env.core_security_type =
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
  | (CFP_Dummy, lvl) -> (Dummy, lvl)
  (* currently fails if the function parameter is polymorphic. Eventually, we'd want to implement proper conversion *)
  | (CFP_Poly _, _) ->
      raise (TypeException "CFP_Poly cannot be coerced to core_security_type")




let rec typeof_expr (secrecy_lattice : cst_access_policy)
  (integrity_lattice : cst_access_policy) (expr : Cst_syntax.expr) (t_env : typing_env) : Cst_env.core_security_type = 
  let typeof_expr_rec = (typeof_expr secrecy_lattice integrity_lattice) in 
  match expr.desc with

    (* Need to look up type in `t_env` *)
    | Ident { id; desc; param } ->
        (* Look up the type of `id` in the typing environment t_env *)
         begin match Maps.IdentMap.find_opt id t_env with 
          | Some t -> (coerce_tenv_typ t) 
          | None -> (raise_type_exception_with_location (Format.sprintf "No entry for the following Ident.t: %s" (Ident.name id)) expr.loc)
         end
    (* Return type bool for both options IF it was declared as simple type *)
    | Boolean _ -> 

        (* Need to check that `bool` was actually declared as a simple type *)
        let _ = begin match (Cst_env.find_opt expr.env "bool") with 
          | Some ((_, Cst_env.SimpleTypeDef([]))) -> ()
          | _ -> (raise_type_exception_with_location "type bool was not declared as a simple type in this program" expr.Cst_syntax.loc)
        end in 

        (Cst_env.TSimple("bool", []), (Public, Untrusted))
    
    (* Return type string for both options IF it was declared as a simple type *)
    | String _ ->
        (* Need to check that `string` was actually declared as a simple type *)
        let _ = begin match (Cst_env.find_opt expr.env "string") with 
          | Some ((_, Cst_env.SimpleTypeDef([]))) -> ()
          | _ -> (raise_type_exception_with_location "type string was not declared as a simple type in this program" expr.Cst_syntax.loc)
        end in 

        (Cst_env.TSimple("string", []), (Public, Untrusted))

    (* Return type int for both options IF it was declared as a simple type *)
    | Integer _ ->
        (* Need to check that `int` was actually declared as a simple type *)
        let _ = begin match (Cst_env.find_opt expr.env "int") with 
          | Some ((_, Cst_env.SimpleTypeDef([]))) -> ()
          | _ -> (raise_type_exception_with_location "type int was not declared as a simple type in this program" expr.Cst_syntax.loc)
        end in 

        (Cst_env.TSimple("int", []), (Public, Untrusted))

    (* Return type float for both options IF it was declared as a simple type *)
    | Float _ ->
        (* Need to check that `float` was actually declared as a simple type *)
        let _ = begin match (Cst_env.find_opt expr.env "float") with 
          | Some ((_, Cst_env.SimpleTypeDef([]))) -> ()
          | _ -> (raise_type_exception_with_location "type float was not declared as a simple type in this program" expr.Cst_syntax.loc)
        end in 

        (Cst_env.TSimple("float", []), (Public, Untrusted))

    (* Option 1: Look up typing signature of `id` in Cst_env.t, 
        then look up types of args in `Cst_env.t` and see if they match *)
    (* Option 2: Look up typing signature of `id` in Cst_env.t, 
        then look up types of args in `t_env` and see if they match *)
    | Apply (id, args) ->
        (* obtain the list of function parameters that `id` accepts *)
        let function_params = begin match Cst_env.find_opt_by_id expr.env id with 
          | Some (Cst_env.ExtFun(params)) -> params
          | Some (Cst_env.ExtSyscall(params)) -> params 
          | Some (Cst_env.MemberFunc(params)) -> params
          | _ -> raise (TypeException (Format.sprintf "The symbol %s cannot be applied ; 
                        because it is not an equational theory function syscall or member function" (Ident.name id)))
        end in 
        
        (* OCaml provides no easy way to retrieve the last element of a list, so this has to be done *)
        let init_and_last lst =
            let rec aux acc = function
                | [] -> raise (TypeException (Format.sprintf "function parameter list of %s is empty, which should not be possible" (Ident.string_part id)))
                | [x] -> (List.rev acc, x)
                | x :: xs -> aux (x :: acc) xs
            in
            aux [] lst
        in
        let function_params_input, ret_ty = init_and_last function_params in 

        (* arity check *)
        (* (this should have been checked for already in `typer.ml/desugarer.ml`, but I'm just doing it again here )*)
        let arity_expected = (List.length function_params) - 1 (* minus one, because we don't count the return type as input type *) in 
        let arity_actual = List.length args in 
        if (arity_expected <> arity_actual) then
            raise (TypeException (Format.sprintf "symbol %s is expected to receive %i arguments but it received %i arguments" (Ident.string_part id) arity_expected arity_actual));


        
        
        (* Check whether each argument is a subtype of the function parameter type, modulo the return type of function params *)
        let types_of_args = List.map (fun e -> (typeof_expr_rec e t_env)) args in 

        (* TODO handle substitution of concrete types for polymorphic types *)
        (* for now, we coerce the function parameters to `core_security_type`'s *)
        let types_of_function_params = List.map (coerce_fun_param) function_params_input in 
        
        
        let args_x_f_params = List.combine types_of_args types_of_function_params in
        let all_subtypes = List.for_all (fun (x, y) -> 
          print_endline (Cst_env.show_core_security_type x);
          print_endline (Cst_env.show_core_security_type y);
          is_subtype secrecy_lattice integrity_lattice x y) args_x_f_params in

        if all_subtypes then
            (* TODO infer the return type of a function if it happens to be polymorphic *)
              (* for now, we coerce the return type to `core_security_type` *)
            coerce_fun_param ret_ty
        else
            raise (TypeException (Format.sprintf "function parameter list of %s did not match types of the arguments" (Ident.string_part id)))

    | Tuple exprs ->
        if (List.length exprs < 2) then
            (raise_type_exception_with_location "A tuple expression must have at least two expressions" expr.Cst_syntax.loc);

        let es_typs = List.map (fun e -> (typeof_expr_rec e t_env)) exprs in 

        let (_, (secrecy_lvl1, integrity_lvl1)) = List.hd es_typs in 
        let (_, (secrecy_lvl2, integrity_lvl2)) = List.hd (List.tl es_typs) in 

        (* TODO: _it is really not that ideal that we are computing this information again here_. 
            Ideally, we should just be able to look it up after the pass `To_cst` *)
        (* TODO: don't know what to do in case there is no upper/lower bound *)
        let init_secrecy_lvl = Option.value ~default:secrecy_lvl1 (To_cst.join_of_secrecy_lvls secrecy_lattice secrecy_lvl1 secrecy_lvl2) in 
        let init_integrity_lvl = Option.value ~default:integrity_lvl1 (To_cst.meet_of_integrity_lvls integrity_lattice integrity_lvl1 integrity_lvl2) in 

        let init_tuple_typ = (Cst_env.TProd(List.hd es_typs, List.hd (List.tl es_typs)), (init_secrecy_lvl, init_integrity_lvl)) in 

        (* we need to ensure that "(((w * x) * y) * z)" and "(w * (x * (y * z)))"  are interpreted as the same type when typechecking *)
        let resulting_tuple_type = List.fold_left (fun acc_tup_type e_typ -> 
                let (_, (secrecy_lvl_acc, integrity_lvl_acc)) = acc_tup_type in 
                let (_, (e_typ_secrecy_lvl, e_typ_integrity_lvl)) = e_typ in 

                let secrecy_lvl' = Option.value ~default:secrecy_lvl_acc (To_cst.join_of_secrecy_lvls secrecy_lattice secrecy_lvl_acc e_typ_secrecy_lvl) in 
                let integrity_lvl' = Option.value ~default:integrity_lvl_acc (To_cst.meet_of_integrity_lvls integrity_lattice integrity_lvl_acc e_typ_integrity_lvl) in 

                (Cst_env.TProd(acc_tup_type, e_typ), (secrecy_lvl', integrity_lvl'))
            ) init_tuple_typ (List.tl (List.tl es_typs)) in 
        resulting_tuple_type

    (* Both options: return type (unit, (Public, Untrusted)) *)
    | Unit ->
        (Dummy, (Public, Untrusted))




let typecheck_fact (secrecy_lattice : cst_access_policy) 
  (integrity_lattice : cst_access_policy) (fact : Cst_syntax.fact) 
  (t_env : typing_env) : unit = match fact.desc with 
  | Channel {channel ; name ; args} -> failwith "TODO"
  | Out(e) -> failwith "TODO"

  (* In(e) is always well-typed *)
  | In(e) -> ()
  (* Plain facts are always well-typed *)
  | Plain(name, es) -> ()

  (* Eq and Neq facts are always well-typed *)
  | Eq(e1, e2) -> ()
  | Neq(e1, e2) -> ()
  (* A File fact [path.contents] is always well-typed *)
  | File{ path ; contents } -> ()
  (* A global fact <name>::<es> is always well-typed *)
  | Global(name, es) -> ()



let rec convert_product_type_to_list_of_types (prod_type : Cst_env.core_security_type) (loc : Location.t) : Cst_env.core_security_type list = begin match prod_type with 
  | (Cst_env.TProd(t1, t2), (_, _)) -> 
    let t1_tys = convert_product_type_to_list_of_types t1 loc in 
    let t2_tys = convert_product_type_to_list_of_types t2 loc in 
    t1_tys @ t2_tys
  | t -> [t]
  end


(* typecheck a list of commands and check that they all return the same type *)
let rec check_cmds_return_same_type (secrecy_lattice : cst_access_policy)
  (integrity_lattice : cst_access_policy) (cmds : Cst_syntax.cmd list) (loc : Location.t) (t_env : typing_env) : Cst_env.core_security_type = 
  let typeof_cmd_rec = (typeof_cmd secrecy_lattice integrity_lattice) in 
  begin
    match cmds with 
    | [] -> (raise_type_exception_with_location "empty case or repeat statement" loc)
    | c1 :: cmds' -> 
        let ty1 = (typeof_cmd_rec c1 t_env) in 
        List.iter(fun (c : Cst_syntax.cmd) -> 
                    let ty' = typeof_cmd_rec c t_env in
                    (* For now, ty' must be a subtype of ty1, but we can _probably_ be more relaxed *)
                    if not (is_subtype secrecy_lattice integrity_lattice ty' ty1) then 
                        (raise_type_exception_with_location "All branches of a case/repeat statement must return the same type" loc)
                ) cmds';
        ty1
  end


and typeof_cmd  (secrecy_lattice : cst_access_policy)
  (integrity_lattice : cst_access_policy) (cmd : Cst_syntax.cmd) (t_env : typing_env) : Cst_env.core_security_type = 
  let typeof_expr_rec = (typeof_expr secrecy_lattice integrity_lattice) in 
  let typeof_cmd_rec = (typeof_cmd secrecy_lattice integrity_lattice) in 
  let typecheck_fact_rec = (typecheck_fact secrecy_lattice integrity_lattice) in 
  match cmd.Cst_syntax.desc with 
    (* Both options: (unit, (Public, Untrusted)) *)
    | Skip -> (TUnit, (Public, Untrusted))
    (* Both options: typecheck first and then the return type of the second *)
    | Sequence (c1, c2) -> 
        let _ = (typeof_cmd_rec c1 t_env) in 
        (typeof_cmd_rec c2 t_env)
    (* Both options: need to check that no "ill-typed" channel facts are `put` *)
       (* need to check that no ill-typed `out` fact exists *)
    | Put facts -> 
      List.iter(fun fact -> typecheck_fact_rec fact t_env) facts;
      (TUnit, (Public, Untrusted))

    (* add binding (id, typeof_expr(e)) to t_env, 
        and typecheck cmd with updated t_env *)
    | Let (id, e, c) -> 

        (* if the variable we are assigning to is `msg` *)
        let cst_type = (typeof_expr_rec e t_env) in
        let t_env' = Maps.IdentMap.add id (cst_to_tenv_typ cst_type) t_env in 
        (typeof_cmd_rec c t_env')
    (* Look up `id` in `t_env` and check if typeof_expr(e) = the same *)
    (* then return unit *)
    | Assign (Some id, e) -> 
        let cst_typ = (typeof_expr_rec e t_env) in 
        let looked_up_typ = match Maps.IdentMap.find_opt id t_env with 
          | Some typ -> coerce_tenv_typ typ
          | None -> raise (TypeException (Format.sprintf "Identifier %s was not present in typing environment t_env" (Ident.string_part id)))
        in
        (* cst_typ must be a subtype of the looked_up_typ *)
        if not (is_subtype secrecy_lattice integrity_lattice cst_typ looked_up_typ) then
            (raise_type_exception_with_location "The type being assigned does not match the type of the variable being assigned" cmd.Cst_syntax.loc);
        (TUnit, (Public, Untrusted))
    (*  typecheck e 
        THEN return unit IF Ok(...)
    *)
    | Assign (None, e) -> 
        let _ = (typeof_expr_rec e t_env) in 
        (TUnit, (Public, Untrusted))
    (* both cases: typecheck all branches to see that they are well-typed and return the same type *)
    | Case cases ->  
        let cmds = List.map (fun (c : Cst_syntax.case) -> c.cmd) cases in 
        (check_cmds_return_same_type secrecy_lattice integrity_lattice cmds cmd.loc t_env)
    (* both cases: typecheck all branches to see that they are well-typed and return the same result *)
    | While (guards, untils) -> 
      let guards_cmds = List.map (fun (c : Cst_syntax.case) -> c.cmd) guards in 
      let untils_cmds = List.map (fun (u : Cst_syntax.case) -> u.cmd) untils in 
      let _ = (check_cmds_return_same_type secrecy_lattice integrity_lattice guards_cmds cmd.loc t_env) in
      check_cmds_return_same_type secrecy_lattice integrity_lattice untils_cmds cmd.loc t_env
    (* - need to check that no "ill-typed" channel facts are `put`
       - need to check that no ill-typed `out` fact exists *)
    | Event facts ->  
        List.iter (fun f -> (typecheck_fact secrecy_lattice integrity_lattice f t_env) ) facts;
        (TUnit, (Public, Untrusted))
    (*  need to return the type of e *)
    | Return e -> 
        (typeof_expr_rec e t_env)
    (* Option 1: Simply return the type of body. 
        IF (typing information was present) -> We assume that 
        that `(id, sec_ty)` is already in Cst_env. 
        ELSE -> No typing information was present and typechecking will fail when `id` gets read *)
    (* Option 2: Add binding (id, sec_ty) to `t_env`, and return the type of `body` *)
    | New (id, sec_ty_opt, constr_opt, body) ->  
        (* XXX I don't know at this point if I need to do anything at all with `constr_opt` *)
        let sec_ty = match sec_ty_opt with
          | Some ty -> cst_to_tenv_typ ty 
          | None -> raise_type_exception_with_location "Any `new` statement must have a typing annotation in order to typecheck sucessfully" cmd.loc 
        in 
        let t_env' = Maps.IdentMap.add id sec_ty t_env in 
        typeof_cmd_rec body t_env'
    
    (* Option 1: we assume that bindings `(id_1 : ty_1), ..., (id_n : ty_n)` are already there. We 
    simply need to return the type of the body *)
    (* Option 2: add bindings `(id_1 : ty_1), ..., (id_n : ty_n)` to `t_env`, and return the type of the body *)
    | Get (ids, e, name, body) ->
        (* XXX do I need to do anything at all with `name`? Such as: register it in my environment? *)
        let tys = (convert_product_type_to_list_of_types (typeof_expr_rec e t_env) e.loc) in 
        if (List.length ids <> List.length tys) then
            raise_type_exception_with_location "Cannot unpack this structure because an incorrect amount of resulting identifiers are given" e.loc;
        
        (* add each new binding to environment *)
        let t_env' = List.fold_left (fun acc_env (id_ord, ty) -> 
            let tenv_ty = cst_to_tenv_typ ty in 
            Maps.IdentMap.add id_ord tenv_ty acc_env) t_env (List.combine ids tys) in 
        typeof_cmd_rec body t_env' 

    (* Both options: simply need to typecheck `e` and return `unit` *)
    | Del (e, name) ->
        (* XXX do I need to do anything at all with `name`? Such as: check whether it exists or not? *)
        let _ = (typeof_expr_rec e t_env) in 
        (TUnit, (Public, Untrusted))


let create_initial_t_env (cst_env : Cst_env.t) : typing_env = 
  let handle_desc (d : Cst_env.desc) : t_env_typ option =
    begin match d with
    | SimpleTypeDef _ -> None
    | Var (_, cst_ty_opt) -> Option.map cst_to_tenv_typ cst_ty_opt
    | ExtFun fps -> Some (FunT (List.map coerce_fun_param fps))
    | ExtSyscall fps -> Some (FunT (List.map coerce_fun_param fps))
    | MemberFunc fps -> Some (FunT (List.map coerce_fun_param fps))
    | Const (_, cst_ty) -> Some (cst_to_tenv_typ cst_ty)

    (* TODO: I don't understand if I need to return a `Some` here *)
    | ChannelDecl (_, chan_ty_ident) -> None
    | Attack -> None
    | ProcTypeDef -> None
    | FilesysTypeDef -> None

    (* TODO: I don't understand if I need to return a `Some` here *)
    | ChanTypeDef _ -> None
    | SecurityTypeDef _ -> None
    | Process -> None
  end in 
  List.fold_left (fun acc_t_env (id, desc) -> 
    let t_env_typ_opt = (handle_desc desc) in 
    begin match t_env_typ_opt with 
      | Some typ -> (Maps.IdentMap.add id typ acc_t_env)
      | None -> acc_t_env
    end
    ) Maps.IdentMap.empty cst_env.vars


(* let extend_t_env_with_args (t_env : typing_env) : typing_env =  *)




let typecheck_decl (secrecy_lattice : cst_access_policy)
  (integrity_lattice : cst_access_policy) (decl : Cst_syntax.decl) : unit = 
  let typeof_expr_rec = (typeof_expr secrecy_lattice integrity_lattice) in 
  let typeof_cmd_rec = (typeof_cmd secrecy_lattice integrity_lattice) in 


  let initial_tenv = create_initial_t_env decl.env in 
  begin match decl.Cst_syntax.desc with 
  | Cst_syntax.Syscall {id; args; fun_params; cmd} ->
    (* It is necessary to typecheck the cmd of syscall:
       1.) To ensure that there are no typing violations
       2.) To ensure that the return type is equal to the type that was put in the function signature *)


      let bindings = List.combine args (List.map (fun x -> cst_to_tenv_typ (coerce_fun_param x)) fun_params) in 

      let t_env = List.fold_left (fun acc_t_env (id, t_env_typ) ->  
        Maps.IdentMap.add id t_env_typ acc_t_env
        ) initial_tenv bindings in 

      (* CURRENT SETUP: we typecheck the body of a Cst_syntax.Syscall at this point ONCE under the assumption that we trust the typing signature *)
      (* then in `typecheck_cmd` we only check whether the list of arguments matches the list of function parameters  *)
      let _ = typeof_cmd_rec cmd t_env 
      in () 


  | Cst_syntax.Attack _ ->
      (* failwith "TODO: not sure if Cst_syntax.Attack needs to be typechecked"; *)
      (* For now, we consider all active attacks to be well-typed *)
      ()

  | Cst_syntax.Process { id; args; vars; funcs; main; _ } ->


      (* we need to update the `t_env` such that: 
        - channel args are added to t_env
           (let's see _which_ type I need to add in order to make this work... )
        - each var is added to `t_env` with the type of its expression
        - each member `func` is added to `t_env` with its typing signature
      *)

      (* add `args` channel args to t_env *)
      let t_env' = List.fold_left (fun acc_t_env (arg : Typed.chan_param) -> 
        (* For some reason, OCaml will keep complaining that `channel` is unbound of a `Typed.chan_param`, so I have to do a useless pattern match like this *)
        begin match arg with
          | {channel = channel_id ; typ = typ_id ; _ } -> 
            let t_params = begin match Cst_env.find_opt decl.env (Ident.string_part typ_id) with 
              | Some (_, Cst_env.ChanTypeDef(params)) -> params 
              | _ -> (raise_type_exception_with_location 
                      (Format.sprintf "%s was not created as a channel type definition" (Ident.string_part typ_id))
                      decl.loc
                      )
            end in 
            (* add binding to the t_env_acc *)
            let resulting_typ = CST (Cst_env.TChan t_params, (Public, Untrusted)) in 
            Maps.IdentMap.add channel_id resulting_typ acc_t_env
        end
        ) initial_tenv args in 

      (* add each var \in vars to t_env *)

      let t_env'' = List.fold_left (fun acc_t_env (var_ident, var_expr) -> 
        (* Use the accumulated env to type the expression *)
        let resulting_typ = CST ((typeof_expr_rec var_expr acc_t_env)) in 
          Maps.IdentMap.add var_ident resulting_typ acc_t_env  
        ) t_env' vars in 

      
      (* CURRENT SETUP: we typecheck the body of a member function ONCE, under the assumption that we trust the typing signature*)
      (* then in `typecheck_cmd`, we only check whether the list of arguments matches the list of function parameters *)

      (* typecheck the cmd of each member function *)
      let typeof_member_func (func : Ident.t * (Ident.t * Cst_env.core_security_function_param) list * Cst_syntax.cmd) 
        : Cst_env.core_security_type = 
         let (_, fun_ids_and_param_typs, fun_cmd) = func in 
         let t_env''' = List.fold_left (fun acc_t_env (member_fun_param_id, member_fun_param_typ) -> 
           let t_env_typ = cst_to_tenv_typ (coerce_fun_param (member_fun_param_typ)) in 
           Maps.IdentMap.add member_fun_param_id t_env_typ acc_t_env
         ) t_env'' fun_ids_and_param_typs in 
         (typeof_cmd_rec fun_cmd t_env''')
      in

      let _ = List.map (typeof_member_func) funcs in 

      (* it is not necessary to add the typing signature of a function to the t_env *)
      (* that information is already present in the Cst_env.t *)

      
      (print_endline (Format.sprintf "Running typeof_cmd on process name %s" (Ident.string_part id)));

      let _ = (typeof_cmd_rec main t_env'') in ()

  | Cst_syntax.System _ ->
      raise (TypeException "A Rabbit program with multiple `system` declarations is ill-typed ")
  end


let typecheck_sys (cst_decls : Cst_syntax.decl list) 
  (sys : Cst_syntax.decl) (secrecy_lattice : cst_access_policy)
  (integrity_lattice : cst_access_policy) : unit = match sys.Cst_syntax.desc with 
  | Cst_syntax.System(proc_strs) ->

    (* for all `proc_name` \in `procs`, we need to check that `proc_name` is well-typed *)

    (* get only the declarations for which their name appears in `proc_strs` *)
    let filtered_decls =
      List.filter (fun decl -> match decl.Cst_syntax.desc with
        | Cst_syntax.Process { id; _ } -> List.mem (Ident.string_part id) proc_strs
        | _ -> false  (* keep all non-process declarations *)
      ) cst_decls in 

    (print_endline "typecheck sys : printing filtered_decls process names");
    List.iter (fun decl -> match decl.Cst_syntax.desc with 
        | Cst_syntax.Process { id; _ } -> print_endline (Ident.string_part id) 
        | _ -> ()
    ) filtered_decls;

    
    (* typecheck each decl of filtered_decls *)
    List.iter (fun decl -> 
        typecheck_decl secrecy_lattice integrity_lattice decl) filtered_decls;
  | _ -> assert true