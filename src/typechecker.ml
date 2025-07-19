

exception TypeException of string


type typing_env = Cst_env.core_security_type Maps.IdentMap.t


let rec typeof_expr (secrecy_lattice : To_cst.cst_access_policy)
  (integrity_lattice : To_cst.cst_access_policy) (expr : Cst_syntax.expr) (t_env : typing_env) : Cst_env.core_security_type = 
  let typeof_expr_rec = (typeof_expr secrecy_lattice integrity_lattice) in 
  match expr.desc with

    (* Option 1: Need to look up type in `Cst_env.t` *)
    (* Option 2: Need to look up type in `t_env` *)
    | Ident { id; desc; param } ->
         begin match Maps.IdentMap.find_opt id t_env with 
          | Some t -> t 
          | None -> raise (TypeException (Format.sprintf "No entry for the following Ident.t: %s" (Ident.name id)))
         end
    (* Return type bool for both options IF it was declared as simple type *)
    | Boolean b ->
        (* Handle boolean *)
        (Dummy, (S_Ignore, I_Ignore))

    (* Return type string for both options IF it was declared as a simple type *)
    | String s ->
        (* Handle string *)
        (Dummy, (S_Ignore, I_Ignore))

    (* Return type int for both options IF it was declared as a simple type *)
    | Integer i ->
        (* Handle integer *)
        (Dummy, (S_Ignore, I_Ignore))

    (* Return type float for both options IF it was declared as a simple type *)
    | Float f ->
        (* Handle float *)
        (Dummy, (S_Ignore, I_Ignore))

    (* Option 1: Look up typing signature of `id` in Cst_env.t, 
        then look up types of args in `Cst_env.t` and see if they match *)
    (* Option 2: Look up typing signature of `id` in Cst_env.t, 
        then look up types of args in `t_env` and see if they match *)
    | Apply (id, args) ->
        (* get the list of function parameters that `id` accepts *)
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
        (* TODO handle substitution of concrete types for polymorphic types *)
        (* arity check *)
        (* (this should have been checked for already in `typer.ml/desugarer.ml`, but I'm just doing it again here )*)
        let arity_expected = (List.length function_params) - 1 (* minus one, because we don't count the return type as input type *) in 
        let arity_actual = List.length args in 
        if (arity_expected <> arity_actual) then
            raise (TypeException (Format.sprintf "symbol %s is expected to receive %i arguments but it received %i arguments" (Ident.string_part id) arity_expected arity_actual));
        
        (* Check equality of function parameter types and given types, modulo the return type of function params *)
        let function_params_of_args = List.map (fun e -> Cst_env.cst_to_csfp (typeof_expr_rec e t_env)) args in 
        let zipped = List.combine function_params_input function_params_of_args in
        let all_match = List.for_all (fun (x, y) -> x = y) zipped in

        if all_match then
            (* TODO infer the return type of a function if it happens to be polymorphic *)
            (* ret_ty *)
        
            (Dummy, (S_Ignore, I_Ignore))
        else
            raise (TypeException (Format.sprintf "function parameter list of %s did not match types of the arguments" (Ident.string_part id)))


    (* Option 1: Look up typing information of all expressions in `Cst_env.t` *)
    (* Option 2: Look up typing information of all expressions in `t_env` *)
    | Tuple exprs ->
        (* Handle tuple *)
        (Dummy, (S_Ignore, I_Ignore))

    (* Both options: return type (unit, (Public, Untrusted)) *)
    | Unit ->
        (* Handle unit *)
        (Dummy, (S_Ignore, I_Ignore))


let rec typeof_cmd  (secrecy_lattice : To_cst.cst_access_policy)
  (integrity_lattice : To_cst.cst_access_policy) (cmd : Cst_syntax.cmd) (t_env : typing_env) : Cst_env.core_security_type = 
  let typeof_expr_rec = (typeof_expr secrecy_lattice integrity_lattice) in 
  let typeof_cmd_rec = (typeof_cmd secrecy_lattice integrity_lattice) in 
  match cmd.Cst_syntax.desc with 
    (* Both options: (unit, (Public, Untrusted)) *)
    | Skip -> (TUnit, (Public, Untrusted))
    (* Both options: typecheck first and then the return type of the second *)
    | Sequence (c1, c2) -> 
        let _ = (typeof_cmd secrecy_lattice integrity_lattice c1) in 
        (typeof_cmd_rec c2 t_env)
    (* Both options: need to check that no "ill-typed" channel facts are `put` *)
       (* need to check that no ill-typed `out` fact exists *)
    | Put facts -> (Dummy, (S_Ignore, I_Ignore))

    (* Option 1: we cannot check if `type_expr(e) equals the one in Cst_env.t, 
        because Cst_env.t will not yet contain a binding for `id` *)
    (* Option 2: add binding (id, typeof_expr(e)) to t_env, 
        and typecheck cmd with updated t_env *)
    | Let (id, e, c) -> 
        (* if the variable we are assigning to is `msg` *)
        let _ = (typeof_expr_rec e t_env) in
        (typeof_cmd_rec c t_env)
    (* Option 1: Look up `id` in Cst_env.t and check if typeof_expr(e) = the same *)
    (* Option 2: Look up `id` in `t_env` and check if typeof_expr(e) = the same *)
    (* THEN both options: return unit *)
    | Assign (Some id, e) -> 
        let _ = (typeof_expr_rec e t_env) in 
        (TUnit, (Public, Untrusted))
    (* Both options: typecheck e 
        THEN return unit IF Ok(...)
    *)
    | Assign (None, e) -> 
        print_endline (Cst_syntax.show_expr e);
        let _ = (typeof_expr_rec e t_env) in 
        (TUnit, (Public, Untrusted))
    (* both cases: typecheck all branches to see that they are well-typed and return the same type *)
    | Case cases ->  (Dummy, (S_Ignore, I_Ignore))
    (* both cases: typecheck all branches to see that they are well-typed and return the same result *)
    | While (guards, untils) -> (Dummy, (S_Ignore, I_Ignore))
    (* Both options: need to check that no "ill-typed" channel facts are `put` *)
       (* need to check that no ill-typed `out` fact exists *)
    | Event facts ->  (Dummy, (S_Ignore, I_Ignore))
    (* both cases: need to return the type of e *)
    | Return e ->  (Dummy, (S_Ignore, I_Ignore))

    (* Option 1: Simply return the type of body. 
        IF (typing information was present) -> We assume that 
        that `(id, sec_ty)` is already in Cst_env. 
        ELSE -> No typing information was present and typechecking will fail when `id` gets read *)
    (* Option 2: Add binding (id, sec_ty) to `t_env`, and return the type of `body` *)
    | New (id, sec_ty_opt, constr_opt, body) ->  (Dummy, (S_Ignore, I_Ignore))
    
    (* Option 1: we assume that bindings `(id_1 : ty_1), ..., (id_n : ty_n)` are already there. We 
    simply need to return the type of the body *)
    (* Option 2: add bindings `(id_1 : ty_1), ..., (id_n : ty_n)` to `t_env`, and return the type of the body *)
    | Get (ids, e, name, body) -> (Dummy, (S_Ignore, I_Ignore))

    (* Both options: simply need to typecheck `e` and return `unit` *)
    | Del (e, name) ->  (Dummy, (S_Ignore, I_Ignore))


let typecheck_decl (secrecy_lattice : To_cst.cst_access_policy)
  (integrity_lattice : To_cst.cst_access_policy) (decl : Cst_syntax.decl) (t_env : typing_env) : unit = 
  let typeof_expr_rec = (typeof_expr secrecy_lattice integrity_lattice) in 
  let typeof_cmd_rec = (typeof_cmd secrecy_lattice integrity_lattice) in 
  match decl.Cst_syntax.desc with 
  | Cst_syntax.Syscall {id; args; cmd} ->
      (* Option 2: we should simply add the syscall with args and cmd to our `t_env`, and we can retrieve the 
      `args` and `cmd` later when we are typechecking a `cmd` or `expr`
      *) 

      (* TODO on Sunday: add Syscall(args, cmd) to the `t_env` somehow or create a new environment for function. I just want a working typechecker, I don't care about the code quality up until then *)
      let updated_t_env = Maps.IdentMap.add id (* TODO *) in
      () 

  | Cst_syntax.Attack _ ->
      (* failwith "TODO: not sure if Cst_syntax.Attack needs to be typechecked"; *)
      ()

  | Cst_syntax.Process { id; main; _ } ->
      (print_endline (Format.sprintf "Running typeof_cmd on process name %s" (Ident.string_part id)));
      (* we should only need to typecheck the Process decl *)
      let _ = (typeof_cmd_rec main t_env) in ()

  | Cst_syntax.System _ ->
      (* handle System *)
      raise (TypeException "A Rabbit program with multiple `system` declarations is ill-typed ")


let typecheck_sys (cst_decls : Cst_syntax.decl list) 
  (sys : Cst_syntax.decl) (secrecy_lattice : To_cst.cst_access_policy)
  (integrity_lattice : To_cst.cst_access_policy) : unit = match sys.Cst_syntax.desc with 
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


    let initial_tenv = Maps.IdentMap.empty in 
    
    (* typecheck each decl of filtered_decls *)
    List.iter (fun decl -> 
        typecheck_decl secrecy_lattice integrity_lattice decl initial_tenv) filtered_decls;
  | _ -> assert true