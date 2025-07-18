

exception TypeException of string



let rec typeof_expr (secrecy_lattice : To_cst.cst_access_policy)
  (integrity_lattice : To_cst.cst_access_policy) (expr : Cst_syntax.expr) : Cst_env.core_security_type = 
  let typeof_expr_rec = (typeof_expr secrecy_lattice integrity_lattice) in 
  match expr.desc with
    | Ident { id; desc; param } ->
        (* Handle identifier *)
        (* if (Ident.string_part id = "msg") then 
        print_endline (Cst_syntax.show_expr expr); *)
        (Dummy, (S_Ignore, I_Ignore))

    | Boolean b ->
        (* Handle boolean *)
        (Dummy, (S_Ignore, I_Ignore))

    | String s ->
        (* Handle string *)
        (Dummy, (S_Ignore, I_Ignore))

    | Integer i ->
        (* Handle integer *)
        (Dummy, (S_Ignore, I_Ignore))

    | Float f ->
        (* Handle float *)
        (Dummy, (S_Ignore, I_Ignore))

    | Apply (id, args) ->
        let types_of_args = List.map typeof_expr_rec args in 
        (Dummy, (S_Ignore, I_Ignore))

    | Tuple exprs ->
        (* Handle tuple *)
        (Dummy, (S_Ignore, I_Ignore))

    | Unit ->
        (* Handle unit *)
        (Dummy, (S_Ignore, I_Ignore))


let rec typeof_cmd  (secrecy_lattice : To_cst.cst_access_policy)
  (integrity_lattice : To_cst.cst_access_policy) (cmd : Cst_syntax.cmd) : Cst_env.core_security_type = 
  let typeof_expr_rec = (typeof_expr secrecy_lattice integrity_lattice) in 
  let typeof_cmd_rec = (typeof_cmd secrecy_lattice integrity_lattice) in 
  match cmd.Cst_syntax.desc with 
    | Skip ->  (TUnit, (Public, Untrusted))
    | Sequence (c1, c2) -> 
        let _ = (typeof_cmd secrecy_lattice integrity_lattice c1) in 
        (typeof_cmd secrecy_lattice integrity_lattice c2)
    | Put facts -> (Dummy, (S_Ignore, I_Ignore))
    | Let (id, e, c) -> 
        (* if the variable we are assigning to is `msg` *)
        let _ = (typeof_expr secrecy_lattice integrity_lattice e) in
        (typeof_cmd secrecy_lattice integrity_lattice c)
    | Assign (Some id, e) -> 
        let _ = (typeof_expr secrecy_lattice integrity_lattice e) in 
        (TUnit, (Public, Untrusted))
    | Assign (None, e) -> 
        print_endline (Cst_syntax.show_expr e);
        let _ = (typeof_expr secrecy_lattice integrity_lattice e) in 
        (TUnit, (Public, Untrusted))
    | Case cases ->  (Dummy, (S_Ignore, I_Ignore))
    | While (guards, untils) -> (Dummy, (S_Ignore, I_Ignore))
    | Event facts ->  (Dummy, (S_Ignore, I_Ignore))
    | Return e ->  (Dummy, (S_Ignore, I_Ignore))
    | New (id, sec_ty_opt, constr_opt, body) ->  (Dummy, (S_Ignore, I_Ignore))
    | Get (ids, e, name, body) -> (Dummy, (S_Ignore, I_Ignore))
    | Del (e, name) ->  (Dummy, (S_Ignore, I_Ignore))


let typecheck_decl (secrecy_lattice : To_cst.cst_access_policy)
  (integrity_lattice : To_cst.cst_access_policy) (decl : Cst_syntax.decl) : unit = 
  let typeof_expr_rec = (typeof_expr secrecy_lattice integrity_lattice) in 
  let typeof_cmd_rec = (typeof_cmd secrecy_lattice integrity_lattice) in 
  match decl.Cst_syntax.desc with 
  | Cst_syntax.Syscall _ ->
      (* failwith "TODO: not sure if Cst_syntax.Attack needs to be typechecked"; *)
      ()

  | Cst_syntax.Attack _ ->
      (* failwith "TODO: not sure if Cst_syntax.Attack needs to be typechecked"; *)
      ()

  | Cst_syntax.Process { id; main; _ } ->
      (print_endline (Format.sprintf "Running typeof_cmd on process name %s" (Ident.string_part id)));
      (* we should only need to typecheck the Process decl *)
      let _ = (typeof_cmd secrecy_lattice integrity_lattice main) in ()

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
    
    (* typecheck each decl of filtered_decls *)
    List.iter (typecheck_decl
    secrecy_lattice integrity_lattice) filtered_decls;
  | _ -> assert true