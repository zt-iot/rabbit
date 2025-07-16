

exception TypeException of string



let typeof_expr (_ : To_cst.cst_access_policy)
  (_ : To_cst.cst_access_policy) (expr : Cst_syntax.expr) : Cst_env.core_security_type = match expr.Cst_syntax.desc with 
  | _ -> failwith "TODO"


let typeof_cmd  (_ : To_cst.cst_access_policy)
  (_ : To_cst.cst_access_policy) (cmd : Cst_syntax.cmd) : Cst_env.core_security_type = match cmd.Cst_syntax.desc with 
  | _ -> failwith "TODO"


let typecheck_decl (secrecy_lattice : To_cst.cst_access_policy)
  (integrity_lattice : To_cst.cst_access_policy) (decl : Cst_syntax.decl) : unit = match decl.Cst_syntax.desc with 
  | Cst_syntax.Syscall _ ->
      (* failwith "TODO: not sure if Cst_syntax.Attack needs to be typechecked"; *)
      ()

  | Cst_syntax.Attack _ ->
      (* failwith "TODO: not sure if Cst_syntax.Attack needs to be typechecked"; *)
      ()

  | Cst_syntax.Process { id; main; _ } ->
      (* we should only need to typecheck the Process decl *)
      if (Ident.string_part id = "alice") then
        let _ = (print_endline (Cst_syntax.show_decl decl));
      in 
      let _ = (typeof_cmd secrecy_lattice integrity_lattice main) in ()

  | Cst_syntax.System _ ->
      (* handle System *)
      raise (TypeException "A Rabbit program with multiple `system` declarations is ill-typed ")


let typecheck_sys (cst_decls : Cst_syntax.decl list) 
  (sys : Cst_syntax.decl) (secrecy_lattice : To_cst.cst_access_policy)
  (integrity_lattice : To_cst.cst_access_policy) : unit = match sys.Cst_syntax.desc with 
  | Cst_syntax.System(proc_strs) ->

    (* for all `proc_name` \in `procs`, we need to check that `proc_name` is well-typed *)

    (* get only the declarations for which their name appears in `procs` *)
    let filtered_decls =
      List.filter (fun decl -> match decl.Cst_syntax.desc with
        | Cst_syntax.Process { id; _ } -> List.mem (Ident.string_part id) proc_strs
        | _ -> false  (* keep all non-process declarations *)
      ) cst_decls in 
    
    (* typecheck each decl of filtered_decls *)
    List.iter (typecheck_decl
    secrecy_lattice integrity_lattice) filtered_decls;
  | _ -> assert true