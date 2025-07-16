

exception TypeException of string



let typeof_expr expr = match expr.Cst_syntax.desc with 
  | _ -> failwith "TODO"


let typeof_cmd cmd = match cmd.Cst_syntax.desc with 
  | _ -> failwith "TODO"


let typecheck_decl decl = match decl.Cst_syntax.desc with 
  (* we should only need to typecheck the Process decl *)
  (* | Cst_syntax.Process{ id; param; args; typ; files; vars; funcs; main } -> 
    failwith "TODO" *)
  | _ -> failwith "TODO"


let typecheck_sys (_ : Cst_syntax.decl list) 
  (sys : Cst_syntax.decl) (_ : To_cst.cst_access_policy)
  (_ : To_cst.cst_access_policy) = match sys.Cst_syntax.desc with 
  | Cst_syntax.System(_) ->
    failwith "TODO"
  | _ -> assert true