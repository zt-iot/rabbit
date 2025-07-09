open Sets

exception TypeException of string



let typeof_expr expr = match expr.Cst_syntax.desc with 
  | _ -> failwith "TODO"


let typeof_cmd cmd = match cmd.Cst_syntax.desc with 
  | _ -> failwith "TODO"


let typecheck_decl decl = match decl.Cst_syntax.desc with 
  (* we should only need to typecheck the Process decl *)
  | Cst_syntax.Process{ id; param; args; typ; files; vars; funcs; main } -> 
    failwith "TODO"
  | _ -> failwith "TODO"


let rec typecheck_sys (decls : Cst_syntax.decl list) 
  (sys : Cst_syntax.decl) = match sys.Cst_syntax.desc with 
  | Cst_syntax.System(procs) ->
    failwith "TODO"
  | _ -> assert false