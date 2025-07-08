open Sets


exception TypeException of string


type core_type = 
  | TChan of core_type list
  | TSimple of Name.ident * core_type list
  | TProd of core_type * core_type


type secrecy_lvl = 
  | Public 
  | SNode of proc_ty_set 

type integrity_lvl = 
  | Untrusted
  | INode of proc_ty_set

type core_security_type = core_type * (secrecy_lvl * integrity_lvl)


type function_param_type = 
  | CParamCore of core_security_type
  | CParamPoly of Name.ident


let typeof_cmd cmd = match cmd.Cst_syntax.desc with 
  | _ -> failwith "TODO"


let rec typecheck_decl decl = match decl.Cst_syntax.desc with 
  (* we should only need to typecheck the Process decl *)
  | Cst_syntax.Process{ id; param; args; typ; files; vars; funcs; main } -> 
    failwith "TODO"
  | _ -> failwith "TODO"


let rec typecheck_sys (decls : Cst_syntax.decl list) 
  (sys : Cst_syntax.decl) = match sys.Cst_syntax.desc with 
  | Cst_syntax.System(procs) ->
    failwith "TODO"
  | _ -> assert false