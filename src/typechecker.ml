open Sets


exception TypeException of string


type core_type = 
  | TChan of core_type list
  | TSimple of Name.ident * core_type list
  | TProd of core_type * core_type


type secrecy_lvl = 
  | Public 
  | SNode of proc_set 

type integrity_lvl = 
  | Untrusted
  | INode of proc_set

type core_security_type = core_type * (secrecy_lvl * integrity_lvl)


type function_param_type = 
  | CParamCore of core_security_type
  | CParamPoly of Name.ident


let rec typeof_cmd cmd env = match cmd.desc with 
  | _ -> failwith "TODO"


let rec typecheck_decl decl env = match decl.desc with 
  (* we should only need to typecheck the Process decl *)
  | Typed.Process{ id; param; args; typ; files; vars; funcs; main } -> 
    failwith "TODO"
  | _ -> failwith "TODO"


let rec typecheck_sys (decls : Cst_syntax.decl list) 
  (sys : Cst_syntax.decl) = match sys with 
  | Cst_syntax.System(procs) ->
    failwith "TODO"
  | _ -> assert false