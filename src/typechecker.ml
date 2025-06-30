






(* let rec typeof_expr e env = match e with 
  | Typed.
  | _ failwith "TODO" *)


let rec typecheck_decl decl env = match decl.desc with 
  | Typed.Process{ id; param; args; typ; files; vars; funcs; main } -> 
    failwith "TODO"
  | _ -> failwith "TODO"