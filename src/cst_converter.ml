


(* Supplying an environment is not necessary: 
the global environment is 
simply the environment from the Cst_syntax.decl.System declaration
*)
let rec convert (decls : Typed.decl list) : (Cst_syntax.decl list) = match List.rev decls with
  | [] ->
      failwith "Expected a System declaration at the end, but the list is empty"
  | last_decl :: _ ->
      (match last_decl.desc with
      | Typed.System (procs, _) ->
          let proc_names = List.fold_left (fun (proc, acc_names) -> 
            let new_names = begin match proc with 
              | Unbounded(pproc_located) -> 
                [fst pproc_located.data.id]
              | Bounded(_, pproc_located_list) ->
                List.map (fun pproc_located -> fst pproc_located.data.id) pproc_located_list
              end in 
            new_names @@ acc_names
          ) [] procs in ()
      | _ ->
          failwith "The last declaration must be a `system` declaration")