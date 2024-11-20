(** Conversion from concrete syntax to abstract syntax.
    Here we also load all required files, which may not be
    optimal but is systematic. *)

(** Conversion errors *)
type desugar_error =
  | UnknownIdentifier of string
  | UnknownIdentifier_ch of string
  | UnknownIdentifier_path of string
  | UnknownIdentifier_process of string
  | UnknownIdentifier2 of string
  | UnknownFunction of string
  | AlreadyDefined of string 
  | ForbiddenIdentifier of string
  | ArgNumMismatch of string * int * int
  | NegativeArity of int
  | ForbiddenFresh 
  | UnintendedError 
  | WrongInputType

exception Error of desugar_error Location.located

(** [error ~loc err] raises the given runtime error. *)
let error ~loc err = Stdlib.raise (Error (Location.locate ~loc err))

(** Print error description. *)
let print_error err ppf =
  match err with
  | UnknownIdentifier x -> Format.fprintf ppf "unknown identifier %s" x
  | UnknownIdentifier2 x -> Format.fprintf ppf "unknown identifier %s" x
  | UnknownFunction x -> Format.fprintf ppf "unknown function %s" x
  | AlreadyDefined x -> Format.fprintf ppf "identifier already defined %s" x
  | ForbiddenIdentifier x -> Format.fprintf ppf "forbidden identifier %s" x
  | ArgNumMismatch (x, i, j) -> Format.fprintf ppf "%s arguments provided while %s requires %s" (string_of_int i) x (string_of_int j)
  | UnintendedError -> Format.fprintf ppf "unintended behavior. contact the developer"
  | WrongInputType -> Format.fprintf ppf "wrong input type"
  | ForbiddenFresh -> Format.fprintf ppf "fresh is reserved identifier"
  | NegativeArity k -> Format.fprintf ppf "negative arity is given: %s" (string_of_int k)
  | _ -> Format.fprintf ppf "" 
  


(* fr is used only for parsing and processing external instructions *)
let rec process_expr ctx lctx {Location.data=c; Location.loc=loc} = 
   let process_expr' ctx lctx = function
   | Input.Var id -> 
      if Context.ctx_check_const ctx id then Syntax.Const id
      else if Context.ctx_check_ext_const ctx id then Syntax.ExtConst id
      else if Context.lctx_check_chan lctx id then Syntax.Channel (id, "")
      else if Context.lctx_check_path lctx id then Syntax.Path id
      else if Context.lctx_check_process lctx id then Syntax.Process id
      else if Context.lctx_check_var lctx id then Syntax.Variable (Syntax.index_var id (Context.lctx_get_var_index ~loc lctx id))
      else error ~loc (UnknownIdentifier id) 
   | Input.Boolean b -> Syntax.Boolean b
   | Input.String s -> Syntax.String s 
   | Input.Integer z -> Syntax.Integer z
   | Input.Float f -> Syntax.Float f
   | Input.Apply(o, el) ->
      if Context.ctx_check_ext_syscall ctx o then error ~loc (ForbiddenIdentifier o) else
      if Context.ctx_check_ext_func_and_arity ctx (o, List.length el) then Syntax.Apply (o, (List.map (fun a -> process_expr ctx lctx a) el)) else
      error ~loc (UnknownIdentifier o)
   | Input.Tuple el -> Syntax.Tuple (List.map (fun a -> process_expr ctx lctx a) el)
  in
  let c = process_expr' ctx lctx c in
  Location.locate ~loc c

(* let infer_ty ctx lctx {Location.data=c; Location.loc=loc} = 
   match c with
   | Syntax.Channel -> TyPreChan
   | Syntax.Channel _ -> TyChan
   | _ -> TyVal *)

let rec process_stmt ctx lctx {Location.data=c; Location.loc=loc} = 
   let process_stmt' ctx lctx = function
   | Input.OpStmt a -> 
      let (ctx', lctx', a') = process_atomic_stmt ctx lctx a in (ctx', lctx', Syntax.OpStmt a')
   | Input.EventStmt (a, el) -> 
      let (ctx, lctx', a') = process_atomic_stmt ctx lctx a in
      let (ctx, el') = List.fold_left (fun (ctx, el') e -> 
            let loc' = e.Location.loc in 
            match  e.Location.data with
            | Input.Event (eid, idl) ->
               (* evend id can be anything as it is syntactically distinguished *)
               let ctx = 
               begin
               if Context.ctx_check_event ctx eid then 
                  if List.length idl = Context.ctx_get_event_arity ctx eid ~loc then ctx
                  else error ~loc (ArgNumMismatch (eid, (List.length idl), (Context.ctx_get_event_arity ctx eid ~loc))) (* arity doesn't match *)
               else Context.ctx_add_event ctx (eid, List.length idl)
               end in
               let idl = List.map (fun e -> process_expr ctx lctx' e) idl in 
               (ctx, {Location.data=Syntax.Event (eid, idl) ; Location.loc=loc'}:: el')) (ctx, []) el in 
               (ctx, lctx', Syntax.EventStmt(a', el'))
  in
  let (ctx, lctx, c) = process_stmt' ctx lctx c in
  (ctx, lctx, Location.locate ~loc c)
  
  and process_atomic_stmt ctx lctx {Location.data=c; Location.loc=loc} = 
      let process_atomic_stmt' ctx lctx = function
      | Input.Skip -> (ctx, lctx, Syntax.Skip)
      | Input.LetUnderscore e ->
         let (lctx'', vid') = (lctx, Syntax.indexed_underscore) in 
         begin match e.Location.data with 
         |  Input.Apply(o, args) -> 
            if Context.lctx_check_func lctx o then
            begin
               (* call *)
            if Context.lctx_get_func_arity lctx o = List.length args then
               let args' = List.map (fun arg -> process_expr ctx lctx arg) args in
               (ctx, lctx'', Syntax.Call (vid', o, args'))
            else
             (* not enough argumentes *)
               error ~loc (ArgNumMismatch (o, (List.length args), (Context.lctx_get_func_arity lctx o)))
            end else
            if Context.ctx_check_ext_syscall ctx o then
            begin
               let args_ty = Context.ctx_get_ext_syscall_arity ~loc:e.Location.loc ctx o in
               if List.length args = List.length args_ty then
                  (ctx, lctx'', Syntax.Syscall(vid', o, 
                     List.map2 (fun arg arg_ty -> 
                     let e = process_expr ctx lctx arg in 
                     (match e.Location.data, arg_ty with
                     | Syntax.Channel (s, _), Input.TyChannel -> Location.locate ~loc:e.Location.loc (Syntax.Channel (s, o))
                     | _, Input.TyChannel -> error ~loc (WrongInputType)
                     | _, _ -> e), arg_ty) args args_ty))
               else error ~loc (ArgNumMismatch (o, List.length args, List.length args_ty))
            end
            else (ctx, lctx'', Syntax.Let(vid', process_expr ctx lctx e))
         | _ -> (ctx, lctx'', Syntax.Let(vid', process_expr ctx lctx e))
         end

      | Input.Let (vid, e, isnewvar) ->
         let (lctx'', vid') =
           if Context.lctx_check_var lctx vid then
             if isnewvar then error ~loc (AlreadyDefined vid) else  (lctx, Syntax.index_var vid (Context.lctx_get_var_index ~loc lctx vid))
           else
             if isnewvar then let lctx' = Context.lctx_add_new_var ~loc lctx vid in (lctx', Syntax.index_var vid (Context.lctx_get_var_index  ~loc lctx' vid))
             else error ~loc (UnknownIdentifier vid)
         in
         begin match e.Location.data with 
         |  Input.Apply(o, args) -> 
            if Context.lctx_check_func lctx o then
            begin
               (* call *)
            if Context.lctx_get_func_arity lctx o = List.length args then
               let args' = List.map (fun arg -> process_expr ctx lctx arg) args in
               (ctx, lctx'', Syntax.Call (vid', o, args'))
            else
             (* not enough argumentes *)
               error ~loc (ArgNumMismatch (o, (List.length args), (Context.lctx_get_func_arity lctx o)))
            end else
            (* if a function is applied to a local variable. 
               this should only be allowed in system call processing. *)
            if Context.lctx_check_var lctx o then 
            begin
               (* call *)
               let args' = List.map (fun arg -> process_expr ctx lctx arg) args in
                 (ctx, lctx'', Syntax.Call (vid', o, args'))
            end else

            if Context.ctx_check_ext_syscall ctx o then
            begin
               let args_ty = Context.ctx_get_ext_syscall_arity ~loc:e.Location.loc ctx o in
               if List.length args = List.length args_ty then
                  (ctx, lctx'', Syntax.Syscall(vid', o, 
                     List.map2 (fun arg arg_ty -> 
                     let e = process_expr ctx lctx arg in 
                     
                     (match e.Location.data, arg_ty with
                     | Syntax.Channel (s, _), Input.TyChannel -> Location.locate ~loc:e.Location.loc (Syntax.Channel (s, o))
                     | _, Input.TyChannel -> error ~loc (WrongInputType)
                     | _, _ -> e)
                     , arg_ty
                  ) args args_ty))
               else error ~loc (ArgNumMismatch (o, List.length args, List.length args_ty))
            end
            else (ctx, lctx'', Syntax.Let(vid', process_expr ctx lctx e))
         | _ -> (ctx, lctx'', Syntax.Let(vid', process_expr ctx lctx e))
         end

      | Input.If (e1, e2, c1, c2) ->
         let e1' = process_expr ctx lctx e1 in 
         let e2' = process_expr ctx lctx e2 in 
         let lctx' = Context.lctx_add_frame lctx in 
         let (ctx1, _, c1') = process_stmts ctx lctx' c1 in 
         let (ctx2, _, c2') = process_stmts ctx1 lctx' c2 in 
         (ctx2, lctx, Syntax.If (e1', e2', c1', c2'))

      | Input.For (vid, i, j, c) ->
         let (lctx', vid') = 
            let lctx'' = Context.lctx_add_frame lctx in 
            let lctx2 = if Context.lctx_check_var lctx'' vid then lctx'' else Context.lctx_add_new_var ~loc lctx'' vid in 
            (lctx2, Syntax.index_var vid (Context.lctx_get_var_index ~loc lctx2 vid)) in
            let (ctx', _, c') = process_stmts ctx lctx' c in 
            (ctx', lctx, Syntax.For(vid', i, j, c'))
     in
     let (ctx, lctx, c) = process_atomic_stmt' ctx lctx c in
     (ctx, lctx, Location.locate ~loc c)
     
   and process_stmts ctx lctx cs =
   match cs with
   | c :: cs' -> 
      let (ctx', lctx', c') = process_stmt ctx lctx c in 
      let (ctx'', lctx'', c'') = process_stmts ctx' lctx' cs' in 
      (ctx'', lctx'', c' :: c'')
   | [] -> 
      (ctx, lctx, [])

let process_init = (Context.ctx_init, Context.pol_init, Context.def_init, [], ([],[]))


let rec process_decl ctx pol def sys ps {Location.data=c; Location.loc=loc} =
   let process_decl' ctx pol def sys ps = function
   | Input.DeclExtFun (f, k) -> 
      let ctx' =
         if Context.check_used ctx f then error ~loc (AlreadyDefined f) else 
         if k = 0 then Context.ctx_add_ext_const ctx f else if k > 0 then Context.ctx_add_ext_func ctx (f, k) else error ~loc (NegativeArity k) 
      in (ctx', pol, def, sys, fst ps)

   | Input.DeclExtEq (e1, e2) -> 
      let rec collect_vars e lctx =
         try let e = process_expr ctx lctx e in (e, lctx)
         with
         | Error {Location.data=err; Location.loc=locc} ->
            begin match err with
            | UnknownIdentifier id -> collect_vars e (Context.lctx_add_new_var ~loc lctx id)
            | _ -> error ~loc:locc err
            end
      in 
      (* is this really correct??? check with x = y next time!! *)
      let (e1', lctx) = collect_vars e1 Context.lctx_init in 
      let (e2', lctx) = collect_vars e2 lctx in
      (ctx, pol, Context.def_add_ext_eq def (List.hd lctx.Context.lctx_var, e1', e2'), sys, fst ps)


   | Input.DeclExtSyscall(f, typed_args, substs, rules, ret) ->      
      if Context.check_used ctx f then error ~loc (AlreadyDefined f) else 
         (* parse arguments *)
         let lctx = List.fold_left (fun lctx' ta -> 
            match ta with
            | (Input.TyValue, v) -> Context.lctx_add_new_var ~loc lctx' v
            | (Input.TyChannel, v) -> Context.lctx_add_new_chan ~loc lctx' v
            | (Input.TyPath, v) -> Context.lctx_add_new_path ~loc lctx' v
            | (Input.TyProcess, v) -> error ~loc (UnknownIdentifier2 v)) (Context.lctx_init) typed_args in

         let lctx = Context.lctx_add_frame lctx in 

         let lctx, substs = List.fold_left (fun (lctx, substs) (y, e) ->
            if not (List.exists (fun (_, s) -> s = y) typed_args) then 
            error ~loc (UnknownIdentifier y) else
            let rec f e lctx = 
               try 
                  lctx, process_expr ctx lctx e  
               with 
               | Error {Location.data=err; Location.loc=locc} ->
                  begin match err with
                  | UnknownIdentifier id -> 
                     f e (Context.lctx_add_new_var ~loc:locc lctx id)
                  | _ -> error ~loc:locc err
               end
            in 
            let lctx, e = f e lctx in 
            lctx, substs @ [(y, e)]) (lctx, []) substs in 

         let process_fact f ctx lctx =
            match f.Location.data with
            | Input.Fact (id, el) ->
               (Context.ctx_add_or_check_fact ~loc ctx (id, List.length el), Location.locate ~loc:f.Location.loc (Syntax.Fact(id, List.map (process_expr ctx lctx) el)))
            | Input.GlobalFact (id, el) ->
               (Context.ctx_add_or_check_fact ~loc ctx (id, List.length el), Location.locate ~loc:f.Location.loc (Syntax.GlobalFact(id, List.map (process_expr ctx lctx) el)))
            | Input.ChannelFact (l, id, el) ->
               (* check validty of local scope l *)
               if Context.lctx_check_chan lctx l then 
                  (Context.ctx_add_or_check_lfact ~loc ctx (id, List.length el), Location.locate ~loc:f.Location.loc (Syntax.ChannelFact(l, id, List.map (process_expr ctx lctx) el)))
               else error ~loc (UnknownIdentifier_ch l)
            | Input.PathFact (l, id, el) ->
               (* check validty of local scope l *)
               if Context.lctx_check_path lctx l then 
                  (Context.ctx_add_or_check_lfact ~loc ctx (id, List.length el), Location.locate ~loc:f.Location.loc (Syntax.PathFact(l, id, List.map (process_expr ctx lctx) el)))
               else error ~loc (UnknownIdentifier_path l)
            | _ -> error ~loc (UnknownIdentifier2 "")
         in

         let process_rule (pre, post) ctx lctx = 
            let ctx, pre =
               List.fold_left (fun (ctx, facts) f -> let ctx', f' = process_fact f ctx lctx in (ctx', f' :: facts)) (ctx, []) pre in
            let ctx, post =
               List.fold_left (fun (ctx, facts) f -> let ctx', f' = process_fact f ctx lctx in (ctx', f' :: facts)) (ctx, []) post in
               (ctx, (pre, post)) in

         let rec process_crule {Location.data=rs; Location.loc=loc} ctx lctx = 
            match rs with
            | Input.CRule (pre, post) -> 
               let ctx, (pre, post) = process_rule (pre, post) ctx lctx in
               (ctx, Location.locate ~loc:loc (Syntax.CRule (pre, post)))

            | Input.CRuleStmt (pre, stmts, post) -> 
               let ctx, pre =
                  List.fold_left (fun (ctx, facts) f -> let ctx', f' = process_fact f ctx lctx in (ctx', f' :: facts)) (ctx, []) pre in
               begin try 
               let (ctx, lctx, stmts) = 
                  process_stmts ctx lctx stmts in
               let ctx, post =
                  List.fold_left (fun (ctx, facts) f -> let ctx', f' = process_fact f ctx lctx in (ctx', f' :: facts)) (ctx, []) post 
               in 
               (ctx, Location.locate ~loc:loc (Syntax.CRuleStmt (pre, stmts, post)))
               with 
               | Error {Location.data=err; Location.loc=locc} ->
                  match err with
                  | UnknownIdentifier id -> error ~loc (UnknownIdentifier2 id)
                  | UnknownIdentifier_ch id -> error ~loc (UnknownIdentifier2 id)
                  | UnknownIdentifier_path id -> error ~loc (UnknownIdentifier2 id)
               | _ -> error ~loc:locc err
               end 

            | Input.CRulePar (r1, r2) -> 
               let (ctx, r1) = process_crule r1 ctx lctx in 
               let (ctx, r2) = process_crule r2 ctx lctx in 
               (ctx, Location.locate ~loc:loc (Syntax.CRulePar (r1, r2)))

            | Input.CRuleSeq (r1, r2) -> 
               let (ctx, r1) = process_crule r1 ctx lctx in 
               let (ctx, r2) = process_crule r2 ctx lctx in 
               (ctx, Location.locate ~loc:loc (Syntax.CRuleSeq (r1, r2)))

            | Input.CRuleRep r ->
               match r.Location.data with 
               | Input.CRuleRep r -> 
                  let ctx, r = process_crule r ctx lctx in 
                     ctx, Location.locate ~loc:loc (Syntax.CRuleRep r)
               | _ -> 
                  let ctx, r = process_crule r ctx lctx in 
                  ctx, Location.locate ~loc:loc (Syntax.CRuleRep r)
         in  
         let rec process rs lctx =         
            try 
               let (ctx, rs) = process_crule rs ctx lctx in 
               let ret = (match ret with Some r -> Some (process_expr ctx lctx r) | None -> None) in 
               (ctx, rs, ret, lctx)
            with
            | Error {Location.data=err; Location.loc=locc} ->
               begin match err with
               | UnknownIdentifier id -> process rs (Context.lctx_add_new_var ~loc lctx id)
               | UnknownIdentifier_ch id -> process rs (Context.lctx_add_new_chan ~loc (Context.lctx_remove_var lctx id) id)
               | UnknownIdentifier_path id -> process rs (Context.lctx_add_new_path ~loc (Context.lctx_remove_var lctx id) id)
               | _ -> error ~loc:locc err
               end
         in

         let (ctx, rs, ret, lctx) = process rules lctx in
         let metavar = List.hd lctx.Context.lctx_var in 
         (* let args = List.hd (Context.lctx_pop_frame ~loc lctx).Context.lctx_var in  *)
         let ch_args = lctx.Context.lctx_chan in 
         let path_args = lctx.Context.lctx_path in 

         (Context.ctx_add_ext_syscall ctx (f, List.map fst typed_args), pol, Context.def_add_ext_syscall def (f, (typed_args), (ch_args, path_args), metavar, substs, rs, ret), sys, fst ps)


   | Input.DeclExtAttack(f, typed_arg, rule) ->      
      if Context.check_used ctx f then error ~loc (AlreadyDefined f) else 
         (* parse arguments *)
         let lctx = List.fold_left (fun lctx' ta -> 
            match ta with
            | (Input.TyValue, v) -> error ~loc (UnknownIdentifier2 v)
            | (Input.TyChannel, v) -> Context.lctx_add_new_chan ~loc lctx' v
            | (Input.TyPath, v) -> Context.lctx_add_new_path ~loc lctx' v
            | (Input.TyProcess, v) -> Context.lctx_add_new_process ~loc lctx' v) (Context.lctx_init) [typed_arg] in

         let process_fact f ctx lctx =
            match f.Location.data with
            | Input.Fact (id, el) ->
               (Context.ctx_add_or_check_fact ~loc ctx (id, List.length el), Location.locate ~loc:f.Location.loc (Syntax.Fact(id, List.map (process_expr ctx lctx) el)))
            | Input.GlobalFact (id, el) ->
               (Context.ctx_add_or_check_fact ~loc ctx (id, List.length el), Location.locate ~loc:f.Location.loc (Syntax.GlobalFact(id, List.map (process_expr ctx lctx) el)))
            | Input.ChannelFact (l, id, el) ->
               (* check validty of local scope l *)
               if Context.lctx_check_chan lctx l then 
                  (Context.ctx_add_or_check_lfact ~loc ctx (id, List.length el), Location.locate ~loc:f.Location.loc (Syntax.ChannelFact(l, id, List.map (process_expr ctx lctx) el)))
               else error ~loc (UnknownIdentifier_ch l)
            | Input.PathFact (l, id, el) ->
               (* check validty of local scope l *)
               if Context.lctx_check_path lctx l then 
                  (Context.ctx_add_or_check_lfact ~loc ctx (id, List.length el), Location.locate ~loc:f.Location.loc (Syntax.PathFact(l, id, List.map (process_expr ctx lctx) el)))
               else error ~loc (UnknownIdentifier_path l)
            | Input.ProcessFact (l, id, el) ->
               (* check validty of local scope l *)
               if Context.lctx_check_process lctx l then 
                  (Context.ctx_add_or_check_fact ~loc ctx (id, List.length el + 1), Location.locate ~loc:f.Location.loc (Syntax.ProcessFact(l, id, List.map (process_expr ctx lctx) el)))
               else error ~loc (UnknownIdentifier_process l)

         in

         let rec process_rules rs ret lctx = 
            try 
               begin
                  let ctx, rs = 
                     List.fold_left (fun (ctx, rs) (pre, post) -> 
                     let ctx, pre =
                        List.fold_left (fun (ctx, facts) f -> let ctx', f' = process_fact f ctx lctx in (ctx', f' :: facts)) (ctx, []) pre in
                     let ctx, post =
                        List.fold_left (fun (ctx, facts) f -> let ctx', f' = process_fact f ctx lctx in (ctx', f' :: facts)) (ctx, []) post in
                     (ctx, (pre, post) :: rs)) (ctx, []) rs in
                  let ret = (match ret with Some r -> Some (process_expr ctx lctx r) | None -> None) in 
                  (ctx, rs, ret, lctx)
                end 
            with
            | Error {Location.data=err; Location.loc=locc} ->
               begin match err with
               | UnknownIdentifier id -> process_rules rs ret (Context.lctx_add_new_var ~loc lctx id)
               | UnknownIdentifier_ch id -> process_rules rs ret (Context.lctx_add_new_chan ~loc (Context.lctx_remove_var lctx id) id)
               | UnknownIdentifier_path id -> process_rules rs ret (Context.lctx_add_new_path ~loc (Context.lctx_remove_var lctx id) id)
               | UnknownIdentifier_process id -> process_rules rs ret (Context.lctx_add_new_process ~loc (Context.lctx_remove_var lctx id) id)
               | _ -> error ~loc:locc err
               end
         in

         let (ctx, rs, ret, lctx) = process_rules [rule] None (Context.lctx_add_frame lctx) in
         let rs = match rs with | [rs] -> rs | _ -> error ~loc UnintendedError in
         (* let metavar = List.hd lctx.Context.lctx_var in  *)
         (* let args = List.hd (Context.lctx_pop_frame ~loc lctx).Context.lctx_var in  *)
         let ch_args = lctx.Context.lctx_chan in 
         let path_args = lctx.Context.lctx_path in 
         let process_args = lctx.Context.lctx_process in
         (Context.ctx_add_ext_attack ctx (f, fst typed_arg), pol, 
            Context.def_add_ext_attack def (f, (ch_args, path_args, process_args), rs), sys, fst ps)


   | Input.DeclType (id, c) -> 
      if Context.check_used ctx id then error ~loc (AlreadyDefined id) else (Context.ctx_add_ty ctx (id, c), pol, def, sys, fst ps)
   
   | Input.DeclAccess(s, t, al) -> 
      let tys = Context.ctx_get_ty ~loc ctx s in
      let tyt = List.map (Context.ctx_get_ty ~loc ctx) t in 
      let f pol' a =
         begin
         match tys, tyt with
         | Input.CProc, [Input.CChan] -> 
            if Context.ctx_check_ext_syscall ctx a then Context.pol_add_access pol' (s, t, a)
            else error ~loc (UnknownIdentifier a)
         | Input.CProc, [Input.CFsys] -> 
            if Context.ctx_check_ext_syscall ctx a then Context.pol_add_access pol' (s, t, a)
            else error ~loc (UnknownIdentifier a)
         | Input.CProc, [] -> 
            if Context.ctx_check_ext_syscall ctx a then Context.pol_add_access pol' (s, t, a)
            else error ~loc (UnknownIdentifier a)            
         | _, _ -> error ~loc (WrongInputType)
         end
      in (ctx, List.fold_left f pol al, def, sys, fst ps)

   | Input.DeclAttack (tl, al) -> 
      let f t a =
         if Context.ctx_check_ty ctx t then
         if Context.ctx_check_ext_attack ctx a then
         match Context.ctx_get_ty ~loc ctx t, Context.ctx_get_ext_attack_arity ~loc ctx a with
         | Input.CProc, Input.TyProcess 
         | Input.CChan, Input.TyChannel 
         | Input.CFsys, Input.TyPath ->
            (t, a)
         | _, _ -> error ~loc (WrongInputType)
         else error ~loc (UnknownIdentifier a)
         else error ~loc (UnknownIdentifier t) in
      let p = List.fold_left (fun p t -> 
         List.fold_left (fun p a -> Context.pol_add_attack p (f t a)) p al) pol tl in 
      (ctx, p, def, sys, fst ps)

  | Input.DeclInit (id, e) -> 
      if Context.check_used ctx id then error ~loc (AlreadyDefined id) else 
      let e' = match e with | Some e -> Some (process_expr ctx Context.lctx_init e) | _ -> None in 
      (Context.ctx_add_const ctx id, pol, Context.def_add_const def (id, e'), sys, fst ps)

  | Input.DeclFsys (id, fl) ->
      if Context.check_used ctx id then error ~loc (AlreadyDefined id) else 
      let fl' = List.map (fun (a, e, b) -> 
         match Context.ctx_get_ty ~loc ctx b with
         | Input.CFsys ->
            (a, process_expr ctx Context.lctx_init e, b )
         | _ -> error ~loc (WrongInputType)
         ) fl in 
      let (ctx', def') = List.fold_left 
         (fun (ctx', def') (a, e, b) -> (Context.ctx_add_fsys ctx' (id, a, b), Context.def_add_fsys def' (id, a, e))) (ctx, def) fl' in 
         (ctx', pol, def', sys, fst ps)

  | Input.DeclChan (id, c) ->
      if Context.check_used ctx id then error ~loc (AlreadyDefined id) else 
      (Context.ctx_add_ch ctx (id, c), pol, def, sys, fst ps)

  | Input.DeclProc (pid, cargs, ty, cl, fs, m) ->
      begin match Context.ctx_get_ty ~loc ctx ty 
      with 
      | Input.CProc -> 
         if Context.check_used ctx pid then error ~loc (AlreadyDefined pid) else 
         let lctx = List.fold_left (fun lctx' cid -> Context.lctx_add_new_chan ~loc lctx' cid) Context.lctx_init cargs in
         let (lctx, ldef) = List.fold_left (fun (lctx', ldef') (vid, e) -> 
            (Context.lctx_add_new_var ~loc lctx' vid, Context.ldef_add_new_var ldef' (vid, process_expr ctx lctx' e))) (lctx, Context.ldef_init) cl in
         let (ctx, lctx, ldef) = List.fold_left (fun (ctx'', lctx'', ldef'') (fid, args, cs, ret) -> 
            if Context.lctx_check_func lctx'' fid then error ~loc (AlreadyDefined fid) else 
            let lctx = List.fold_left (fun lctx' vid -> Context.lctx_add_new_var ~loc lctx' vid) (Context.lctx_add_frame lctx'') args in
            let (ctx', lctx', cs')  = process_stmts ctx'' lctx cs in 
            (ctx', Context.lctx_add_new_func ~loc lctx'' (fid, List.length args), 
                  Context.ldef_add_new_func ldef'' (fid, args, cs', Syntax.index_var ret (Context.lctx_get_var_index ~loc lctx' ret)))) (ctx, lctx, ldef) fs in
            let (ctx, _, m') = process_stmts ctx (Context.lctx_add_frame lctx) m in 
            (Context.ctx_add_proctmpl ctx (Context.mk_ctx_proctmpl (pid, lctx.Context.lctx_chan, ty, List.hd lctx.Context.lctx_var, lctx.Context.lctx_func)), pol, 
               Context.def_add_proctmpl def pid ldef m', sys, fst ps)

      | _ -> error ~loc (WrongInputType) 
      end 
   | Input.DeclSys (procs, lemmas) ->
      let processed_procs = List.map (fun proc -> 
         match proc.Location.data with 
         | Input.Proc(pid, chans, fsys) -> 
            if not (Context.ctx_check_proctmpl ctx pid) then error ~loc (UnknownIdentifier pid) else
              (match fsys with | Some fsys -> if not (Context.ctx_check_fsys ctx fsys) then error ~loc (UnknownIdentifier fsys) else () | _ -> ()); 
            let (_, cargs, ptype, _, _) = Context.to_pair_ctx_proctmpl (Context.ctx_get_proctmpl ctx pid) in
            let cargs = List.rev cargs in 
            let (_, vl, fl, m) = Context.to_pair_def_proctmpl (Context.def_get_proctmpl def pid) in
            let fpaths =
              match fsys with
              | Some fsys -> 
                 let fpaths = List.fold_left (fun fpaths (fsys', path, ftype) -> if fsys = fsys' then (path, ftype) :: fpaths else fpaths) [] ctx.Context.ctx_fsys in 
                 let fpaths = List.map (fun (path, ftype) -> 
                                  let (_ , _ , v) = List.find (fun (fsys', path', val') -> fsys' = fsys && path = path') def.Context.def_fsys in 
                                  (path, v, ftype)) fpaths in 
                 let fpaths = List.map (fun (path, v, ftype) -> 
                                  let accs = List.fold_left (fun accs (s, t, a) -> 
                                                 if s = ptype && List.exists (fun s -> s = ftype) t then a :: accs else accs) [] pol.Context.pol_access in
                                  let attks = List.fold_left (fun attks (t, a) -> 
                                                  if t = ftype then a :: attks else attks) [] pol.Context.pol_attack in
                                  (path,v,accs, attks)) fpaths in fpaths
              | None -> []
            in
            (* substitute channels *)
            if (List.length cargs) !=  (List.length chans) then error ~loc (ArgNumMismatch (pid, (List.length chans), (List.length cargs)))
            else
               let (chs, vl, fl, m) = List.fold_left2 
                  (fun (chs, vl, fl, m) ch_f ch_t -> 
                     (* print_string (ch_f ^ " to "^ch_t^"\n") ; *)
                     if Context.ctx_check_ch ctx ch_t then 
                        let (_, chan_ty) = List.find (fun (s, _
                        ) -> s = ch_t) ctx.Context.ctx_ch in  
                        let accesses = List.fold_left (fun acs (f', t', ac) -> if f' = ptype && List.exists (fun s -> s = chan_ty) t' then ac::acs else acs) [] pol.Context.pol_access in 
                        (* replace channel variables and check access policies! *)
                        (
                           (if List.exists (fun (ch_t', _,  _) -> ch_t = ch_t') chs then chs else
                           (ch_t, accesses,
                              List.fold_left (fun attks (s, a) -> if s = ch_t then a :: attks else attks ) [] pol.Context.pol_attack) :: chs),
                              List.map (fun (v, e) -> (v, Substitute.expr_chan_sub e ch_f ch_t accesses)) vl,
                              List.map (fun (fn, args, c, ret) -> (fn, args, List.map (fun c -> Substitute.stmt_chan_sub c ch_f ch_t accesses) c, ret)) fl,
                              List.map (fun c -> Substitute.stmt_chan_sub c ch_f ch_t accesses) m)
                     else error ~loc (UnknownIdentifier ch_t)) ([], vl, fl, m) cargs chans in 
               (pid, 
                  List.fold_left (fun attks (t, a) -> if t = pid then a :: attks else attks) [] pol.Context.pol_attack,
                  chs, fpaths, vl, fl, m, ptype, fsys
                  (* getting type *)

               )) procs in
      (* for now, have plain text for lemmas *)
      let processed_lemmas = List.map (fun l -> 
         let tmp = 
         begin match l.Location.data with 
         | Input.Lemma (l, p) -> 
            let rec collect_vars e lctx =
               try let e = process_expr ctx lctx e in (e, lctx)
               with
               | Error {Location.data=err; Location.loc=locc} ->
                  begin match err with
                  | UnknownIdentifier id -> collect_vars e (Context.lctx_add_new_var ~loc lctx id)
                  | _ -> error ~loc:locc err
                  end
               in 

            match p.Location.data with 
               | Input.PlainString s -> Syntax.PlainLemma (l, s)
               | Input.Reachability evs -> 
                  let (lctx, evl) = 
                     List.fold_left (fun (lctx, evl) ev -> 
                        match ev.Location.data with
                        | Input.Event (ename, els) ->
                           let (lctx, els) = 
                              List.fold_left (fun (lctx, els) e ->
                                                let (e', lctx) = collect_vars e lctx in
                                                   (lctx, els @ [e'])) (lctx, []) els in 
                           (lctx, evl @ [Location.locate ~loc:ev.Location.loc (Syntax.Event (ename, els))])) (Context.lctx_init, []) evs in
                  Syntax.ReachabilityLemma (l, List.hd lctx.Context.lctx_var, evl)

               | Input.Correspondence (e1, e2) ->
                  let (lctx, evl) = 
                     List.fold_left (fun (lctx, evl) ev -> 
                        match ev.Location.data with
                        | Input.Event (ename, els) ->
                           let (lctx, els) = 
                              List.fold_left (fun (lctx, els) e ->
                                                let (e', lctx) = collect_vars e lctx in
                                                   (lctx, els @ [e'])) (lctx, []) els in 
                           (lctx, evl @ [Location.locate ~loc:ev.Location.loc (Syntax.Event (ename, els))])) (Context.lctx_init, []) [e1 ; e2] in
                  match evl with
                  | [e1; e2] ->
                     Syntax.CorrespondenceLemma (l, List.hd lctx.Context.lctx_var, e1, e2)
            end in 
            Location.locate ~loc:l.Location.loc tmp
         ) lemmas in   
      (*  *)
      let (processed_procs) = 
         List.fold_left 
            (fun processed_procs (pid, attks, chans, files, vl, fl, m, ptype, fsys) ->    
               let pnum = 
                  List.length (List.find_all (fun p -> p.Context.proc_name = pid) processed_procs) in         
               ({Context.proc_pid=pnum; 
               Context.proc_type =ptype; 
               Context.proc_filesys= fsys; 
               Context.proc_name=pid; 
               Context.proc_attack=attks; 
               Context.proc_channel=chans; 
               Context.proc_file=files; 
               Context.proc_variable=vl; 
               Context.proc_function=fl; 
               Context.proc_main=m} :: processed_procs)) 
      [] processed_procs in 
      (ctx, pol, def, {
                        Context.sys_ctx = ctx;
                        Context.sys_pol = pol;
                        Context.sys_def = def;
                        Context.sys_proc=processed_procs;
                        Context.sys_lemma = processed_lemmas}::sys, fst ps)
      
      | Input.DeclLoad fn ->
         (*  *)
         let ((a, b), fn') = ps in 
         let new_fn = (Filename.dirname fn') ^ "/" ^ fn in 
         let (ctx, pol, def, sys, parser_state) = load new_fn ctx pol def sys in 
         let parser_state = 
         (* marge  parser_state and ps*)
         (fst parser_state @ a, snd parser_state @ b) in

         (ctx, pol, def, sys, parser_state) 


in process_decl' ctx pol def sys ps c

and load fn ctx pol def sys =
   let decls, parser_state = Lexer.read_file Parser.file fn in 
   let (ctx, pol, def, sys, parser_state) = List.fold_left 
   (fun (ctx, pol, def, sys, parser_state) decl -> process_decl ctx pol def sys (parser_state, fn) decl)  
   (ctx, pol, def, sys, parser_state) decls in (ctx, pol, def, sys, parser_state)

