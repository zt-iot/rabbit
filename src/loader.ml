(** Conversion from concrete syntax to abstract syntax.
    Here we also load all required files, which may not be
    optimal but is systematic. *)

(** Conversion errors *)
type desugar_error =
  | UnknownIdentifier of string
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
  | UnknownFunction x -> Format.fprintf ppf "unknown function %s" x
  | AlreadyDefined x -> Format.fprintf ppf "identifier already defined %s" x
  | ForbiddenIdentifier x -> Format.fprintf ppf "forbidden identifier %s" x
  | ArgNumMismatch (x, i, j) -> Format.fprintf ppf "%s arguments provided while %s requires %s" (string_of_int i) x (string_of_int j)
  | UnintendedError -> Format.fprintf ppf "unintended behavior. contact the developer"
  | WrongInputType -> Format.fprintf ppf "wrong input type"
  | ForbiddenFresh -> Format.fprintf ppf "fresh is reserved identifier"
  | NegativeArity k -> Format.fprintf ppf "negative arity is given: %s" (string_of_int k)


(* fr is used only for parsing and processing external instructions *)
let rec process_expr ?(fr=[]) ctx lctx {Location.data=c; Location.loc=loc} = 
   let process_expr' ?(fr=[]) ctx lctx = function
   | Input.Var id -> 
      if Context.ctx_check_const ctx id then Syntax.Const id
      else if Context.ctx_check_ext_const ctx id then Syntax.ExtConst id
      else if Context.lctx_check_chan lctx id then Syntax.Channel (id, [], [])
      else if Context.lctx_check_var lctx id then Syntax.Variable (Syntax.index_var id (Context.lctx_get_var_index ~loc lctx id))
      else error ~loc (UnknownIdentifier id) 
   | Input.Boolean b -> Syntax.Boolean b
   | Input.String s -> Syntax.String s 
   | Input.Integer z -> Syntax.Integer z
   | Input.Float f -> Syntax.Float f
   | Input.Apply(o, el) ->
      if o = "fresh" then 
         if List.exists (fun n -> n = 0) fr then error ~loc ForbiddenFresh else 
            begin match el with
            | [s] -> begin match s.Location.data with | Input.Var s -> Syntax.FrVariable s | _ -> error ~loc UnintendedError  end 
            | _   -> error ~loc UnintendedError  
            end 
      else 
      if Primitives.is_forbidden_operator o then error ~loc (ForbiddenIdentifier o) else
      if Context.ctx_check_ext_func_and_arity ctx (o, List.length el) then Syntax.Apply (o, (List.map (fun a -> process_expr ~fr ctx lctx a) el)) else
      error ~loc (UnknownIdentifier o)
   | Input.Tuple el -> Syntax.Tuple (List.map (fun a -> process_expr ~fr  ctx lctx a) el)
  in
  let c = process_expr' ~fr ctx lctx c in
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
            if Primitives.check_primitive_ins o then
            begin
               let (_, ins, args_ty) = List.find (fun (s, _, _) -> s = o) Primitives.primitive_ins in
               if List.length args = List.length args_ty then
                  (ctx, lctx'', Syntax.Instruction(vid', ins, 
                     List.map2 (fun arg arg_ty -> 
                     let e = process_expr ctx lctx arg in 
                     match e.Location.data, arg_ty with
                     | Syntax.Channel (s, _, _), Etype.EtyCh (l1, l2) -> Location.locate ~loc:e.Location.loc (Syntax.Channel (s, l1, l2))
                     | Syntax.Channel (s, _, _), Etype.EtyVal -> error ~loc (WrongInputType)
                     | _, Etype.EtyVal -> e
                     | _, _ ->  error ~loc (WrongInputType)) args args_ty))
               else error ~loc (ArgNumMismatch (o, List.length args, List.length args_ty))
            end
            else (ctx, lctx'', Syntax.Let(vid', process_expr ctx lctx e))
         | _ -> (ctx, lctx'', Syntax.Let(vid', process_expr ctx lctx e))
         end

      | Input.Let (vid, e) ->
         let (lctx'', vid') =
            if Context.lctx_check_var lctx vid then (lctx, Syntax.index_var vid (Context.lctx_get_var_index ~loc lctx vid)) else
            let lctx' = Context.lctx_add_new_var ~loc lctx vid in (lctx', Syntax.index_var vid (Context.lctx_get_var_index  ~loc lctx' vid))
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
            if Primitives.check_primitive_ins o then
            begin
               let (_, ins, args_ty) = List.find (fun (s, _, _) -> s = o) Primitives.primitive_ins in
               if List.length args = List.length args_ty then
                  (ctx, lctx'', Syntax.Instruction(vid', ins, 
                     List.map2 (fun arg arg_ty -> 
                     let e = process_expr ctx lctx arg in 
                     match e.Location.data, arg_ty with
                     | Syntax.Channel (s, _, _), Etype.EtyCh (l1, l2) -> Location.locate ~loc:e.Location.loc (Syntax.Channel (s, l1, l2))
                     | Syntax.Channel (s, _, _), Etype.EtyVal -> error ~loc (WrongInputType)
                     | _, Etype.EtyVal -> e
                     | _, _ ->  error ~loc (WrongInputType)) args args_ty))
               else error ~loc (ArgNumMismatch (o, List.length args, List.length args_ty))
            end
            else (ctx, lctx'', Syntax.Let(vid', process_expr ctx lctx e))
         | _ -> (ctx, lctx'', Syntax.Let(vid', process_expr ctx lctx e))
         end
      | Input.If (e, c1, c2) ->
         let e' = process_expr ctx lctx e in 
         let lctx' = Context.lctx_add_frame lctx in 
         let (ctx1, _, c1') = process_stmts ctx lctx' c1 in 
         let (ctx2, _, c2') = process_stmts ctx1 lctx' c2 in 
         (ctx2, lctx, Syntax.If (e', c1', c2'))

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


let process_decl ctx pol def sys {Location.data=c; Location.loc=loc} =
   let process_decl' ctx pol def sys = function
   | Input.DeclExtFun (f, k) -> 
      let ctx' =
         if Context.check_used ctx f then error ~loc (AlreadyDefined f) else 
         if k = 0 then Context.ctx_add_ext_const ctx f else if k > 0 then Context.ctx_add_ext_func ctx (f, k) else error ~loc (NegativeArity k) 
      in (ctx', pol, def, sys)

   | Input.DeclExtEq (e1, e2) -> 
      let rec collect_vars e lctx =
         try let e = process_expr ctx lctx e in (e, lctx)
         with
         | Error {Location.data=err; Location.loc=locc} ->
            begin match err with
            | UnknownIdentifier id -> collect_vars e1 (Context.lctx_add_new_var ~loc lctx id)
            | _ -> error ~loc:locc err
            end
      in 
      let (e1', lctx) = collect_vars e1 Context.lctx_init in 
      let (e2', lctx) = collect_vars e2 lctx in
      (ctx, pol, Context.def_add_ext_eq def (List.hd lctx.Context.lctx_var, e1', e2'), sys)

  (* | DeclExtIns of Name.ident * expr list * event list * expr * event list *)

   | Input.DeclExtIns(id, args, pre, ret, post) -> error ~loc UnintendedError


   | Input.DeclType (id, c) -> 
      if Context.check_used ctx id then error ~loc (AlreadyDefined id) else (Context.ctx_add_ty ctx (id, c), pol, def, sys)
   
   | Input.DeclAccess(s, t, al) -> 
      let tys = Context.ctx_get_ty ~loc ctx s in
      let tyt = Context.ctx_get_ty ~loc ctx t in
      let f pol' a =
         begin
         match tys, tyt, a with
         | Input.CProc, Input.CFsys, "read" -> Context.pol_add_access pol' (s, t, Input.CRead)
         | Input.CProc, Input.CFsys, "write" -> Context.pol_add_access pol' (s, t, Input.CWrite)
         | Input.CProc, Input.CChan, "send" -> Context.pol_add_access pol' (s, t, Input.CSend)
         | Input.CProc, Input.CChan, "recv" -> Context.pol_add_access pol' (s, t, Input.CRecv)
         | _, _, _ -> error ~loc (WrongInputType)
         end
      in (ctx, List.fold_left f pol al, def, sys)

   | Input.DeclAttack (t, al) -> 
      let tyt = Context.ctx_get_ty ~loc ctx t in
      let f pol' a =
         begin
         match tyt, a with
         | Input.CProc, Input.CEaves 
         | Input.CProc, Input.CTamper 
         | Input.CFsys, Input.CEaves 
         | Input.CFsys, Input.CTamper 
         | Input.CChan, Input.CEaves 
         | Input.CChan, Input.CTamper 
         | Input.CChan, Input.CDrop -> Context.pol_add_attack pol' (t, a)
         | _, _-> error ~loc (WrongInputType)
         end
      in (ctx, List.fold_left f pol al, def, sys)

  | Input.DeclInit (id, e) -> 
      if Context.check_used ctx id then error ~loc (AlreadyDefined id) else 
      let e' = process_expr ctx Context.lctx_init e in 
      (Context.ctx_add_const ctx id, pol, Context.def_add_const def (id, e'), sys)

  | Input.DeclFsys (id, fl) ->
      if Context.check_used ctx id then error ~loc (AlreadyDefined id) else 
      let fl' = List.map (fun (a, e, b) -> 
         match Context.ctx_get_ty ~loc ctx b with
         | Input.CFsys ->
            (a, process_expr ctx Context.lctx_init e, b )
         | _ -> error ~loc (WrongInputType)
         ) fl in 
      let (ctx', def') = List.fold_left (fun (ctx', def') (a, e, b) -> (Context.ctx_add_fsys ctx' (id, a, b), Context.def_add_fsys def' (id, a, e))) (ctx, def) fl' in 
      (ctx', pol, def', sys)

  | Input.DeclChan (id, c, ty) ->
      if Context.check_used ctx id then error ~loc (AlreadyDefined id) else 
      (Context.ctx_add_ch ctx (id, c, ty), pol, def, sys)

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
               Context.def_add_proctmpl def pid ldef m', sys)

      | _ -> error ~loc (WrongInputType) 
      end 
   | Input.DeclSys (procs, lemmas) ->
      let processed_procs = List.map (fun proc -> 
         match proc.Location.data with 
         | Input.Proc(pid, chans, fsys) -> 
            if not (Context.ctx_check_proctmpl ctx pid) then error ~loc (UnknownIdentifier pid) else
            if not (Context.ctx_check_fsys ctx fsys) then error ~loc (UnknownIdentifier fsys) else
            let (_, cargs, ptype, _, _) = Context.to_pair_ctx_proctmpl (Context.ctx_get_proctmpl ctx pid) in
            let (_, vl, fl, m) = Context.to_pair_def_proctmpl (Context.def_get_proctmpl def pid) in
            let fpaths = List.fold_left (fun fpaths (fsys', path, ftype) -> if fsys = fsys' then (path, ftype) :: fpaths else fpaths) [] ctx.Context.ctx_fsys in 
            let fpaths = List.map (fun (path, ftype) -> 
                                    let (_ , _ , v) = List.find (fun (fsys', path', val') -> fsys' = fsys && path = path') def.Context.def_fsys in 
                                    (path, v, ftype)) fpaths in 
            let fpaths = List.map (fun (path, v, ftype) -> 
                                    let accs = List.fold_left (fun accs (s, t, a) -> 
                                       if s = ptype && t = ftype then a :: accs else accs) [] pol.Context.pol_access in
                                    let attks = List.fold_left (fun attks (t, a) -> 
                                       if t = ftype then a :: attks else attks) [] pol.Context.pol_attack in
                                    (path,v,accs, attks)) fpaths in 
            if (List.length cargs) !=  (List.length chans) then error ~loc (ArgNumMismatch (pid, (List.length chans), (List.length cargs)))
            else
               let (chs, vl, fl, m) = List.fold_left2 
                  (fun (chs, vl, fl, m) ch_f ch_t -> 
                     if Context.ctx_check_ch ctx ch_t then 
                        let (_, chan_class, chan_ty) = List.find (fun (s, _, _) -> s = ch_t) ctx.Context.ctx_ch in  
                        let accesses = List.fold_left (fun acs (f', t', ac) -> if f' = ptype && t' = chan_ty then ac::acs else acs) [] pol.Context.pol_access in 
                        (
                           (if List.exists (fun (ch_t', _, _, _) -> ch_t = ch_t') chs then chs else
                           (ch_t, chan_class, accesses,
                              List.fold_left (fun attks (s, a) -> if s = ch_t then a :: attks else attks ) [] pol.Context.pol_attack) :: chs),
                              List.map (fun (v, e) -> (v, Substitute.expr_chan_sub e ch_f ch_t accesses chan_class)) vl,
                              List.map (fun (fn, args, c, ret) -> (fn, args, List.map (fun c -> Substitute.stmt_chan_sub c ch_f ch_t accesses chan_class) c, ret)) fl,
                              List.map (fun c -> Substitute.stmt_chan_sub c ch_f ch_t accesses chan_class) m)
                     else error ~loc (UnknownIdentifier ch_t)) ([], vl, fl, m) cargs chans in 
               (pid, 
                  List.fold_left (fun attks (t, a) -> if t = pid then a :: attks else attks) [] pol.Context.pol_attack,
                  chs, fpaths, vl, fl, m)) procs in  
      let (processed_procs, _) = List.fold_left (fun (processed_procs,k) (pid, attks, chans, files, vl, fl, m)
         -> ({Context.proc_pid=k; Context.proc_name=pid; Context.proc_attack=attks; Context.proc_channel=chans; Context.proc_file=files; Context.proc_variable=vl; Context.proc_function=fl; Context.proc_main=m} :: processed_procs, k+1)) 
      ([],0) processed_procs in 
      (ctx, pol, def, {
                        Context.sys_ctx = ctx;
                        Context.sys_pol = pol;
                        Context.sys_def = def;
                        Context.sys_proc=processed_procs}::sys)
in process_decl' ctx pol def sys c


let process_init = (Context.ctx_init, Context.pol_init, Context.def_init, [])

let load fn ctx pol def sys =
   let decls= Lexer.read_file Parser.file fn in 
   let (ctx, pol, def, sys) = List.fold_left 
   (fun (ctx, pol, def, sys) decl -> process_decl ctx pol def sys decl) 
   (ctx, pol, def, sys) decls in (ctx, pol, def, sys)

