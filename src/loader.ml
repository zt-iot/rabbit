(** Conversion from concrete syntax to abstract syntax.
    Here we also load all required files, which may not be
    optimal but is systematic. *)

(** Conversion errors *)
type desugar_error =
  | UnknownVariable of string
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
  | NoBindingVariable
  | WrongChannelType of string * string

exception Error of desugar_error Location.located

(** [error ~loc err] raises the given runtime error. *)
let error ~loc err = Stdlib.raise (Error (Location.locate ~loc err))

(** Print error description. *)
let print_error err ppf =
  match err with
  | UnknownVariable x -> Format.fprintf ppf "unknown identifier %s" x
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
  | WrongChannelType (x, y) -> Format.fprintf ppf "%s type expected but %s given"  x y
  | NoBindingVariable -> Format.fprintf ppf "no binding variable"
  | _ -> Format.fprintf ppf "" 
  

let rec process_expr ctx lctx {Location.data=c; Location.loc=loc} = 
   let process_expr' ctx lctx = function
   | Input.Var id -> 
      if Context.ctx_check_const ctx id then Syntax.Const id
      else if Context.ctx_check_ext_const ctx id then Syntax.ExtConst id
      else if Context.lctx_check_chan lctx id then Syntax.Channel (id, "")
      else if Context.lctx_check_path lctx id then Syntax.Path id
      else if Context.lctx_check_process lctx id then Syntax.Process id
      else if Context.lctx_check_var lctx id then Syntax.Variable id
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


let rec process_expr2 ctx lctx {Location.data=c; Location.loc=loc} = 
   let process_expr2' ctx lctx = function
   | Input.Var id -> 
      if Context.ctx_check_const ctx id then Syntax.Const id
      else if Context.ctx_check_ext_const ctx id then Syntax.ExtConst id
      else if Context.lctx_check_chan lctx id then Syntax.Channel (id, "")
      else if Context.lctx_check_path lctx id then Syntax.Path id
      else if Context.lctx_check_process lctx id then Syntax.Process id
      else if Context.lctx_check_var lctx id then Syntax.Variable id
      else if Context.lctx_check_meta lctx id then Syntax.Variable id
      else error ~loc (UnknownVariable id) 
   | Input.Boolean b -> Syntax.Boolean b
   | Input.String s -> Syntax.String s 
   | Input.Integer z -> Syntax.Integer z
   | Input.Float f -> Syntax.Float f
   | Input.Apply(o, el) ->
      if Context.ctx_check_ext_syscall ctx o then error ~loc (ForbiddenIdentifier o) else
      if Context.ctx_check_ext_func_and_arity ctx (o, List.length el) then Syntax.Apply (o, (List.map (fun a -> process_expr2 ctx lctx a) el)) else
      error ~loc (UnknownIdentifier o)
   | Input.Tuple el -> Syntax.Tuple (List.map (fun a -> process_expr2 ctx lctx a) el)
  in
  let c = process_expr2' ctx lctx c in
  Location.locate ~loc c


let process_fact_closed ctx lctx f =
   let loc = f.Location.loc in 
   match f.Location.data with
   | Input.Fact (id, el) ->
      (Context.ctx_add_or_check_fact ~loc ctx (id, List.length el), 
         Location.locate ~loc:f.Location.loc (Syntax.Fact(id, List.map (process_expr2 ctx lctx) el)))
   | Input.GlobalFact (id, el) ->
      (Context.ctx_add_or_check_fact ~loc ctx (id, List.length el), 
         Location.locate ~loc:f.Location.loc (Syntax.GlobalFact(id, List.map (process_expr2 ctx lctx) el)))
   | Input.ChannelFact (l, id, el) ->
      (* check validty of local scope l *)
      if Context.lctx_check_chan lctx l || Context.lctx_check_meta lctx l then 
         (Context.ctx_add_or_check_lfact ~loc ctx (id, List.length el), 
            Location.locate ~loc:f.Location.loc (Syntax.ChannelFact(l, id, List.map (process_expr2 ctx lctx) el)))
      else if Context.lctx_check_id lctx l then error ~loc (UnknownVariable id)
      else error ~loc (UnknownIdentifier_ch l)
   | Input.PathFact (l, id, el) ->
      (* check validty of local scope l *)
      if Context.lctx_check_path lctx l || Context.lctx_check_meta lctx l then 
         (Context.ctx_add_or_check_lfact ~loc ctx (id, List.length el), 
            Location.locate ~loc:f.Location.loc (Syntax.PathFact(l, id, List.map (process_expr2 ctx lctx) el)))
      else if Context.lctx_check_id lctx l then error ~loc (UnknownVariable id)
      else error ~loc (UnknownIdentifier_path l)
   | _ -> error ~loc (UnknownIdentifier2 "")

let process_facts_closed ctx lctx fl = 
   List.fold_left (fun (ctx, fl) f -> 
      let (ctx, f) = process_fact_closed ctx lctx f in 
      (ctx, fl @ [f])) (ctx, []) fl

let rec process_fact ctx lctx f =
   try 
      let (ctx, f) = process_fact_closed ctx lctx f in
      (ctx, lctx, f)
   with 
   | Error {Location.data=err; Location.loc=locc} ->
      begin match err with
      | UnknownVariable v -> 
         process_fact ctx (Context.lctx_add_new_meta ~loc:locc lctx v) f
      | _ -> error ~loc:locc err
   end

let process_facts ctx lctx fl = 
   List.fold_left (fun (ctx, lctx, fl) f -> 
      let (ctx, lctx, f) = process_fact ctx lctx f in 
      (ctx, lctx, fl @ [f])) (ctx, lctx, []) fl


let rec process_cmd ctx lctx {Location.data=c; Location.loc=loc} = 
   let process_cmd' ctx lctx = function
      | Input.Skip -> (ctx, lctx, Syntax.Skip)
      
      | Input.Sequence (c1, c2) -> 
         let (ctx, lctx, c1) = process_cmd ctx lctx c1 in
         let (ctx, lctx, c2) = process_cmd ctx lctx c2 in
         (ctx, lctx, Syntax.Sequence (c1, c2))

      | Input.Wait (fl, c) -> 
         let lctx' = Context.lctx_add_frame lctx in
         let (ctx, lctx', fl) = process_facts ctx lctx' fl in  
         let (ctx, lctx', c) = process_cmd ctx lctx' c in
         (ctx, lctx, Syntax.Wait (fl, c))

      | Input.Put fl -> 
         let (ctx, fl) = process_facts_closed ctx lctx fl in 
         (ctx, lctx, Syntax.Put (fl))

      | Input.Let (v, e) -> 
         (if Context.lctx_check_var lctx v then error ~loc (AlreadyDefined v) else ());
         let lctx = Context.lctx_add_new_var ~loc lctx v in
         (ctx, lctx, Syntax.Let(v, process_expr ctx lctx e))

      | Input.Assign (ov, e) -> 
         (match ov with | Some v -> if Context.lctx_check_var lctx v then () else error ~loc (UnknownIdentifier v) | _ -> ());
         begin match e.Location.data with
         | Input.Apply(o, args) ->
            if Context.ctx_check_ext_syscall ctx o 
            then 
               (*  when o is a system call *)
               begin
                  let args_ty = Context.ctx_get_ext_syscall_arity ~loc ctx o in
                  (if List.length args = List.length args_ty then () else error ~loc (ArgNumMismatch (o, List.length args, List.length args_ty)));
                  (ctx, lctx, Syntax.SCall(ov, o, 
                     List.map2 (fun arg arg_ty -> 
                        let e = process_expr ctx lctx arg in                   
                           (match e.Location.data, arg_ty with
                           | Syntax.Channel (s, _), Input.TyChannel -> Location.locate ~loc:e.Location.loc (Syntax.Channel (s, o))
                           | _, Input.TyChannel -> error ~loc (WrongInputType)
                           | _, _ -> e)
                           (* , arg_ty *)
                        ) args args_ty))
               end
            (*  when o is a function *)
            else if Context.lctx_check_func lctx o then
            begin
               (if List.length args = Context.lctx_get_func_arity lctx o then () else error ~loc (ArgNumMismatch (o, List.length args, (Context.lctx_get_func_arity lctx o))));
               (ctx, lctx, Syntax.FCall(ov, o, List.map (process_expr ctx lctx) args))
            end
            else 
            (* when o is a term *)
            match ov with
            | Some v -> (ctx, lctx, Syntax.Assign(v, process_expr ctx lctx e))
            | _ -> error ~loc (NoBindingVariable)
         | _ ->           
            match ov with
            | Some v -> (ctx, lctx, Syntax.Assign(v, process_expr ctx lctx e))
            | _ -> error ~loc (NoBindingVariable)
         end 

      | Input.Case (al, c1, bl, c2) ->
         let plctx = Context.lctx_add_frame lctx in
         
         let (ctx, lctx1, al) = process_facts ctx plctx al in 
         let (ctx, _, c1) = process_cmd ctx lctx1 c1 in 

         let (ctx, lctx2, bl) = process_facts ctx plctx bl in 
         let (ctx, _, c2) = process_cmd ctx lctx2 c2 in 

         (ctx, lctx, Syntax.Case (al, c1, bl, c2))

     | Input.While (al, bl, c) ->
         let plctx = Context.lctx_add_frame lctx in
         let (ctx, plctx, al) = process_facts ctx plctx al in
         let (ctx, plctx, bl) = process_facts ctx plctx bl in
         let (ctx, plctx, c) = process_cmd ctx plctx c in 
         (ctx, lctx, Syntax.While (al, bl, c))

     | Input.Event (fl) ->
         let (ctx, fl) = process_facts_closed ctx lctx fl in
         (ctx, lctx, Syntax.Event (fl))
      in 
      let (ctx, lctx, c) = process_cmd' ctx lctx c in 
      (ctx, lctx, ((lctx.Context.lctx_meta, lctx.Context.lctx_var), Location.locate ~loc c))


let process_init = (Context.ctx_init, Context.pol_init, Context.def_init, [], ([],[]))

let rec process_decl ctx pol def sys ps {Location.data=c; Location.loc=loc} =
   let process_decl' ctx pol def sys ps = function
   | Input.DeclLoad fn ->
      (*  *)
      let ((a, b), fn') = ps in 
      let new_fn = (Filename.dirname fn') ^ "/" ^ fn in 
      let (ctx, pol, def, sys, parser_state) = load new_fn ctx pol def sys in 
      let parser_state = 
      (* marge  parser_state and ps*)
      (fst parser_state @ a, snd parser_state @ b) in

      (ctx, pol, def, sys, parser_state) 

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


   | Input.DeclExtSyscall(f, typed_args, c, e) ->      
      (if Context.check_used ctx f then error ~loc (AlreadyDefined f) else ());

         (* parse arguments *)
         let lctx = List.fold_left (fun lctx' ta -> 
            match ta with
            | (Input.TyValue, v) -> Context.lctx_add_new_var ~loc lctx' v
            | (Input.TyChannel, v) -> Context.lctx_add_new_chan ~loc lctx' v
            | (Input.TyPath, v) -> Context.lctx_add_new_path ~loc lctx' v
            | (Input.TyProcess, v) -> error ~loc (UnknownIdentifier2 v)) (Context.lctx_init) typed_args in

         let lctx = Context.lctx_add_frame lctx in 
         let (ctx, lctx, c) = process_cmd ctx lctx c in
         let ch_args = lctx.Context.lctx_chan in 
         let path_args = lctx.Context.lctx_path in 

         (Context.ctx_add_ext_syscall ctx (f, List.map fst typed_args), 
            pol, 
            Context.def_add_ext_syscall def (f, typed_args, c, process_expr ctx lctx e), sys, fst ps)

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
      with | Input.CProc -> () | _ -> error ~loc (WrongInputType) end;
      (if Context.check_used ctx pid then error ~loc (AlreadyDefined pid) else ());
      (* load channel parameters *)
      let lctx = List.fold_left (fun lctx' (cid, cty) -> 
         if Context.ctx_check_ty_ch ctx cty 
         then 
            Context.lctx_add_new_chan ~loc lctx' cid
         else
            error ~loc (UnknownIdentifier cty)
         ) Context.lctx_init cargs in

      (* load top-level variables *)
      let (lctx, ldef) = List.fold_left (fun (lctx', ldef') (vid, e) -> 
         (Context.lctx_add_new_var ~loc lctx' vid, Context.ldef_add_new_var ldef' (vid, process_expr ctx lctx' e))) (lctx, Context.ldef_init) cl in

      (* load functions *)
      let (ctx, lctx, ldef) = List.fold_left (fun (ctx'', lctx'', ldef'') (fid, args, cs, ret) -> 
         if Context.lctx_check_func lctx'' fid then error ~loc (AlreadyDefined fid) else 
         let lctx = List.fold_left (fun lctx' vid -> Context.lctx_add_new_var ~loc lctx' vid) (Context.lctx_add_frame lctx'') args in
         let (ctx', lctx', cs')  = process_cmd ctx'' lctx cs in 
         (ctx', Context.lctx_add_new_func ~loc lctx'' (fid, List.length args), 
               Context.ldef_add_new_func ldef'' (fid, args, cs', process_expr ctx' lctx' ret))) (ctx, lctx, ldef) fs in

      (* load main function *)
      let (ctx, _, m') = process_cmd ctx (Context.lctx_add_frame lctx) m in 

      (Context.ctx_add_proctmpl ctx (Context.mk_ctx_proctmpl (pid, List.rev cargs, ty, List.hd lctx.Context.lctx_var, lctx.Context.lctx_func)), pol, 
         Context.def_add_proctmpl def pid ldef m', sys, fst ps)

      

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
                  (fun (chs, vl, fl, m) (ch_f, ty_f) ch_t -> 
                     (* print_string (ch_f ^ " to "^ch_t^"\n") ; *)
                     if Context.ctx_check_ch ctx ch_t then 
                        let (_, chan_ty) = List.find (fun (s, _
                        ) -> s = ch_t) ctx.Context.ctx_ch in
                        (if chan_ty = ty_f then () else error ~loc (WrongChannelType (ch_f^":"^ty_f, ch_t^":"^chan_ty)));  
                        let accesses = List.fold_left (fun acs (f', t', ac) -> if f' = ptype && List.exists (fun s -> s = chan_ty) t' then ac::acs else acs) [] pol.Context.pol_access in 
                        (* replace channel variables and check access policies! *)
                        (
                           (if List.exists (fun (ch_t', _,  _) -> ch_t = ch_t') chs then chs else
                           (ch_t, accesses,
                              List.fold_left (fun attks (s, a) -> if s = ch_t then a :: attks else attks ) [] pol.Context.pol_attack) :: chs),
                              List.map (fun (v, e) -> (v, Substitute.expr_chan_sub e ch_f ch_t accesses)) vl,
                              List.map (fun (fn, args, c, ret) -> (fn, args, Substitute.cmd_chan_sub c ch_f ch_t accesses, ret)) fl,
                              Substitute.cmd_chan_sub m ch_f ch_t accesses)
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
               | _ -> error ~loc:loc UnintendedError
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
      


in process_decl' ctx pol def sys ps c

and load fn ctx pol def sys =
   let decls, parser_state = Lexer.read_file Parser.file fn in 
   let (ctx, pol, def, sys, parser_state) = List.fold_left 
   (fun (ctx, pol, def, sys, parser_state) decl -> process_decl ctx pol def sys (parser_state, fn) decl)  
   (ctx, pol, def, sys, parser_state) decls in (ctx, pol, def, sys, parser_state)

