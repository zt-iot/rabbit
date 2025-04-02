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
  | UnknownVariable x -> Format.fprintf ppf "unknown variable %s" x
  | UnknownIdentifier x -> Format.fprintf ppf "unknown identifier %s" x
  | UnknownIdentifier_ch x -> Format.fprintf ppf "unknown identifier channel %s" x
  | UnknownIdentifier_path x -> Format.fprintf ppf "unknown identifier path %s" x
  | UnknownIdentifier_process x -> Format.fprintf ppf "unknown identifier process %s" x
  | UnknownIdentifier2 x -> Format.fprintf ppf "unknown identifier2 %s" x
  | UnknownFunction x -> Format.fprintf ppf "unknown function %s" x
  | AlreadyDefined x -> Format.fprintf ppf "identifier already defined %s" x
  | ForbiddenIdentifier x -> Format.fprintf ppf "forbidden identifier %s" x
  | ArgNumMismatch (x, i, j) -> Format.fprintf ppf "%s arguments provided while %s requires %s" (string_of_int i) x (string_of_int j)
  | NegativeArity k -> Format.fprintf ppf "negative arity is given: %s" (string_of_int k)
  | ForbiddenFresh -> Format.fprintf ppf "fresh is reserved identifier"
  | UnintendedError -> Format.fprintf ppf "unintended behavior. contact the developer"
  | WrongInputType -> Format.fprintf ppf "wrong input type"
  | NoBindingVariable -> Format.fprintf ppf "no binding variable"
  | WrongChannelType (x, y) -> Format.fprintf ppf "%s type expected but %s given"  x y
  

let find_index f lst =
  let rec aux i = function
    | [] -> None
    | x :: xs -> if f x then Some i else aux (i + 1) xs
  in
  aux 0 lst

let rec process_expr ?(param="") ctx lctx {Location.data=c; Location.loc=loc} = 
   let process_expr' ctx lctx = function
   | Input.Var id -> 
      if Context.ctx_check_const ctx id then Syntax.Const id
      else if Context.ctx_check_ext_const ctx id then Syntax.ExtConst id
      else if Context.lctx_check_chan lctx id then Syntax.Channel (id, "")
      else if Context.lctx_check_path lctx id then Syntax.Path id
      else if Context.lctx_check_process lctx id then Syntax.Process id
      else if Context.lctx_check_param lctx id then Syntax.Param id
      else if id = param then Syntax.Param id 
      else 
         begin
            match find_index (fun v -> v = id) lctx.Context.lctx_top_var with
         | Some i -> Syntax.TopVariable (id, i)
         | None -> 
            match find_index (fun v -> v = id) lctx.Context.lctx_loc_var with
            | Some i -> Syntax.LocVariable (id, i)
            | None -> 
               match find_index (fun v -> v = id) lctx.Context.lctx_meta_var with
               | Some i -> Syntax.MetaVariable (id, i)
               | None -> error ~loc (UnknownIdentifier id) 
      end
   | Input.Boolean b -> Syntax.Boolean b
   | Input.String s -> Syntax.String s 
   | Input.Integer z -> Syntax.Integer z
   | Input.Float f -> Syntax.Float f
   | Input.Apply(o, el) ->
      if Context.ctx_check_ext_syscall ctx o then error ~loc (ForbiddenIdentifier o) else
      if Context.ctx_check_ext_func_and_arity ctx (o, List.length el) then Syntax.Apply (o, (List.map (fun a -> process_expr ~param:param ctx lctx a) el)) else
      error ~loc (UnknownIdentifier o)
   | Input.Tuple el -> Syntax.Tuple (List.map (fun a -> process_expr ~param:param ctx lctx a) el)
   | Input.Param (pid, p) -> 
      if Context.ctx_check_param_const ctx pid then 
         Syntax.ParamConst (pid, process_expr ~param:param ctx lctx p) 
      else if Context.lctx_check_param_chan lctx pid then Syntax.ParamChan (pid, process_expr ~param:param ctx lctx p) 
      else error ~loc (UnknownIdentifier pid) 
  in
  let c = process_expr' ctx lctx c in
  Location.locate ~loc c


let rec process_expr2 new_meta_vars ctx lctx {Location.data=c; Location.loc=loc} = 
   let process_expr2' new_meta_vars ctx lctx = function
   | Input.Var id -> 
      if Context.ctx_check_const ctx id then Syntax.Const id
      else if Context.ctx_check_ext_const ctx id then Syntax.ExtConst id
      else if Context.lctx_check_chan lctx id then Syntax.Channel (id, "")
      else if Context.lctx_check_path lctx id then Syntax.Path id
      else if Context.lctx_check_process lctx id then Syntax.Process id
      else if Context.lctx_check_param lctx id then Syntax.Param id
      else 
      begin
         match find_index (fun v -> v = id) lctx.Context.lctx_top_var with
         | Some i -> Syntax.TopVariable (id, i)
         | None -> 
            match find_index (fun v -> v = id) lctx.Context.lctx_loc_var with
            | Some i -> Syntax.LocVariable (id, i)
            | None -> 
               match find_index (fun v -> v = id) lctx.Context.lctx_meta_var with
               | Some i -> Syntax.MetaVariable (id, i)
               | None -> 
                  match find_index (fun v -> v = id) new_meta_vars with
                  | Some i -> Syntax.MetaNewVariable (id, i)
                  | None -> error ~loc (UnknownVariable id) 
      end
   | Input.Boolean b -> Syntax.Boolean b
   | Input.String s -> Syntax.String s 
   | Input.Integer z -> Syntax.Integer z
   | Input.Float f -> Syntax.Float f
   | Input.Apply(o, el) ->
      if Context.ctx_check_ext_syscall ctx o then error ~loc (ForbiddenIdentifier o) else
      if Context.ctx_check_ext_func_and_arity ctx (o, List.length el) then Syntax.Apply (o, (List.map (fun a -> process_expr2 new_meta_vars ctx lctx a) el)) else
      error ~loc (UnknownIdentifier o)
   | Input.Tuple el -> Syntax.Tuple (List.map (fun a -> process_expr2 new_meta_vars ctx lctx a) el)
   
   | Input.Param (pid, p) -> 
      if Context.ctx_check_param_const ctx pid then Syntax.ParamConst (pid, process_expr2 new_meta_vars ctx lctx p) 
      else if Context.lctx_check_param_chan lctx pid then Syntax.ParamChan (pid, process_expr2 new_meta_vars ctx lctx p) 
      else error ~loc (UnknownIdentifier pid) 

  in
  let c = process_expr2' new_meta_vars ctx lctx c in
  Location.locate ~loc c


let process_fact_closed new_meta_vars ctx lctx f =
   let loc = f.Location.loc in 
   match f.Location.data with
   | Input.Fact (id, el) ->
      (Context.ctx_add_or_check_lfact ~loc ctx (id, List.length el), 
         Location.locate ~loc:f.Location.loc (Syntax.Fact(id, List.map (process_expr2 new_meta_vars ctx lctx) el)))
   | Input.GlobalFact (id, el) ->
      (Context.ctx_add_or_check_fact ~loc ctx (id, List.length el), 
         Location.locate ~loc:f.Location.loc (Syntax.GlobalFact(id, List.map (process_expr2 new_meta_vars ctx lctx) el)))
   | Input.ChannelFact (l, id, el) ->
      (* check validty of local scope l *)
         (Context.ctx_add_or_check_lfact ~loc ctx (id, List.length el), 
                  Location.locate ~loc:f.Location.loc 
                  (Syntax.ChannelFact(process_expr2 new_meta_vars ctx lctx l,
                        id, List.map (process_expr2 new_meta_vars ctx lctx) el)))
   (* | Input.PathFact (l, "File", e) ->
      (* check validty of local scope l *)
         (Context.ctx_add_or_check_lfact ~loc ctx (id, List.length el), 
                  Location.locate ~loc:f.Location.loc 
                  (Syntax.PathFact(process_expr2 new_meta_vars ctx lctx l,
                        id, List.map (process_expr2 new_meta_vars ctx lctx) el))) *)
   | Input.ResFact(i, el) ->
         (ctx, Location.locate ~loc:f.Location.loc 
                  (Syntax.ResFact(i, List.map (process_expr2 new_meta_vars ctx lctx) el)))

   | _ -> error ~loc (UnknownIdentifier2 "")

let process_facts_closed new_meta_vars ctx lctx fl = 
   List.fold_left (fun (ctx, fl) f -> 
      let (ctx, f) = process_fact_closed new_meta_vars ctx lctx f in 
      (ctx, fl @ [f])) (ctx, []) fl

let rec collect_meta_fact new_meta_vars ctx lctx f =
   try 
      let (ctx, f) = process_fact_closed new_meta_vars ctx lctx f in
      (ctx, lctx, f), []
   with 
   | Error {Location.data=err; Location.loc=locc} ->
      begin match err with
      | UnknownVariable v -> 
         let (r, l) = collect_meta_fact (v::new_meta_vars) ctx lctx f in
         (r, l @ [v])
      | _ -> error ~loc:locc err
   end

let collect_meta_facts ctx lctx fl = 
   List.fold_left (fun ((ctx, lctx, fl), ls) f -> 
      let (ctx, lctx, f), l = collect_meta_fact ls ctx lctx f in 
      ((ctx, lctx, fl @ [f]), ls @ l)) ((ctx, lctx, []), []) fl

let process_facts ctx lctx fl = 
   let _, vl = collect_meta_facts ctx lctx fl in
   (* let lctx = {lctx with Context.lctx_meta_var = vl@lctx.Context.lctx_meta_var} in  *)
   let (ctx, fl) = process_facts_closed vl ctx lctx fl in
   (ctx, lctx, fl), vl

let rec process_cmd ctx lctx {Location.data=c; Location.loc=loc} = 
   let process_cmd' ctx lctx = function
      | Input.Skip -> (ctx, lctx, Syntax.Skip)
      
      | Input.Sequence (c1, c2) -> 
         let (ctx, lctx, c1) = process_cmd ctx lctx c1 in
         let (ctx, lctx, c2) = process_cmd ctx lctx c2 in
         (ctx, lctx, Syntax.Sequence (c1, c2))

      | Input.Put fl -> 
         let (ctx, fl) = process_facts_closed [] ctx lctx fl in 
         (ctx, lctx, Syntax.Put (fl))

      | Input.Let (v, e, c) -> 
         begin 
         match e.Location.data with
         | Input.Apply(o, args) ->
            let eloc = e.Location.loc in
            begin
               if Context.ctx_check_ext_syscall ctx o || Context.lctx_check_func lctx o
               then let ctx, lctx, c = process_cmd ctx lctx (Location.locate ~loc:loc 
                                          (Input.Let (v, Location.locate ~loc:eloc (Input.String ""), 
                                             Location.locate ~loc:eloc (Input.Sequence (
                                             Location.locate ~loc:eloc (Input.Assign (Some v, e)), c))))) in 
                     (ctx, lctx, c.Location.data)
               else
                  begin
                     (if Context.lctx_check_var lctx v then error ~loc (AlreadyDefined v) else ());
                     let lctx' = Context.lctx_add_new_var ~loc lctx v in
                     let (ctx, _, c) = process_cmd ctx lctx' c in 
                     (ctx, lctx, Syntax.Let(v, process_expr ctx lctx e, c))
                  end
            end
         | _ -> 
                  (if Context.lctx_check_var lctx v then error ~loc (AlreadyDefined v) else ());
                  let lctx' = Context.lctx_add_new_var ~loc lctx v in
                  let (ctx, _, c) = process_cmd ctx lctx' c in 
                  (ctx, lctx, Syntax.Let(v, process_expr ctx lctx e, c))
         end
      | Input.Assign (ov, e) -> 
         let ov = 
         (match ov with 
            | Some id -> 
               begin match find_index (fun v -> v = id) lctx.Context.lctx_top_var with
               | Some i -> (Some (id, (i, true)))
               | None -> 
                  match find_index (fun v -> v = id) lctx.Context.lctx_loc_var with
                  | Some i -> (Some (id, (i, false)))
                  | None -> error ~loc (UnknownIdentifier id) 
(*                      match find_index (fun v -> v = id) lctx.Context.lctx_meta_var with
                     | Some i -> Syntax.MetaVariable (id, i)
                     | None -> error ~loc (UnknownIdentifier id) 
 *)
             end 
            | None -> None) in 
         begin match e.Location.data with
         | Input.Apply(o, args) ->
            begin
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
            end
         | _ ->           
            match ov with
            | Some v -> (ctx, lctx, Syntax.Assign(v, process_expr ctx lctx e))
            | _ -> error ~loc (NoBindingVariable)
         end 

            
      | Input.Case (cs) ->

         let ctx, cs = List.fold_left 
            (fun (ctx, cs) (fl, c) -> 
               let (ctx, lctx', fl), vl = process_facts ctx lctx fl in 
               let (ctx, _, c) = process_cmd ctx {lctx with Context.lctx_meta_var = vl@lctx.Context.lctx_meta_var} c in 
               (ctx, cs @ [(vl, fl, c)])) (ctx, []) cs in         

         (ctx, lctx, Syntax.Case (cs))

     | Input.While (cs1, cs2) ->

         let ctx, cs1 = List.fold_left 
         (fun (ctx, cs) (fl, c) -> 
            let (ctx, lctx', fl), vl = process_facts ctx lctx fl in 
            let (ctx, _, c) = process_cmd ctx {lctx with Context.lctx_meta_var = vl@lctx.Context.lctx_meta_var} c in 
            (ctx, cs @ [(vl, fl, c)])) (ctx, []) cs1 in         

         let ctx, cs2 = List.fold_left 
         (fun (ctx, cs) (fl, c) -> 
            let (ctx, lctx', fl), vl = process_facts ctx lctx fl in 
            let (ctx, _, c) = process_cmd ctx {lctx with Context.lctx_meta_var = vl@lctx.Context.lctx_meta_var} c in 
            (ctx, cs @ [(vl, fl, c)])) (ctx, []) cs2 in         

         (ctx, lctx, Syntax.While (cs1, cs2))

     | Input.Event (fl) ->
         let (ctx, fl) = process_facts_closed [] ctx lctx fl in
         (ctx, lctx, Syntax.Event (fl))

      | Input.Return e ->
         (ctx, lctx, Syntax.Return (process_expr ctx lctx e))


      | Input.New (v, fid, el, c) ->
         (if Context.lctx_check_var lctx v then error ~loc (AlreadyDefined v) else ());
         let ctx = Context.ctx_add_or_check_inj_fact ~loc ctx (fid, List.length el) in 
         (* (if Context.ctx_check_inj_fact ctx fid then error ~loc (AlreadyDefined v) else ()); *)
         let lctx' = Context.lctx_add_new_meta ~loc lctx v in
         let (ctx, _, c) = process_cmd ctx lctx' c in 
         (ctx, lctx, Syntax.New(v, fid, List.map (process_expr ctx lctx) el, c))


      | Input.Get (vl, id, fid, c) ->
         (if not (Context.ctx_check_inj_fact ctx fid) then error ~loc (UnknownIdentifier fid) else ());
         (
            let i = Context.ctx_get_inj_fact_arity ~loc ctx fid in 
            let j = List.length vl in if not (i = j) then error ~loc (ArgNumMismatch (fid,i,j)) else ());
            let lctx' = List.fold_left (fun lctx' v ->
            (if Context.lctx_check_var lctx v then error ~loc (AlreadyDefined v) else ());
            Context.lctx_add_new_meta ~loc lctx' v
            ) lctx (List.rev vl) in
         let (ctx, _, c) = process_cmd ctx lctx' c in 
         (ctx, lctx, Syntax.Get(vl, process_expr ctx lctx id, fid, c))
   

      | Input.Del (id, fid) ->
         (if not (Context.ctx_check_inj_fact ctx fid) then error ~loc (UnknownIdentifier fid) else ());
         (ctx, lctx, Syntax.Del(process_expr ctx lctx id, fid))  

      in 
      
      let (ctx, lctx, c) = process_cmd' ctx lctx c in 
      (ctx, lctx, Location.locate ~loc c)
      (* (ctx, lctx, ((lctx.Context.lctx_meta_var, lctx.Context.lctx_loc_var, lctx.Context.lctx_top_var), Location.locate ~loc c)) *)


let process_init = (Context.ctx_init, Context.pol_init, Context.def_init, [], ([],[]))

let process_pproc ?(param="") loc ctx def pol (proc : Input.pproc) = 
   let (pid, files, vl, fl, m, cargs, chans, ptype) = 
   begin match proc.Location.data with 
   | Input.ParamProc(pid, param', chans) -> 
      if not (Context.ctx_check_proctmpl ctx pid) then error ~loc (UnknownIdentifier pid) else
      let (_, param'', cargs, ptype, _, _) = Context.to_pair_ctx_proctmpl (Context.ctx_get_proctmpl ctx pid) in
      (match param'' with 
      | Some _ -> () | None -> error ~loc (UnknownIdentifier ""));
      let cargs = List.rev cargs in 
      let (_, files, vl, fl, m) = Context.to_pair_def_proctmpl (Context.def_get_proctmpl def pid) in
      let realparam = process_expr ~param:param ctx Context.lctx_init param' in      
      let files = List.map (fun (p, ty, e) -> (Substitute.expr_param p realparam, ty, Substitute.expr_param e realparam)) files in 
      let vl = List.map (fun (v, e) -> (v, Substitute.expr_param e realparam)) vl in 
      let fl = List.map (fun (fn, args, c) -> (fn, args, Substitute.cmd_param c realparam)) fl in 
      let m = Substitute.cmd_param m realparam in
      
      (pid, files, vl, fl, m, cargs, chans, ptype)

   | Input.Proc(pid, chans) -> 
      if not (Context.ctx_check_proctmpl ctx pid) then error ~loc (UnknownIdentifier pid) else
      let (_, param', cargs, ptype, _, _) = Context.to_pair_ctx_proctmpl (Context.ctx_get_proctmpl ctx pid) in
      (match param' with 
      | Some _ -> error ~loc (UnknownIdentifier "") | None -> ());
      let cargs = List.rev cargs in 
      let (_, files, vl, fl, m) = Context.to_pair_def_proctmpl (Context.def_get_proctmpl def pid) in
   
      (pid, files, vl, fl, m, cargs, chans, ptype)
      end in 

      (* substitute channels *)
      if (List.length cargs) !=  (List.length chans) then error ~loc (ArgNumMismatch (pid, (List.length chans), (List.length cargs)))
      else
         let (files, vl, fl, m, installed_channels) = List.fold_left2 
            (fun (files, vl, fl, m, installed_channels) (is_param, ch_f, ty_f) ch_t -> 
               begin match ch_t with
               | Input.ChanArgPlain ch_t ->
                  (if is_param then error ~loc (WrongChannelType   ("", "")) else ());
                  (if not (Context.ctx_check_ch ctx ch_t) then error ~loc (UnknownIdentifier ch_t) else ());
                  let (_, chan_ty) = List.find (fun (s, _) -> s = ch_t) ctx.Context.ctx_ch in
                  (if chan_ty = ty_f then () else error ~loc (WrongChannelType (ch_f^":"^ty_f, ch_t^":"^chan_ty)));  
                     (* replace channel variables and check access policies! *)
                  let new_chan = (Location.locate ~loc:Location.Nowhere (Syntax.Channel (ch_t, ""))) in 
                     (
                     List.map (fun (p, ty, e) -> (Substitute.expr_chan_sub p ch_f new_chan, ty, Substitute.expr_chan_sub e ch_f new_chan)) files,   
                     List.map (fun (v, e) -> (v, Substitute.expr_chan_sub e ch_f new_chan)) vl,
                     List.map (fun (fn, args, c) -> (fn, args, Substitute.cmd_chan_sub c ch_f new_chan)) fl,
                     Substitute.cmd_chan_sub m ch_f new_chan,
                     (Syntax.ChanArgPlain (ch_t, ty_f))::installed_channels
                     )
               
               | Input.ChanArgParam ch_t ->
                  (if not is_param then error ~loc (WrongChannelType   ("", "")) else ());
                  (if not (Context.ctx_check_param_ch ctx ch_t) then error ~loc (UnknownIdentifier ch_t) else ());
                  (*  *)
                  let (_, chan_ty) = List.find (fun (s, _) -> s = ch_t) ctx.Context.ctx_param_ch in
                  (if chan_ty = ty_f then () else error ~loc (WrongChannelType (ch_f^":"^ty_f, ch_t^":"^chan_ty)));  
                     (* replace channel variables and check access policies! *)
                  (
                     List.map (fun (p, ty, e) -> (Substitute.expr_param_chan_sub p ch_f ch_t, ty, Substitute.expr_param_chan_sub e ch_f ch_t)) files,
                     List.map (fun (v, e) -> (v, Substitute.expr_param_chan_sub e ch_f ch_t)) vl,
                     List.map (fun (fn, args, c) -> (fn, args, Substitute.cmd_param_chan_sub c ch_f ch_t)) fl,
                     Substitute.cmd_param_chan_sub m ch_f ch_t,
                     (Syntax.ChanArgParam (ch_t, ty_f))::installed_channels
                     )
               
               | Input.ChanArgParamInst (cid, e) ->
                  (if is_param then error ~loc (WrongChannelType   ("", "")) else ());
                  (if not (Context.ctx_check_param_ch ctx cid) then error ~loc (UnknownIdentifier cid) else ());
                  let (_, chan_ty) = List.find (fun (s, _) -> s = cid) ctx.Context.ctx_param_ch in
                  (if chan_ty = ty_f then () else error ~loc (WrongChannelType (ch_f^":"^ty_f, cid^":"^chan_ty)));  
                  (* replace channel variables and check access policies! *)
                  let e = process_expr ~param:param ctx Context.lctx_init e in 
                  let new_chan = (Location.locate ~loc:Location.Nowhere (Syntax.ParamChan (cid, e))) in 
                  (
                     List.map (fun (p, ty, e) -> (Substitute.expr_chan_sub p ch_f new_chan, ty, Substitute.expr_chan_sub e ch_f new_chan)) files,
                     List.map (fun (v, e) -> (v, Substitute.expr_chan_sub e ch_f new_chan)) vl,
                     List.map (fun (fn, args, c) -> (fn, args, Substitute.cmd_chan_sub c ch_f new_chan)) fl,
                     Substitute.cmd_chan_sub m ch_f new_chan,
                     (Syntax.ChanArgParamInst (cid, e, ty_f))::installed_channels
                  )

               end) (files, vl, fl, m, []) cargs chans in 
               {Context.proc_pid=0; 
               Context.proc_type =ptype; 
               Context.proc_filesys= files; 
               Context.proc_name=pid; 
               Context.proc_variable=vl; 
               Context.proc_function=fl; 
               Context.proc_main=m;
               Context.proc_channels=installed_channels}

         (* (pid, fpaths, vl, fl, m, ptype, fsys) *)

         (* | UnboundedProc of pproc 
         | BoundedProc of (Name.ident * pproc list) *)
         
let process_proc loc ctx def pol (proc : Input.proc) = 
   match proc with
   | Input.UnboundedProc p -> 
      ([process_pproc loc ctx def pol p], [])
   | Input.BoundedProc (pname, pl) ->
      let pl = List.map (process_pproc ~param:pname loc ctx def pol) pl in 
      ([], pl)

let rec process_decl ctx pol def sys ps ({Location.data=c; Location.loc=loc} : Input.decl) =
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
      (ctx, pol, Context.def_add_ext_eq def (lctx.Context.lctx_loc_var, e1', e2'), sys, fst ps)

   | Input.DeclExtSyscall(f, typed_args, c) ->      
      (if Context.check_used ctx f then error ~loc (AlreadyDefined f) else ());

         (* parse arguments *)
         let lctx = List.fold_left (fun lctx' ta -> 
            match ta with
            | (Input.TyValue, v) -> Context.lctx_add_new_var ~loc lctx' v
            | (Input.TyChannel, v) -> Context.lctx_add_new_chan ~loc lctx' v
            | (Input.TyPath, v) -> Context.lctx_add_new_path ~loc lctx' v
            | (Input.TyProcess, v) -> error ~loc (UnknownIdentifier2 v)) (Context.lctx_init) typed_args in

         (* let lctx = Context.lctx_add_frame lctx in  *)
         let (ctx, lctx, c) = process_cmd ctx lctx c in

         (Context.ctx_add_ext_syscall ctx (f, List.map fst typed_args), 
            pol, 
            Context.def_add_ext_syscall def (f, typed_args, c), sys, fst ps)

   | Input.DeclExtAttack(f, t, typed_args, c) ->      
      (if Context.check_used ctx f then error ~loc (AlreadyDefined f) else ());
      (if not (Context.ctx_check_ext_syscall ctx t) then error ~loc (UnknownIdentifier t) else ());
      let args_ty = Context.ctx_get_ext_syscall_arity ~loc ctx t in
      (if List.length typed_args = List.length args_ty then () else error ~loc (ArgNumMismatch (t, List.length typed_args, List.length args_ty)));

      (* parse arguments *)
      let lctx = List.fold_left (fun lctx' ta -> 
         match ta with
         | (Input.TyValue, v) -> Context.lctx_add_new_var ~loc lctx' v
         | (Input.TyChannel, v) -> Context.lctx_add_new_chan ~loc lctx' v
         | (Input.TyPath, v) -> Context.lctx_add_new_path ~loc lctx' v
         | (Input.TyProcess, v) -> error ~loc (UnknownIdentifier2 v)) (Context.lctx_init) typed_args in

         (* let lctx = Context.lctx_add_frame lctx in  *)
      let (ctx, lctx, c) = process_cmd ctx lctx c in

      (Context.ctx_add_ext_attack ctx (f, t, List.map fst typed_args), 
         pol, 
         Context.def_add_ext_attack def (f,t, typed_args, c), sys, fst ps)

   | Input.DeclType (id, c) -> 
      if Context.check_used ctx id then error ~loc (AlreadyDefined id) else (Context.ctx_add_ty ctx (id, c), pol, def, sys, fst ps)
   
   | Input.DeclAccess(s, t, Some al) -> 

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

   | Input.DeclAccess(s, t, None) -> 

      let tys = Context.ctx_get_ty ~loc ctx s in
      let tyt = List.map (Context.ctx_get_ty ~loc ctx) t in 
      let pol = 
         begin match tys, tyt with
         | Input.CProc, [Input.CChan] -> 
            Context.pol_add_access_all pol (s, t)
            
         | Input.CProc, [Input.CFsys] -> 
            Context.pol_add_access_all pol (s, t)
            
         | _, _ -> error ~loc (WrongInputType)
         end in 
       (ctx, pol, def, sys, fst ps)

   | Input.DeclAttack (tl, al) -> 
      let f t a =
         if Context.ctx_check_ty ctx t then
         if Context.ctx_check_ext_attack ctx a then
         (* match Context.ctx_get_ty ~loc ctx t, Context.ctx_get_ext_attack_arity ~loc ctx a with
         | Input.CProc, Input.TyProcess 
         | Input.CChan, Input.TyChannel 
         | Input.CFsys, Input.TyPath -> *)
            (t, a)
         (* | _, _ -> error ~loc (WrongInputType) *)
         else error ~loc (UnknownIdentifier a)
         else error ~loc (UnknownIdentifier t) in
      let p = List.fold_left (fun p t -> 
         List.fold_left (fun p a -> Context.pol_add_attack p (f t a)) p al) pol tl in 
      (ctx, p, def, sys, fst ps)

  | Input.DeclInit (id, e) -> 
      if Context.check_used ctx id then error ~loc (AlreadyDefined id) else 
      let e' = match e with | Some e -> Some (process_expr ctx Context.lctx_init e) | _ -> None in 
      (Context.ctx_add_const ctx id, pol, Context.def_add_const def (id, e'), sys, fst ps)
   
   (* | DeclParamInit of Name.ident * (Name.ident * expr) option *)
   | Input.DeclParamInit (id, e) -> 
      if Context.check_used ctx id then error ~loc (AlreadyDefined id) else 
         let e' = 
            match e with 
            | Some (p, e) -> 
               Some (p, process_expr ~param:p ctx Context.lctx_init e) 
            | _ -> None in 
         (Context.ctx_add_param_const ctx id, pol, Context.def_add_param_const def (id, e'), sys, fst ps)
   
   
   | Input.DeclParamChan (id, ty) -> 
      if Context.check_used ctx id then error ~loc (AlreadyDefined id) else 
         (Context.ctx_add_param_ch ctx (id, ty), pol, def, sys, fst ps)
      
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
   
  | Input.DeclParamProc (pid, p, cargs, ty, fls, cl, fs, m) ->
      begin match Context.ctx_get_ty ~loc ctx ty 
      with | Input.CProc -> () | _ -> error ~loc (WrongInputType) end;
      (if Context.check_used ctx pid then error ~loc (AlreadyDefined pid) else ());
      (* load channel parameters *)
      let lctx = List.fold_left (fun lctx' (b, cid, cty) -> 
      if Context.ctx_check_ty_ch ctx cty 
         then 
            begin if b then 
               Context.lctx_add_new_param_chan ~loc lctx' cid
            else 
               Context.lctx_add_new_chan ~loc lctx' cid
            end 
         else
            error ~loc (UnknownIdentifier cty)
         ) (Context.lctx_add_new_param ~loc Context.lctx_init p) cargs in
      (* load files *)

      let files = List.map (fun (path, ty, data) ->
         match Context.ctx_get_ty ~loc ctx ty with
         | Input.CFsys ->
            (process_expr ctx lctx path, ty, process_expr ctx lctx data)
         | _ -> error ~loc (WrongInputType)
         ) fls in 

      (* load top-level variables *)
      let (lctx, ldef) = List.fold_left (fun (lctx', ldef') (vid, e) -> 
         (Context.lctx_add_new_top_var ~loc lctx' vid, Context.ldef_add_new_var ldef' (vid, process_expr ctx lctx' e))) (lctx, Context.ldef_init) cl in

      (* load functions *)
      let (ctx, lctx, ldef) = List.fold_left (fun (ctx'', lctx'', ldef'') (fid, args, cs) -> 
         if Context.lctx_check_func lctx'' fid then error ~loc (AlreadyDefined fid) else 
         let lctx = List.fold_left (fun lctx' vid -> Context.lctx_add_new_var ~loc lctx' vid) lctx'' args in
         let (ctx', lctx', cs')  = process_cmd ctx'' lctx cs in 
         (ctx', Context.lctx_add_new_func ~loc lctx'' (fid, List.length args), 
               Context.ldef_add_new_func ldef'' (fid, args, cs'))) (ctx, lctx, ldef) fs in

      (* load main function *)
      let (ctx, _, m') = process_cmd ctx lctx m in 

      (Context.ctx_add_proctmpl ctx (Context.mk_ctx_proctmpl (pid, Some p, List.rev cargs, ty, lctx.Context.lctx_top_var, lctx.Context.lctx_func)), pol, 
         Context.def_add_proctmpl def pid files ldef m', sys, fst ps)


   | Input.DeclProc (pid, cargs, ty,  fls,  cl, fs, m) ->
      begin match Context.ctx_get_ty ~loc ctx ty 
      with | Input.CProc -> () | _ -> error ~loc (WrongInputType) end;
      (if Context.check_used ctx pid then error ~loc (AlreadyDefined pid) else ());
      (* load channel parameters *)
      let lctx = List.fold_left (fun lctx' (b, cid, cty) -> 
      if Context.ctx_check_ty_ch ctx cty 
         then 
            begin if b then 
               Context.lctx_add_new_param_chan ~loc lctx' cid
            else 
               Context.lctx_add_new_chan ~loc lctx' cid
            end 
         else
            error ~loc (UnknownIdentifier cty)
         ) Context.lctx_init cargs in
      (* load files *)
      
      let files = List.map (fun (path, ty, data) ->
         match Context.ctx_get_ty ~loc ctx ty with
         | Input.CFsys ->
            (process_expr ctx lctx path, ty, process_expr ctx lctx data)
         | _ -> error ~loc (WrongInputType)
         ) fls in 

      (* load top-level variables *)
      let (lctx, ldef) = List.fold_left (fun (lctx', ldef') (vid, e) -> 
         (Context.lctx_add_new_top_var ~loc lctx' vid, Context.ldef_add_new_var ldef' (vid, process_expr ctx lctx' e))) (lctx, Context.ldef_init) cl in

      (* load functions *)
      let (ctx, lctx, ldef) = List.fold_left (fun (ctx'', lctx'', ldef'') (fid, args, cs) -> 
         if Context.lctx_check_func lctx'' fid then error ~loc (AlreadyDefined fid) else 
         let lctx = List.fold_left (fun lctx' vid -> Context.lctx_add_new_var ~loc lctx' vid) lctx'' args in
         let (ctx', lctx', cs')  = process_cmd ctx'' lctx cs in 
         (ctx', Context.lctx_add_new_func ~loc lctx'' (fid, List.length args), 
               Context.ldef_add_new_func ldef'' (fid, args, cs'))) (ctx, lctx, ldef) fs in

      (* load main function *)
      let (ctx, _, m') = process_cmd ctx lctx m in 

      (Context.ctx_add_proctmpl ctx (Context.mk_ctx_proctmpl (pid, None, List.rev cargs, ty, lctx.Context.lctx_top_var, lctx.Context.lctx_func)), pol, 
         Context.def_add_proctmpl def pid files ldef m', sys, fst ps)

      

   | Input.DeclSys (procs, lemmas) ->
      let processed_procs, processed_param_procs = 
         List.fold_left (fun (pl, parampl) p -> let pl', parampl' = process_proc loc ctx def pol p in
         
         (pl'@pl, match parampl' with [] -> parampl | _ -> parampl'::parampl)) ([], [  ]) procs in
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
      (* Set up PID  *)


      let processed_procs, used_names = List.fold_left (fun (pl, un) p -> 
            {p with Context.proc_pid = 
               List.length (List.filter (fun n -> n = p.Context.proc_name) un)
            }::pl, p.Context.proc_name::un) ([], []) processed_procs in 


      let processed_param_procs, used_names = 
         List.fold_left (fun (pll, un) pl -> 
            let pll', un = List.fold_left (fun (pl, un) p -> 
               {p with Context.proc_pid = 
                  List.length (List.filter (fun n -> n = p.Context.proc_name) un)
               }::pl, p.Context.proc_name::un) ([], []) pl in 
               pll'::pll, un
               ) ([], used_names) processed_param_procs in 


      (ctx, pol, def, {
                        Context.sys_ctx = ctx;
                        Context.sys_pol = pol;
                        Context.sys_def = def;
                        Context.sys_proc=processed_procs;
                        Context.sys_param_proc=processed_param_procs;
                        Context.sys_lemma = processed_lemmas}::sys, fst ps)
      


in process_decl' ctx pol def sys ps c

and load fn ctx pol def sys =
   let decls, parser_state = Lexer.read_file Parser.file fn in 
   let (ctx, pol, def, sys, parser_state) = List.fold_left 
   (fun (ctx, pol, def, sys, parser_state) decl -> process_decl ctx pol def sys (parser_state, fn) decl)  
   (ctx, pol, def, sys, parser_state) decls in (ctx, pol, def, sys, parser_state)

