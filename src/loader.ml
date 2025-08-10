(** Conversion from concrete syntax to abstract syntax.
    Here we also load all required files, which may not be
    optimal but is systematic. *)

(** Conversion errors *)
type error =
  | UnknownVariable of [ `MetaVar ] * string
  | UnknownIdentifier of string * string
  | AlreadyDefined of string
  | ForbiddenIdentifier of string
  | ArgNumMismatch of string * int * int
  | NegativeArity of int
  | WrongInputType
  | NoBindingVariable
  | WrongChannelType of string * string

exception Error of error Location.located

(** [error ~loc err] raises the given runtime error. *)
let error ~loc err = Stdlib.raise (Error (Location.locate ~loc err))

(** Print error description. *)
let print_error err ppf =
  match err with
  | UnknownVariable (`MetaVar, x) -> Format.fprintf ppf "unknown meta variable %s" x
  | UnknownIdentifier (kind, x) -> Format.fprintf ppf "unknown %s %s" kind x
  | AlreadyDefined x -> Format.fprintf ppf "identifier already defined %s" x
  | ForbiddenIdentifier x -> Format.fprintf ppf "forbidden identifier %s" x
  | ArgNumMismatch (x, i, j) ->
      Format.fprintf
        ppf
        "%s arguments provided while %s requires %s"
        (string_of_int i)
        x
        (string_of_int j)
  | NegativeArity k -> Format.fprintf ppf "negative arity is given: %s" (string_of_int k)
  | WrongInputType -> Format.fprintf ppf "wrong input type"
  | NoBindingVariable -> Format.fprintf ppf "no binding variable"
  | WrongChannelType (x, y) -> Format.fprintf ppf "%s type expected but %s given" x y

let find_index f lst =
  let rec aux i = function
    | [] -> None
    | x :: xs -> if f x then Some i else aux (i + 1) xs
  in
  aux 0 lst
;;

let rec process_expr ?(param = "") ctx lctx { Location.data = c; Location.loc } =
  let c =
    match c with
    | Input.Var id ->
        if Context.ctx_check_const ctx id
        then Syntax.Const (id, None)
        else if Context.ctx_check_ext_const ctx id
        then Syntax.ExtConst id
        else if Context.lctx_check_chan lctx id
        then Syntax.Channel (id, None)
        else if Context.lctx_check_param lctx id
        then Syntax.Variable (id, Param)
        else if id = param
        then Syntax.Variable (id, Param)
        else (
          match find_index (fun v -> v = id) lctx.Context.lctx_top_var with
          | Some i -> Syntax.Variable (id, (Top i))
          | None ->
              (match find_index (fun v -> v = id) lctx.Context.lctx_loc_var with
               | Some i -> Syntax.Variable (id, (Loc i))
               | None ->
                   (match find_index (fun v -> v = id) lctx.Context.lctx_meta_var with
                    | Some i -> Syntax.Variable (id, (Meta i))
                    | None -> error ~loc (UnknownIdentifier ("metavar", id)))))
    | Input.Boolean b -> Syntax.Boolean b
    | Input.String s -> Syntax.String s
    | Input.Integer z -> Syntax.Integer z
    | Input.Float f -> Syntax.Float f
    | Input.Apply (o, el) ->
        if Context.ctx_check_ext_syscall ctx o then error ~loc (ForbiddenIdentifier o);
        if not @@ Context.ctx_check_ext_func_and_arity ctx (o, List.length el)
        then error ~loc (UnknownIdentifier ("function", o));
        Syntax.Apply (o, List.map (fun a -> process_expr ~param ctx lctx a) el)
    | Input.Tuple el ->
        Syntax.Tuple (List.map (fun a -> process_expr ~param ctx lctx a) el)
    | Input.Param (pid, p) ->
        (* [Input.Param] is converted NOT to [Syntax.Param]
           but to [Syntax.ParamConst] or [Syntax.Channel {param= Some _}] *)
        if Context.ctx_check_param_const ctx pid
        then Syntax.Const (pid, Some (process_expr ~param ctx lctx p))
        else if Context.lctx_check_param_chan lctx pid
        then Syntax.Channel (pid, Some (process_expr ~param ctx lctx p))
        else error ~loc (UnknownIdentifier ("parameter", pid))
  in
  Location.locate ~loc c
;;

(* This processor is used when processing facts. It deals unfound metavarables a little differently *)
let rec process_expr2 new_meta_vars ctx lctx { Location.data = c; Location.loc } =
  let c =
    match c with
    | Input.Var id ->
        if Context.ctx_check_const ctx id
        then Syntax.Const (id, None)
        else if Context.ctx_check_ext_const ctx id
        then Syntax.ExtConst id
        else if Context.lctx_check_chan lctx id
        then Syntax.Channel (id, None)
        else if Context.lctx_check_param lctx id
        then Syntax.Variable (id, Param)
        else (
          match find_index (fun v -> v = id) lctx.Context.lctx_top_var with
          | Some i -> Syntax.Variable (id, (Top i))
          | None ->
              (match find_index (fun v -> v = id) lctx.Context.lctx_loc_var with
               | Some i -> Syntax.Variable (id, (Loc i))
               | None ->
                   (match find_index (fun v -> v = id) lctx.Context.lctx_meta_var with
                    | Some i -> Syntax.Variable (id, (Meta i))
                    | None ->
                        (match find_index (fun v -> v = id) new_meta_vars with
                         | Some i -> Syntax.Variable (id, (MetaNew i))
                         | None -> error ~loc (UnknownVariable (`MetaVar, id))))))
    | Input.Boolean b -> Syntax.Boolean b
    | Input.String s -> Syntax.String s
    | Input.Integer z -> Syntax.Integer z
    | Input.Float f -> Syntax.Float f
    | Input.Apply (o, el) ->
        if Context.ctx_check_ext_syscall ctx o then error ~loc (ForbiddenIdentifier o);
        if not @@ Context.ctx_check_ext_func_and_arity ctx (o, List.length el)
        then error ~loc (UnknownIdentifier ("function", o));
        Syntax.Apply (o, List.map (fun a -> process_expr2 new_meta_vars ctx lctx a) el)
    | Input.Tuple el ->
        Syntax.Tuple (List.map (fun a -> process_expr2 new_meta_vars ctx lctx a) el)
    | Input.Param (pid, p) ->
        if Context.ctx_check_param_const ctx pid
        then Syntax.Const (pid, Some (process_expr2 new_meta_vars ctx lctx p))
        else if Context.lctx_check_param_chan lctx pid
        then Syntax.Channel (pid, Some (process_expr2 new_meta_vars ctx lctx p))
        else error ~loc (UnknownIdentifier ("parameter", pid))
  in
  Location.locate ~loc c
;;

let process_fact_closed new_meta_vars ctx lctx f =
  let loc = f.Location.loc in
  match f.Location.data with
  | Input.Fact (id, el) ->
      ( Context.ctx_add_or_check_lfact ~loc ctx (id, List.length el)
      , Location.locate
          ~loc:f.Location.loc
          (Syntax.Fact (id, List.map (process_expr2 new_meta_vars ctx lctx) el)) )
  | Input.GlobalFact (id, el) ->
      ( Context.ctx_add_or_check_fact ~loc ctx (id, List.length el)
      , Location.locate
          ~loc:f.Location.loc
          (Syntax.GlobalFact (id, List.map (process_expr2 new_meta_vars ctx lctx) el)) )
  | Input.ChannelFact (l, id, el) ->
      (* check validty of local scope l *)
      ( Context.ctx_add_or_check_lfact ~loc ctx (id, List.length el)
      , Location.locate
          ~loc:f.Location.loc
          (Syntax.ChannelFact
             ( process_expr2 new_meta_vars ctx lctx l
             , id
             , List.map (process_expr2 new_meta_vars ctx lctx) el )) )
  | Input.EqFact (e1, e2) ->
      ( ctx
      , Location.locate
          ~loc:f.Location.loc
          (Syntax.EqFact (process_expr2 new_meta_vars ctx lctx e1,
                          process_expr2 new_meta_vars ctx lctx e2)))
  | Input.NeqFact (e1, e2) ->
      ( ctx
      , Location.locate
          ~loc:f.Location.loc
          (Syntax.NeqFact (process_expr2 new_meta_vars ctx lctx e1,
                          process_expr2 new_meta_vars ctx lctx e2)))
  | Input.FileFact (e1, e2) ->
      ( ctx
      , Location.locate
          ~loc:f.Location.loc
          (Syntax.FileFact (process_expr2 new_meta_vars ctx lctx e1,
                          process_expr2 new_meta_vars ctx lctx e2)))
  | Input.ProcessFact _ -> assert false (* XXX ??? *)
;;

let process_facts_closed new_meta_vars ctx lctx fl =
  List.fold_left
    (fun (ctx, fl) f ->
       let ctx, f = process_fact_closed new_meta_vars ctx lctx f in
       ctx, fl @ [ f ])
    (ctx, [])
    fl
;;

let rec collect_meta_fact new_meta_vars ctx lctx f =
  try
    let ctx, f = process_fact_closed new_meta_vars ctx lctx f in
    (ctx, lctx, f), []
  with
  | Error { Location.data = err; Location.loc = locc } ->
      (match err with
       | UnknownVariable (_k, v) ->
           let r, l = collect_meta_fact (v :: new_meta_vars) ctx lctx f in
           r, l @ [ v ]
       | _ -> error ~loc:locc err)
;;

let collect_meta_facts ctx lctx fl =
  List.fold_left
    (fun ((ctx, lctx, fl), ls) f ->
       let (ctx, lctx, f), l = collect_meta_fact ls ctx lctx f in
       (ctx, lctx, fl @ [ f ]), ls @ l)
    ((ctx, lctx, []), [])
    fl
;;

let process_facts ctx lctx fl =
  let _, new_meta_vars = collect_meta_facts ctx lctx fl in
  (* let lctx = {lctx with Context.lctx_meta_var = vl@lctx.Context.lctx_meta_var} in  *)
  let ctx, fl = process_facts_closed new_meta_vars ctx lctx fl in
  (ctx, lctx, fl), new_meta_vars
;;

let rec process_cmd ctx lctx { Location.data = c; Location.loc } =
  let ctx, lctx, c =
    match c with
    | Input.Skip -> ctx, lctx, Syntax.Skip
    | Input.Sequence (c1, c2) ->
        let ctx, lctx, c1 = process_cmd ctx lctx c1 in
        let ctx, lctx, c2 = process_cmd ctx lctx c2 in
        ctx, lctx, Syntax.Sequence (c1, c2)
    | Input.Put fl ->
        let ctx, fl = process_facts_closed [] ctx lctx fl in
        ctx, lctx, Syntax.Put fl
    | Input.Let (v, e, c) ->
        (match e.Location.data with
         | Input.Apply (o, _args) ->
             let eloc = e.Location.loc in
             if Context.ctx_check_ext_syscall ctx o || Context.lctx_check_func lctx o
             then (
               let ctx, lctx, c =
                 process_cmd
                   ctx
                   lctx
                   (Location.locate
                      ~loc
                      (Input.Let
                         ( v
                         , Location.locate ~loc:eloc (Input.String "")
                         , Location.locate
                             ~loc:eloc
                             (Input.Sequence
                                (Location.locate ~loc:eloc (Input.Assign (Some v, e)), c))
                         )))
               in
               ctx, lctx, c.Location.data)
             else (
               if Context.lctx_check_var lctx v then error ~loc (AlreadyDefined v);
               let lctx' = Context.lctx_add_new_var ~loc lctx v in
               let ctx, _, c = process_cmd ctx lctx' c in
               ctx, lctx, Syntax.Let (v, process_expr ctx lctx e, c))
         | _ ->
             if Context.lctx_check_var lctx v then error ~loc (AlreadyDefined v) else ();
             let lctx' = Context.lctx_add_new_var ~loc lctx v in
             let ctx, _, c = process_cmd ctx lctx' c in
             ctx, lctx, Syntax.Let (v, process_expr ctx lctx e, c))
    | Input.Assign (ov, e) ->
        let ov =
          match ov with
          | Some id ->
              (* Only [Top] and [Loc] variables are mutable *)
              (match find_index (fun v -> v = id) lctx.Context.lctx_top_var with
               | Some i -> Some (id, Syntax.Top i)
               | None ->
                   (match find_index (fun v -> v = id) lctx.Context.lctx_loc_var with
                    | Some i -> Some (id, Loc i)
                    | None -> error ~loc (UnknownIdentifier ("local variable", id))))
              (* [Meta] is not mutable somehow *)
              (* match find_index (fun v -> v = id) lctx.Context.lctx_meta_var with
                 | Some i -> Syntax.MetaVariable (id, i)
                 | None -> error ~loc (UnknownIdentifier id)
              *)
          | None -> None
        in
        (match e.Location.data with
         | Input.Apply (o, args) ->
             if Context.ctx_check_ext_syscall ctx o
             then (*  when o is a system call *)
               (
               let args' = Context.ctx_get_ext_syscall_arity ~loc ctx o in
               if List.length args = List.length args'
               then ()
               else error ~loc (ArgNumMismatch (o, List.length args, List.length args'));
               ( ctx
               , lctx
               , Syntax.SCall
                   ( ov
                   , o
                   , List.map (fun arg -> process_expr ctx lctx arg) args )))
             else if
               (*  when o is a function *)
               Context.lctx_check_func lctx o
             then (
               if List.length args = Context.lctx_get_func_arity lctx o
               then ()
               else
                 error
                   ~loc
                   (ArgNumMismatch
                      (o, List.length args, Context.lctx_get_func_arity lctx o));
               ctx, lctx, Syntax.FCall (ov, o, List.map (process_expr ctx lctx) args))
             else (
               (* when o is a term *)
               match ov with
               | Some v -> ctx, lctx, Syntax.Assign (v, process_expr ctx lctx e)
               | _ -> error ~loc NoBindingVariable)
         | _ ->
             (match ov with
              | Some v -> ctx, lctx, Syntax.Assign (v, process_expr ctx lctx e)
              | _ -> error ~loc NoBindingVariable))
    | Input.Case cs ->
        let ctx, cs =
          List.fold_left
            (fun (ctx, cs) (fl, c) ->
               let (ctx, _lctx', fl), vl = process_facts ctx lctx fl in
               let ctx, _, c =
                 process_cmd
                   ctx
                   { lctx with Context.lctx_meta_var = vl @ lctx.Context.lctx_meta_var }
                   c
               in
               ctx, cs @ [ vl, fl, c ])
            (ctx, [])
            cs
        in
        ctx, lctx, Syntax.Case cs
    | Input.While (cs1, cs2) ->
        let ctx, cs1 =
          List.fold_left
            (fun (ctx, cs) (fl, c) ->
               let (ctx, _lctx', fl), vl = process_facts ctx lctx fl in
               let ctx, _, c =
                 process_cmd
                   ctx
                   { lctx with Context.lctx_meta_var = vl @ lctx.Context.lctx_meta_var }
                   c
               in
               ctx, cs @ [ vl, fl, c ])
            (ctx, [])
            cs1
        in
        let ctx, cs2 =
          List.fold_left
            (fun (ctx, cs) (fl, c) ->
               let (ctx, _lctx', fl), vl = process_facts ctx lctx fl in
               let ctx, _, c =
                 process_cmd
                   ctx
                   { lctx with Context.lctx_meta_var = vl @ lctx.Context.lctx_meta_var }
                   c
               in
               ctx, cs @ [ vl, fl, c ])
            (ctx, [])
            cs2
        in
        ctx, lctx, Syntax.While (cs1, cs2)
    | Input.Event fl ->
        let ctx, fl = process_facts_closed [] ctx lctx fl in
        ctx, lctx, Syntax.Event fl
    | Input.Return e -> ctx, lctx, Syntax.Return (process_expr ctx lctx e)
    | Input.New (v, fid_el_opt, c) ->
        (* [new x := S(e1,..,en) in c] *)
        if Context.lctx_check_var lctx v then error ~loc (AlreadyDefined v) else ();
        let ctx =
          let fid, el = Option.value fid_el_opt ~default:("",[]) in
          Context.ctx_add_or_check_inj_fact ~loc ctx (fid, List.length el)
        in
        (* (if Context.ctx_check_inj_fact ctx fid then error ~loc (AlreadyDefined v) else ()); *)
        let lctx' = Context.lctx_add_new_meta ~loc lctx v in
        let ctx, _, c = process_cmd ctx lctx' c in
        ctx, lctx, Syntax.New (v, Option.map (fun (fid, el) -> fid, List.map (process_expr ctx lctx) el) fid_el_opt, c)
    | Input.Get (vl, id, fid, c) ->
        (* [let x1,...,xn := e.S in c] *)
        if not (Context.ctx_check_inj_fact ctx fid)
        then error ~loc (UnknownIdentifier ("structure fact", fid));
        (let i = Context.ctx_get_inj_fact_arity ~loc ctx fid in
         let j = List.length vl in
         if not (i = j) then error ~loc (ArgNumMismatch (fid, i, j)) else ());
        let lctx' =
          List.fold_left
            (fun lctx' v ->
               if Context.lctx_check_var lctx v then error ~loc (AlreadyDefined v) else ();
               Context.lctx_add_new_meta ~loc lctx' v)
            lctx
            (List.rev vl)
        in
        let ctx, _, c = process_cmd ctx lctx' c in
        ctx, lctx, Syntax.Get (vl, process_expr ctx lctx id, fid, c)
    | Input.Del (id, fid) ->
        if not (Context.ctx_check_inj_fact ctx fid)
        then error ~loc (UnknownIdentifier ("structure fact", fid));
        ctx, lctx, Syntax.Del (process_expr ctx lctx id, fid)
  in
  ctx, lctx, Location.locate ~loc c
;;

type env =
  { context : Context.context
  ; access_policy : Context.access_policy
  ; definition : Context.definition
  ; system : Context.system list
  ; used_idents : string list
  ; used_strings : string list
  }

let process_init =
  { context = Context.ctx_init
  ; access_policy = Context.pol_init
  ; definition = Context.def_init
  ; system = []
  ; used_idents = []
  ; used_strings = []
  }
;;

let process_pproc ?(param = "") loc ctx def _pol (proc : Input.pproc) =
  let pid, files, vl, fl, m, cargs, chans, ptype =
    match proc.Location.data with
    | Input.ParamProc (pid, param', chans) ->
        (* pid<param'>(chan,..,chan) *)
        if not (Context.ctx_check_proctmpl ctx pid)
        then error ~loc (UnknownIdentifier ("process", pid));
        let Context.
              { ctx_proctmpl_param = param''
              ; ctx_proctmpl_ch = cargs
              ; ctx_proctmpl_ty = ptype
              ; _
              }
          =
          Context.ctx_get_proctmpl ctx pid
        in
        (match param'' with
         | Some _ -> ()
         | None ->
             (* XXX another error required *)
             error ~loc (UnknownIdentifier ("parameter", "")));
        let cargs = List.rev cargs in
        let Context.
              { def_proctmpl_files = files
              ; def_proctmpl_var = vl
              ; def_proctmpl_func = fl
              ; def_proctmpl_main = m
              ; _
              }
          =
          Context.def_get_proctmpl def pid
        in
        let realparam = process_expr ~param ctx Context.lctx_init param' in
        let files =
          List.map
            (fun (p, ty, e) ->
               Substitute.expr_param p realparam, ty, Substitute.expr_param e realparam)
            files
        in
        let vl = List.map (fun (v, e) -> v, Substitute.expr_param e realparam) vl in
        let fl =
          List.map (fun (fn, args, c) -> fn, args, Substitute.cmd_param c realparam) fl
        in
        let m = Substitute.cmd_param m realparam in
        pid, files, vl, fl, m, cargs, chans, ptype
    | Input.Proc (pid, chans) ->
        (* pid(chan,..,chan) *)
        (* XXX Dupe with ParamProc *)
        if not (Context.ctx_check_proctmpl ctx pid)
        then error ~loc (UnknownIdentifier ("process", pid));
        let Context.
              { ctx_proctmpl_param = param'
              ; ctx_proctmpl_ch = cargs
              ; ctx_proctmpl_ty = ptype
              ; _
              }
          =
          Context.ctx_get_proctmpl ctx pid
        in
        (match param' with
         | Some _ ->
             (* XXX another error required *)
             error ~loc (UnknownIdentifier ("parameter", ""))
         | None -> ());
        let cargs = List.rev cargs in
        let Context.
              { def_proctmpl_files = files
              ; def_proctmpl_var = vl
              ; def_proctmpl_func = fl
              ; def_proctmpl_main = m
              ; _
              }
          =
          Context.def_get_proctmpl def pid
        in
        pid, files, vl, fl, m, cargs, chans, ptype
  in
  (* substitute channels *)
  if List.length cargs != List.length chans
  then error ~loc (ArgNumMismatch (pid, List.length chans, List.length cargs));
  let files, vl, fl, m, installed_channels =
    List.fold_left2
      (fun (files, vl, fl, m, installed_channels) (Syntax.ChanParam {id=ch_f; param=is_param; typ=ty_f}) ch_t ->
         let is_param = is_param <> None in
         match ch_t with
         | Input.ChanArgPlain ch_t ->
             if is_param then error ~loc (WrongChannelType ("", ""));
             if not (Context.ctx_check_ch ctx ch_t)
             then error ~loc (UnknownIdentifier ("channel type", ch_t));
             let _, chan_ty = List.find (fun (s, _) -> s = ch_t) ctx.Context.ctx_ch in
             if chan_ty <> ty_f
             then error ~loc (WrongChannelType (ch_f ^ ":" ^ ty_f, ch_t ^ ":" ^ chan_ty));
             (* replace channel variables and check access policies! *)
             let new_chan =
               Location.locate ~loc:Location.Nowhere (Syntax.Channel (ch_t, None))
             in
             ( List.map
                 (fun (p, ty, e) ->
                    ( Substitute.expr_chan_sub p ch_f new_chan
                    , ty
                    , Substitute.expr_chan_sub e ch_f new_chan ))
                 files
             , List.map (fun (v, e) -> v, Substitute.expr_chan_sub e ch_f new_chan) vl
             , List.map
                 (fun (fn, args, c) -> fn, args, Substitute.cmd_chan_sub c ch_f new_chan)
                 fl
             , Substitute.cmd_chan_sub m ch_f new_chan
             , Syntax.ChanArg { id= ch_t; typ= ty_f; param= None } :: installed_channels )
         | Input.ChanArgParam ch_t ->
             if not is_param then error ~loc (WrongChannelType ("", ""));
             if not (Context.ctx_check_param_ch ctx ch_t)
             then error ~loc (UnknownIdentifier ("channel type", ch_t));
             (* *)
             let _, chan_ty =
               List.find (fun (s, _) -> s = ch_t) ctx.Context.ctx_param_ch
             in
             if chan_ty <> ty_f
             then error ~loc (WrongChannelType (ch_f ^ ":" ^ ty_f, ch_t ^ ":" ^ chan_ty));
             (* replace channel variables and check access policies! *)
             ( List.map
                 (fun (p, ty, e) ->
                    ( Substitute.expr_param_chan_sub p ch_f ch_t
                    , ty
                    , Substitute.expr_param_chan_sub e ch_f ch_t ))
                 files
             , List.map (fun (v, e) -> v, Substitute.expr_param_chan_sub e ch_f ch_t) vl
             , List.map
                 (fun (fn, args, c) ->
                    fn, args, Substitute.cmd_param_chan_sub c ch_f ch_t)
                 fl
             , Substitute.cmd_param_chan_sub m ch_f ch_t
             , Syntax.ChanArg { id= ch_t; typ= ty_f; param= Some None } :: installed_channels )
         | Input.ChanArgParamInst (cid, e) ->
             if is_param then error ~loc (WrongChannelType ("", ""));
             if not (Context.ctx_check_param_ch ctx cid)
             then error ~loc (UnknownIdentifier ("channel type", cid));
             let _, chan_ty =
               List.find (fun (s, _) -> s = cid) ctx.Context.ctx_param_ch
             in
             if chan_ty <> ty_f
             then error ~loc (WrongChannelType (ch_f ^ ":" ^ ty_f, cid ^ ":" ^ chan_ty));
             (* replace channel variables and check access policies! *)
             let e = process_expr ~param ctx Context.lctx_init e in
             let new_chan =
               Location.locate ~loc:Location.Nowhere (Syntax.Channel (cid, Some e))
             in
             ( List.map
                 (fun (p, ty, e) ->
                    ( Substitute.expr_chan_sub p ch_f new_chan
                    , ty
                    , Substitute.expr_chan_sub e ch_f new_chan ))
                 files
             , List.map (fun (v, e) -> v, Substitute.expr_chan_sub e ch_f new_chan) vl
             , List.map
                 (fun (fn, args, c) -> fn, args, Substitute.cmd_chan_sub c ch_f new_chan)
                 fl
             , Substitute.cmd_chan_sub m ch_f new_chan
             , Syntax.ChanArg {id= cid; param= Some (Some e); typ=  ty_f} :: installed_channels ))
      (files, vl, fl, m, [])
      cargs
      chans
  in
  { Context.proc_pid = 0
  ; Context.proc_type = ptype
  ; Context.proc_filesys = files
  ; Context.proc_name = pid
  ; Context.proc_variable = vl
  ; Context.proc_function = fl
  ; Context.proc_main = m
  ; Context.proc_channels = installed_channels
  }
;;

let process_proc loc ctx def pol (proc : Input.proc) =
  match proc with
  | Input.UnboundedProc p -> Either.Left (process_pproc loc ctx def pol p)
  | Input.BoundedProc (pname, pl) ->
      let pl = List.map (process_pproc ~param:pname loc ctx def pol) pl in
      Either.Right pl
;;

(* parse arguments and build a local context *)
let local_context_of_arguments ~loc args =
  List.fold_left (fun lctx v ->
      Context.lctx_add_new_var ~loc lctx v)
    Context.lctx_init
    args
;;

let rec process_decl env fn ({ Location.data = c; Location.loc } : Input.decl) =
  match c with
  | Input.DeclLoad fn' ->
      (* [load "xxx.rab"] *)
      let fn' = Filename.dirname fn ^ "/" ^ fn' in
      load fn' env
  | Input.DeclExtFun (f, arity) ->
      (* [function f:2] *)
      if Context.check_used env.context f then error ~loc (AlreadyDefined f);
      let ctx' =
        if arity < 0 then error ~loc (NegativeArity arity);
        if arity = 0
        then Context.ctx_add_ext_const env.context f
        else Context.ctx_add_ext_func env.context (f, arity)
      in
      { env with context = ctx' }
  | Input.DeclExtEq (e1, e2) ->
      (* [equation e1 = e2] *)
      let rec collect_vars e lctx =
        try
          let e = process_expr env.context lctx e in
          e, lctx
        with
        | Error { Location.data = err; Location.loc = locc } ->
            (match err with
             | UnknownIdentifier (_k, id) ->
                 collect_vars e (Context.lctx_add_new_var ~loc lctx id)
             | _ -> error ~loc:locc err)
      in
      (* is this really correct??? check with x = y next time!! *)
      let e1', lctx = collect_vars e1 Context.lctx_init in
      let e2', lctx = collect_vars e2 lctx in
      { env with
        definition =
          Context.def_add_ext_eq env.definition (lctx.Context.lctx_loc_var, e1', e2')
      }
  | Input.DeclExtSyscall (f, args, c, _attack) ->
      (* [syscall f(a1,..,an) { c }] or [passive attack f(a1,..,an) { c }] *)
      if Context.check_used env.context f then error ~loc (AlreadyDefined f);
      let lctx = local_context_of_arguments ~loc args in
      let ctx, _lctx, c = process_cmd env.context lctx c in
      { env with
        context = Context.ctx_add_ext_syscall ctx (f, args)
      ; definition = Context.def_add_ext_syscall env.definition (f, args, c)
      }
  | Input.DeclExtAttack (f, t, args, c) ->
      (* [attack f on name (typ x,..) { c }] *)
      if Context.check_used env.context f then error ~loc (AlreadyDefined f);
      (* [t] must be a syscall *)
      if not (Context.ctx_check_ext_syscall env.context t)
      then error ~loc (UnknownIdentifier ("system call", t));
      let args' = Context.ctx_get_ext_syscall_arity ~loc env.context t in
      if List.length args <> List.length args'
      then error ~loc (ArgNumMismatch (t, List.length args, List.length args'));
      let lctx = local_context_of_arguments ~loc args in
      let ctx, _lctx, c = process_cmd env.context lctx c in
      { env with
        context = Context.ctx_add_ext_attack ctx (f, t, args)
      ; definition = Context.def_add_ext_attack env.definition (f, t, args, c)
      }
  | Input.DeclType (id, tc) ->
      (* [type t : tyclass] *)
      if Context.check_used env.context id then error ~loc (AlreadyDefined id);
      { env with context = Context.ctx_add_ty env.context (id, tc) }
  | Input.DeclAccess (s, tys, Some syscalls) ->
      (* [allow s t1 .. tn [f1, .., fm]] *)
      let tc = Context.ctx_get_ty ~loc env.context s in
      let tycs = List.map (Context.ctx_get_ty ~loc env.context) tys in
      let f pol syscall =
        if not @@ Context.ctx_check_ext_syscall env.context syscall
        then error ~loc (UnknownIdentifier ("system call", syscall));
        (match tc, tycs with
         | Input.CProc, [ Input.CChan ] | Input.CProc, [ Input.CFsys ] | Input.CProc, []
           -> ()
         | _ -> error ~loc WrongInputType);
        Context.pol_add_access pol (s, tys, syscall)
      in
      { env with access_policy = List.fold_left f env.access_policy syscalls }
  | Input.DeclAccess (s, tys, None) ->
      (* [allow s t1 .. tn [.]] *)
      let tc = Context.ctx_get_ty ~loc env.context s in
      let tycs = List.map (Context.ctx_get_ty ~loc env.context) tys in
      (match tc, tycs with
       | Input.CProc, [ Input.CChan ] | Input.CProc, [ Input.CFsys ] -> ()
       | _ -> error ~loc WrongInputType);
      let pol = Context.pol_add_access_all env.access_policy (s, tys) in
      { env with access_policy = pol }
  | Input.DeclAttack (tl, al) ->
      (* [allow attack t1 .. tn [f1, .., fm]] *)
      List.iter
        (fun t ->
           if not @@ Context.ctx_check_ty env.context t
           then error ~loc (UnknownIdentifier ("type", t)))
        tl;
      List.iter
        (fun a ->
           if not @@ Context.ctx_check_ext_attack env.context a
           then error ~loc (UnknownIdentifier ("attack", a)))
        al;
      let p =
        List.fold_left
          (fun p t -> List.fold_left (fun p a -> Context.pol_add_attack p (t, a)) p al)
          env.access_policy
          tl
      in
      { env with access_policy = p }
  | Input.DeclInit (id, Fresh) ->
      (* [const fresh n] *)
      if Context.check_used env.context id then error ~loc (AlreadyDefined id);
      { env with
        context = Context.ctx_add_const env.context id
      ; definition = Context.def_add_const env.definition (id, None)
      }
  | Input.DeclInit (id, Value e) ->
      (* [const n = e] *)
      if Context.check_used env.context id then error ~loc (AlreadyDefined id);
      let e' = process_expr env.context Context.lctx_init e in
      { env with
        context = Context.ctx_add_const env.context id
      ; definition = Context.def_add_const env.definition (id, Some e')
      }
  | Input.DeclInit (id, Fresh_with_param) ->
      (* [const fresh n<>] *)
      if Context.check_used env.context id then error ~loc (AlreadyDefined id);
      { env with
        context = Context.ctx_add_param_const env.context id
      ; definition = Context.def_add_param_const env.definition (id, None)
      }
  | Input.DeclInit (id, Value_with_param (e, p)) ->
      (* [const n<p> = e] *)
      if Context.check_used env.context id then error ~loc (AlreadyDefined id);
      let e' = process_expr ~param:p env.context Context.lctx_init e in
      { env with
        context = Context.ctx_add_param_const env.context id
      ; definition = Context.def_add_param_const env.definition (id, Some (p, e'))
      }
  | Input.DeclChan (ChanParam {id; typ= ty; param= Some ()}) ->
      (* [channel n<> : ty] *)
      if Context.check_used env.context id then error ~loc (AlreadyDefined id);
      { env with context = Context.ctx_add_param_ch env.context (id, ty) }
  | Input.DeclChan (ChanParam {id; typ= ty; param= None}) ->
      (* [channel n : ty] *)
      if Context.check_used env.context id then error ~loc (AlreadyDefined id);
      (* xxx No need to check [c] ? *)
      { env with context = Context.ctx_add_ch env.context (id, ty) }
  | Input.DeclProc
      { id = pid
      ; param = Some p
      ; args = chanargs
      ; typ = ty
      ; files = fls
      ; vars
      ; funcs = fs
      ; main = m
      } ->
      (* [process id<p>(ch1 : ty1, .., chn : tyn) : ty { file ... var ... function ... main ... }] *)
      let ctx = env.context in
      if Context.check_used ctx pid then error ~loc (AlreadyDefined pid);
      if Context.ctx_get_ty ~loc ctx ty <> Input.CProc then error ~loc WrongInputType;
      (* load channel parameters [p] and [chanargs] *)
      let lctx =
        List.fold_left
          (fun lctx' (Input.ChanParam {id=cid; param; typ= cty}) ->
             if not @@ Context.ctx_check_ty_ch ctx cty
             then error ~loc (UnknownIdentifier ("channel type", cty));
             if param <> None
             then Context.lctx_add_new_param_chan ~loc lctx' cid
             else Context.lctx_add_new_chan ~loc lctx' cid)
          (Context.lctx_add_new_param ~loc Context.lctx_init p)
          chanargs
      in
      (* load files [file ...] *)
      let files =
        List.map
          (fun (path, ty, data) ->
             if Context.ctx_get_ty ~loc ctx ty <> Input.CFsys
             then error ~loc WrongInputType;
             process_expr ctx lctx path, ty, process_expr ctx lctx data)
          fls
      in
      (* load top-level variables [var ...] *)
      let lctx, ldef =
        List.fold_left
          (fun (lctx', ldef') (vid, e) ->
             ( Context.lctx_add_new_top_var ~loc lctx' vid
             , Context.ldef_add_new_var ldef' (vid, process_expr ctx lctx' e) ))
          (lctx, Context.ldef_init)
          vars
      in
      (* load functions *)
      let ctx, lctx, ldef =
        List.fold_left
          (fun (ctx'', lctx'', ldef'') (fid, args, cs) ->
             if Context.lctx_check_func lctx'' fid then error ~loc (AlreadyDefined fid);
             let lctx =
               List.fold_left
                 (fun lctx' vid -> Context.lctx_add_new_var ~loc lctx' vid)
                 lctx''
                 args
             in
             let ctx', _lctx', cs' = process_cmd ctx'' lctx cs in
             ( ctx'
             , Context.lctx_add_new_func ~loc lctx'' (fid, List.length args)
             , Context.ldef_add_new_func ldef'' (fid, args, cs') ))
          (ctx, lctx, ldef)
          fs
      in
      (* load main function [main ...] *)
      let ctx, _, m' = process_cmd ctx lctx m in
      { env with
        context =
          Context.ctx_add_proctmpl
            ctx
            Context.
              { ctx_proctmpl_id = pid
              ; ctx_proctmpl_param = Some p
              ; ctx_proctmpl_ch = List.rev chanargs
              ; ctx_proctmpl_ty = ty
              ; ctx_proctmpl_var = lctx.Context.lctx_top_var
              ; ctx_proctmpl_func = lctx.Context.lctx_func
              }
      ; definition = Context.def_add_proctmpl env.definition pid files ldef m'
      }
  | Input.DeclProc
      { id = pid
      ; param = None
      ; args = chanargs
      ; typ = ty
      ; files = fls
      ; vars = cl
      ; funcs = fs
      ; main = m
      } ->
      (* [process id(x1 : ty1, .., xn : tyn) : ty { file ...  var ... function ... main ... }] *)
      let ctx = env.context in
      if Context.check_used ctx pid then error ~loc (AlreadyDefined pid);
      if Context.ctx_get_ty ~loc ctx ty <> Input.CProc then error ~loc WrongInputType;
      (* load channel parameters *)
      let lctx =
        List.fold_left
          (fun lctx' (Syntax.ChanParam {id=cid; param=p; typ= cty}) ->
             if not @@ Context.ctx_check_ty_ch ctx cty
             then error ~loc (UnknownIdentifier ("channel type", cty));
             if p <> None
             then Context.lctx_add_new_param_chan ~loc lctx' cid
             else Context.lctx_add_new_chan ~loc lctx' cid)
          Context.lctx_init
          chanargs
      in
      (* load files [file ...] *)
      let files =
        List.map
          (fun (path, ty, data) ->
             if Context.ctx_get_ty ~loc ctx ty <> Input.CFsys
             then error ~loc WrongInputType;
             process_expr ctx lctx path, ty, process_expr ctx lctx data)
          fls
      in
      (* load top-level variables [var ...] *)
      let lctx, ldef =
        List.fold_left
          (fun (lctx', ldef') (vid, e) ->
             ( Context.lctx_add_new_top_var ~loc lctx' vid
             , Context.ldef_add_new_var ldef' (vid, process_expr ctx lctx' e) ))
          (lctx, Context.ldef_init)
          cl
      in
      (* load functions [function ...] *)
      let ctx, lctx, ldef =
        List.fold_left
          (fun (ctx'', lctx'', ldef'') (fid, args, cs) ->
             if Context.lctx_check_func lctx'' fid then error ~loc (AlreadyDefined fid);
             let lctx =
               List.fold_left
                 (fun lctx' vid -> Context.lctx_add_new_var ~loc lctx' vid)
                 lctx''
                 args
             in
             let ctx', _lctx', cs' = process_cmd ctx'' lctx cs in
             ( ctx'
             , Context.lctx_add_new_func ~loc lctx'' (fid, List.length args)
             , Context.ldef_add_new_func ldef'' (fid, args, cs') ))
          (ctx, lctx, ldef)
          fs
      in
      (* load main function [main ...] *)
      let ctx, _, m' = process_cmd ctx lctx m in
      { env with
        context =
          Context.ctx_add_proctmpl
            ctx
            Context.
              { ctx_proctmpl_id = pid
              ; ctx_proctmpl_param = None
              ; ctx_proctmpl_ch = List.rev chanargs
              ; ctx_proctmpl_ty = ty
              ; ctx_proctmpl_var = lctx.Context.lctx_top_var
              ; ctx_proctmpl_func = lctx.Context.lctx_func
              }
      ; definition = Context.def_add_proctmpl env.definition pid files ldef m'
      }
  | Input.DeclSys (procs, lemmas) ->
      (* [system proc1|..|procn requires [lemma X : ...; ..; lemma Y : ...]] *)
      let processed_procs, processed_param_procs =
        List.fold_left
          (fun (pl, parampl) p ->
             match process_proc loc env.context env.definition env.access_policy p with
             | Either.Left pl' -> pl' :: pl, parampl
             | Either.Right parampl' -> pl, parampl' :: parampl)
          ([], [])
          procs
      in
      (* for now, have plain text for lemmas *)
      let processed_lemmas =
        List.map
          (fun l ->
             (* XXX Location.map? *)
             let tmp =
               match l.Location.data with
               | Input.Lemma (l, p) ->
                   (* unused
                      let rec collect_vars e lctx =
                      try let e = process_expr ctx lctx e in (e, lctx)
                      with
                      | Error {Location.data=err; Location.loc=locc} ->
                         begin match err with
                         | UnknownIdentifier id -> collect_vars e (Context.lctx_add_new_var ~loc lctx id)
                         | _ -> error ~loc:locc err
                         end
                      in
                   *)
                   (match p.Location.data with
                    | Input.PlainString s -> Syntax.PlainLemma { name=l; desc= s }
                    | Input.Reachability evs ->
                        let (_, _, fl), vl =
                          process_facts env.context Context.lctx_init evs
                        in
                        (* XXX 3rd and 4th are always empty *)
                        Syntax.ReachabilityLemma { name= l; fresh_variables= vl; facts= fl }
                    | Input.Correspondence (a, b) ->
                        (match process_facts env.context Context.lctx_init [ a; b ] with
                         | (_, _, [ a; b ]), vl -> Syntax.CorrespondenceLemma { name= l; fresh_variables= vl; premise= a; conclusion= b }
                         | _ -> assert false))
             in
             Location.locate ~loc:l.Location.loc tmp)
          lemmas
      in
      (* Set up PID  *)
      let processed_procs, used_names =
        List.fold_left
          (fun (pl, un) p ->
             ( { p with
                 Context.proc_pid =
                   List.length (List.filter (fun n -> n = p.Context.proc_name) un)
               }
               :: pl
             , p.Context.proc_name :: un ))
          ([], [])
          processed_procs
      in
      let processed_param_procs, _used_names =
        List.fold_left
          (fun (pll, _un) pl ->
             let pll', un =
               List.fold_left
                 (fun (pl, un) p ->
                    ( { p with
                        Context.proc_pid =
                          List.length (List.filter (fun n -> n = p.Context.proc_name) un)
                      }
                      :: pl
                    , p.Context.proc_name :: un ))
                 ([], [])
                 pl
             in
             pll' :: pll, un)
          ([], used_names)
          processed_param_procs
      in
      { env with
        system =
          { Context.sys_ctx = env.context
          ; Context.sys_pol = env.access_policy
          ; Context.sys_def = env.definition
          ; Context.sys_proc = processed_procs
          ; Context.sys_param_proc = processed_param_procs
          ; Context.sys_lemma = processed_lemmas
          }
          :: env.system
      }

and load fn env =
  let decls, (used_idents, used_strings) = Lexer.read_file Parser.file fn in
  let env =
    { env with
      used_idents = used_idents @ env.used_idents
    ; used_strings = used_strings @ env.used_strings
    }
  in
  List.fold_left (fun env decl -> process_decl env fn decl) env decls
;;
