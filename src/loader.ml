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

(** A desugaring context is a list of known identifiers, which is used
    to compute de Bruijn indices. *)

let find_index f l =
   let j = snd (List.fold_right (fun a (i, j) -> let j = if f a && j < 0 then i else j in (i+1, j)) l (0,-1) ) in 
   if j < 0 then None else Some (List.length l - 1 - j)

type context = {
   ctx_ext_const  : (Name.ident) list ; 
   ctx_ext_func   : (Name.ident * int) list ; 
   ctx_ext_ins    : (Name.ident * int) list ; 
   ctx_ty         : (Name.ident * Input.type_class) list ;
   ctx_const      : Name.ident list ;
   ctx_fsys       : (Name.ident * Name.ident * Name.ident) list ; (*fsys name, fsys path, type *)
   ctx_chan       : (Name.ident * Input.chan_class * Name.ident) list ;
   ctx_proc       : (Name.ident * (Name.ident list) * Name.ident * Name.ident list * (Name.ident * int) list) list;
   ctx_event      : (Name.ident * int) list }


let ctx_check_ext_func ctx o = 
   List.exists (fun (s, _) -> s = o) ctx.ctx_ext_func
let ctx_check_ext_func_and_arity ctx o = 
   List.exists (fun s -> s = o) ctx.ctx_ext_func
let ctx_check_ext_const ctx o = 
   List.exists (fun s -> s = o) ctx.ctx_ext_const
let ctx_check_ty ctx o = 
   List.exists (fun (s, _) -> s = o) ctx.ctx_ty
let ctx_check_const ctx o = 
   List.exists (fun s -> s = o) ctx.ctx_const
let ctx_check_fsys ctx o = 
   List.exists (fun (s, _, _) -> s = o) ctx.ctx_fsys
let ctx_check_chan ctx o = 
   List.exists (fun (s, _, _) -> s = o) ctx.ctx_chan
let ctx_check_proc ctx o = 
   List.exists (fun (s, _, _, _, _) -> s = o) ctx.ctx_proc
let ctx_check_event ctx eid = 
   List.exists (fun (s, _) -> s = eid) ctx.ctx_event
let ctx_check_ext_ins ctx eid = 
   List.exists (fun (s, _) -> s = eid) ctx.ctx_ext_ins

let ctx_get_event_arity ~loc ctx eid =
   if ctx_check_event ctx eid then 
   let (_, k) = List.find (fun (s, _) -> s = eid) ctx.ctx_event in k
   else error ~loc (UnknownIdentifier eid)
let ctx_get_ext_ins_arity ~loc ctx eid =
   if ctx_check_ext_ins ctx eid then 
   let (_, k) = List.find (fun (s, _) -> s = eid) ctx.ctx_ext_ins in k
   else error ~loc (UnknownIdentifier eid)
let ctx_get_proc ctx o = 
   List.find (fun (s, _, _, _, _) -> s = o) ctx.ctx_proc

let ctx_add_ext_func ctx (f, k) = {ctx with ctx_ext_func=(f, k)::ctx.ctx_ext_func}
let ctx_add_ext_const ctx c = {ctx with ctx_ext_const=c::ctx.ctx_ext_const}
let ctx_add_ty ctx (id, c) = {ctx with ctx_ty=(id, c)::ctx.ctx_ty}
let ctx_add_const ctx id = {ctx with ctx_const=id::ctx.ctx_const}
let ctx_add_fsys ctx (a, p, ty) = {ctx with ctx_fsys=(a, p, ty)::ctx.ctx_fsys}
let ctx_add_chan ctx (c, t, ty) = {ctx with ctx_chan=(c, t, ty)::ctx.ctx_chan}
let ctx_add_proc ctx p = {ctx with ctx_proc=p::ctx.ctx_proc}
let ctx_add_event ctx (eid, k) = 
   {ctx with ctx_event=(eid,k)::ctx.ctx_event}      
let ctx_add_ext_ins ctx (eid, k) = 
   {ctx with ctx_ext_ins=(eid,k)::ctx.ctx_ext_ins}      


let check_fresh ctx s =
   if ctx_check_ext_func ctx s || 
      ctx_check_ext_const ctx s || 
      ctx_check_ty ctx s || 
      ctx_check_const ctx s || 
      ctx_check_fsys ctx s ||
      ctx_check_chan ctx s || 
      ctx_check_proc ctx s || 
      ctx_check_ext_ins ctx s then false else true 

let check_used ctx s =  
   if (check_fresh ctx s) then false else true


type definition = {
   def_ext_eq : (Name.ident list * Syntax.expr * Syntax.expr) list ;
   def_ext_ins :(Name.ident * (* instruction name *)
                     Name.ident list * (* free variables *)
                     Name.ident list * (* fresh variables *)
                     Syntax.expr list * (* inputs *)
                     Syntax.event list * (* preconditions *)
                     Syntax.event list * (* return *)
                     Syntax.event list) list ;(* postconditions *)
   def_const : (Name.ident * Syntax.expr) list ;
   def_fsys : (Name.ident * Name.ident * Syntax.expr) list (*fsys name, fsys path, data *) ;
   def_proc : (Name.ident * (Name.ident * Syntax.expr) list * (* variablse *)
                        (Name.ident * (Name.ident list) * Syntax.stmt list * Syntax.indexed_var) list * (* member functions *)
                        Syntax.stmt list) list (* main fun *)
}

let def_add_ext_eq def x = {def with def_ext_eq=x::def.def_ext_eq}
let def_add_const def x = {def with def_const=x::def.def_const}
let def_add_fsys def x = {def with def_fsys=x::def.def_fsys}

let def_get_proc def pid = 
   List.find (fun (s, _, _, _) -> s = pid) def.def_proc

let def_get_const def id = 
   List.find (fun (s, _) -> s = id) def.def_const

type access_policy = {
   pol_access : (Name.ident * Name.ident * Input.access_class) list ;
   pol_attack : (Name.ident * Input.attack_class) list 
}

let pol_add_access pol x = {pol with pol_access=x::pol.pol_access}
let pol_add_attack pol x = {pol with pol_attack=x::pol.pol_attack}

type system = {
   sys_proc : (int * (* process id *) Name.ident * (* name of the process template *)
               Input.attack_class list  * (* main function *)
               (Name.ident * Input.chan_class * Input.access_class list * Input.attack_class list) list * (* connected channels: name, channel class, accesses, and attacks *)
               (Name.ident * Syntax.expr * Input.access_class * Input.attack_class list) list * (* paths in the file system, its initial value, access, and attacks *)
               (Name.ident * Syntax.expr) list * (* process's internal variables and their initial values *)
               (Name.ident * Name.ident list * Syntax.stmt list * Syntax.indexed_var ) list * (* process's internal variables and their initial values *)
               Syntax.stmt list 
             ) list 
   (* ;  *)
   (* sys_requirements : Syntax.prop *)
}

(** Initial context *)
let ctx_init = {ctx_ext_func = [] ; ctx_ext_const = [] ; ctx_ext_ins = []; ctx_ty = [] ; ctx_const = [] ; ctx_fsys = [] ; ctx_chan = [] ; ctx_proc = [] ; ctx_event = []}
let def_init = {def_ext_eq = [] ; def_const = [] ; def_ext_ins = [] ; def_fsys=[] ; def_proc = []}
let pol_init = {pol_access = [] ; pol_attack = []}
let sys_init = {sys_proc=[]}


type local_context = {lctx_chan : Name.ident list ; lctx_var : (Name.ident list) list ; lctx_func : (Name.ident * int) list }

let lctx_init = {lctx_chan = []; lctx_var = [ [] ]; lctx_func = []}

type local_definition ={ldef_var : (Name.ident * Syntax.expr) list ; ldef_func : (Name.ident * (Name.ident list) * Syntax.stmt list * Syntax.indexed_var) list }

let ldef_init = {ldef_var=[]; ldef_func=[]}

let ldef_add_new_var ldef (v, e) = 
   {ldef with ldef_var=(v,e) ::ldef.ldef_var}

let ldef_add_new_func ldef f = 
   {ldef with ldef_func=f::ldef.ldef_func}

let def_add_proc def pid ldef m = 
   {def with def_proc=(pid, ldef.ldef_var, ldef.ldef_func, m)::def.def_proc}

let lctx_check_chan lctx c = 
   List.exists (fun i -> i = c) lctx.lctx_chan

let lctx_add_new_chan ~loc lctx c = 
   if List.exists (fun i -> i = c) lctx.lctx_chan then 
      error ~loc (AlreadyDefined c)
   else {lctx with lctx_chan=c::lctx.lctx_chan}

let lctx_check_var lctx v =
   List.fold_right (fun l b -> (List.exists (fun s -> s = v) l) || b) lctx.lctx_var false 

let lctx_add_new_var ~loc lctx v = 
   if lctx_check_var lctx v then error ~loc (AlreadyDefined v) else 
   match lctx.lctx_var with 
   | f::frames -> {lctx with lctx_var=(v::f)::frames}
   | _ -> error ~loc (UnintendedError)

let lctx_add_frame lctx = {lctx with lctx_var=([]::lctx.lctx_var)}

let lctx_pop_frame ~loc lctx = 
   match lctx.lctx_var with 
   | f::frames -> {lctx with lctx_var=frames}
   | _ -> error ~loc (UnintendedError)

let lctx_check_func lctx f = 
   List.exists (fun (i, _) -> i = f) lctx.lctx_func 

let lctx_get_func_arity lctx f = 
   let (_, k) = List.find (fun (i, _) -> i = f) lctx.lctx_func in k

let lctx_add_new_func ~loc lctx (f, i) = 
   if lctx_check_func lctx f then error ~loc (AlreadyDefined f) else {lctx with lctx_func=(f, i)::lctx.lctx_func}

let lctx_get_var_index ~loc lctx v =
   match find_index (fun l -> List.exists (fun s -> s = v) l) lctx.lctx_var with
   | Some i ->
      begin let lctxi = List.nth lctx.lctx_var i in 
      match find_index (fun s -> s = v) lctxi with 
      | Some j ->
         (List.length lctx.lctx_var - i - 1, List.length lctxi - j - 1)
      | None -> error ~loc (UnintendedError) end
   | None -> error ~loc (UnknownIdentifier v)

(* forbidden operators and primitive instructions *)
let forbidden_operator = ["read" ; "write" ; "invoke"; "recv"; "send"; "open"; "close"; "close_conn"; "connect"; "accept"]
type expr_type = TyVal | TyChan of Input.access_class list  * Input.chan_class list

let primitive_ins = [("read", Syntax.IRead, [TyVal]) ;
                     ("write", Syntax.IWrite, [TyVal; TyVal]) ; 
                     ("invoke", Syntax.IInvoke, 
                                 [TyChan([Input.CRecv ; Input.CSend], [Input.CStream]); TyVal; TyVal]) ; 
                     ("recv", Syntax.IRecv, [TyChan([Input.CRecv], [])]) ; 
                     ("send", Syntax.ISend, [TyChan([Input.CSend], []); TyVal]) ; 
                     ("open", Syntax.IOpen, [TyVal]) ; 
                     ("close", Syntax.IClose, [TyVal]) ; 
                     ("close_conn", Syntax.ICloseConn, [TyChan([], [Input.CStream])]) ; 
                     ("connect", Syntax.IConnect, [TyChan([], [Input.CStream])]) ; 
                     ("accept", Syntax.IAccept, [TyChan([Input.CSend], [Input.CStream])])]

let check_primitive_ins i =
   List.exists (fun (n, _, _) -> n = i) primitive_ins

let is_forbidden_operator o = List.exists (fun s -> s = o) forbidden_operator 


(* fr is used only for parsing and processing external instructions *)
let rec process_expr ?(fr=[]) ctx lctx {Location.data=c; Location.loc=loc} = 
   let process_expr' ?(fr=[]) ctx lctx = function
   | Input.Var id -> 
      if ctx_check_const ctx id then Syntax.Const id
      else if ctx_check_ext_const ctx id then Syntax.ExtConst id
      else if lctx_check_chan lctx id then Syntax.Channel (id, [], [])
      else if lctx_check_var lctx id then Syntax.Variable (Syntax.index_var id (lctx_get_var_index ~loc lctx id))
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
      if is_forbidden_operator o then error ~loc (ForbiddenIdentifier o) else
      if ctx_check_ext_func_and_arity ctx (o, List.length el) then Syntax.Apply (o, (List.map (fun a -> process_expr ~fr ctx lctx a) el)) else
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
               if ctx_check_event ctx eid then 
                  if List.length idl = ctx_get_event_arity ctx eid ~loc then ctx
                  else error ~loc (ArgNumMismatch (eid, (List.length idl), (ctx_get_event_arity ctx eid ~loc))) (* arity doesn't match *)
               else ctx_add_event ctx (eid, List.length idl)
               end in
               let idl = List.map (fun e -> process_expr ctx lctx e) idl in 
               (ctx, {Location.data=Syntax.Event (eid, idl) ; Location.loc=loc'}:: el')) (ctx, []) el in 
               (ctx, lctx', Syntax.EventStmt(a', el'))
  in
  let (ctx, lctx, c) = process_stmt' ctx lctx c in
  (ctx, lctx, Location.locate ~loc c)
  
  and process_atomic_stmt ctx lctx {Location.data=c; Location.loc=loc} = 
      let process_atomic_stmt' ctx lctx = function
      | Input.Skip -> (ctx, lctx, Syntax.Skip)
      | Input.Let (vid, e) ->
         let (lctx'', vid') =
            if lctx_check_var lctx vid then (lctx, Syntax.index_var vid (lctx_get_var_index ~loc lctx vid)) else
            let lctx' = lctx_add_new_var ~loc lctx vid in (lctx', Syntax.index_var vid (lctx_get_var_index  ~loc lctx' vid))
         in
         begin match e.Location.data with 
         |  Input.Apply(o, args) -> 
            if lctx_check_func lctx o then
            begin
               (* call *)
            if lctx_get_func_arity lctx o = List.length args then
               let args' = List.map (fun arg -> process_expr ctx lctx arg) args in
               (ctx, lctx'', Syntax.Call (vid', o, args'))
            else
             (* not enough argumentes *)
               error ~loc (ArgNumMismatch (o, (List.length args), (lctx_get_func_arity lctx o)))
            end else
            if check_primitive_ins o then
            begin
               let (_, ins, args_ty) = List.find (fun (s, _, _) -> s = o) primitive_ins in
               if List.length args = List.length args_ty then
                  (ctx, lctx'', Syntax.Instruction(vid', ins, 
                     List.map2 (fun arg arg_ty -> 
                     let e = process_expr ctx lctx arg in 
                     match e.Location.data, arg_ty with
                     | Syntax.Channel (s, _, _), TyChan (l1, l2) -> Location.locate ~loc:e.Location.loc (Syntax.Channel (s, l1, l2))
                     | Syntax.Channel (s, _, _), TyVal -> error ~loc (WrongInputType)
                     | _, TyVal -> e
                     | _, _ ->  error ~loc (WrongInputType)) args args_ty))
               else error ~loc (ArgNumMismatch (o, List.length args, List.length args_ty))
            end
            else (ctx, lctx'', Syntax.Let(vid', process_expr ctx lctx e))
         | _ -> (ctx, lctx'', Syntax.Let(vid', process_expr ctx lctx e))
         end
      | Input.If (e, c1, c2) ->
         let e' = process_expr ctx lctx e in 
         let lctx' = lctx_add_frame lctx in 
         let (ctx1, _, c1') = process_stmts ctx lctx' c1 in 
         let (ctx2, _, c2') = process_stmts ctx1 lctx' c2 in 
         (ctx2, lctx, Syntax.If (e', c1', c2'))

      | Input.For (vid, i, j, c) ->
         let (lctx', vid') = 
            let lctx'' = lctx_add_frame lctx in 
            let lctx2 = if lctx_check_var lctx'' vid then lctx'' else lctx_add_new_var ~loc lctx'' vid in 
            (lctx2, Syntax.index_var vid (lctx_get_var_index ~loc lctx2 vid)) in
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

let ctx_get_ty ~loc ctx s =
   try let (id, ty) = List.find (fun (id, _) -> id = s) ctx.ctx_ty in ty 
   with Not_found -> error ~loc (UnknownIdentifier s)


let process_decl ctx pol def sys {Location.data=c; Location.loc=loc} =
   let process_decl' ctx pol def sys = function
   | Input.DeclExtFun (f, k) -> 
      let ctx' =
         if check_used ctx f then error ~loc (AlreadyDefined f) else 
         if k = 0 then ctx_add_ext_const ctx f else if k > 0 then ctx_add_ext_func ctx (f, k) else error ~loc (NegativeArity k) 
      in (ctx', pol, def, sys)

   | Input.DeclExtEq (e1, e2) -> 
      let rec collect_vars e lctx =
         try let e = process_expr ctx lctx e in (e, lctx)
         with
         | Error {Location.data=err; Location.loc=locc} ->
            begin match err with
            | UnknownIdentifier id -> collect_vars e1 (lctx_add_new_var ~loc lctx id)
            | _ -> error ~loc:locc err
            end
      in 
      let (e1', lctx) = collect_vars e1 lctx_init in 
      let (e2', lctx) = collect_vars e2 lctx in
      (ctx, pol, def_add_ext_eq def (List.hd lctx.lctx_var, e1', e2'), sys)

  (* | DeclExtIns of Name.ident * expr list * event list * expr * event list *)

   | Input.DeclExtIns(id, args, pre, ret, post) -> error ~loc UnintendedError


   | Input.DeclType (id, c) -> 
      if check_used ctx id then error ~loc (AlreadyDefined id) else (ctx_add_ty ctx (id, c), pol, def, sys)
   
   | Input.DeclAccess(s, t, al) -> 
      let tys = ctx_get_ty ~loc ctx s in
      let tyt = ctx_get_ty ~loc ctx t in
      let f pol' a =
         begin
         match tys, tyt, a with
         | Input.CProc, Input.CFsys, Input.CRead 
         | Input.CProc, Input.CFsys, Input.CWrite 
         | Input.CProc, Input.CChan, Input.CSend 
         | Input.CProc, Input.CChan, Input.CRecv -> pol_add_access pol' (s, t, a)
         | _, _, _ -> error ~loc (WrongInputType)
         end
      in (ctx, List.fold_left f pol al, def, sys)

   | Input.DeclAttack (t, al) -> 
      let tyt = ctx_get_ty ~loc ctx t in
      let f pol' a =
         begin
         match tyt, a with
         | Input.CProc, Input.CEaves 
         | Input.CProc, Input.CTamper 
         | Input.CFsys, Input.CEaves 
         | Input.CFsys, Input.CTamper 
         | Input.CChan, Input.CEaves 
         | Input.CChan, Input.CTamper 
         | Input.CChan, Input.CDrop -> pol_add_attack pol' (t, a)
         | _, _-> error ~loc (WrongInputType)
         end
      in (ctx, List.fold_left f pol al, def, sys)

  | Input.DeclInit (id, e) -> 
      if check_used ctx id then error ~loc (AlreadyDefined id) else 
      let e' = process_expr ctx lctx_init e in 
      (ctx_add_const ctx id, pol, def_add_const def (id, e'), sys)

  | Input.DeclFsys (id, fl) ->
      if check_used ctx id then error ~loc (AlreadyDefined id) else 
      let fl' = List.map (fun (a, e, b) -> 
         match ctx_get_ty ~loc ctx b with
         | Input.CFsys ->
            (a, process_expr ctx lctx_init e, b )
         | _ -> error ~loc (WrongInputType)
         ) fl in 
      let (ctx', def') = List.fold_left (fun (ctx', def') (a, e, b) -> (ctx_add_fsys ctx' (id, a, b), def_add_fsys def' (id, a, e))) (ctx, def) fl' in 
      (ctx', pol, def', sys)

  | Input.DeclChan (id, c, ty) ->
      if check_used ctx id then error ~loc (AlreadyDefined id) else 
      (ctx_add_chan ctx (id, c, ty), pol, def, sys)

  | Input.DeclProc (pid, cargs, ty, cl, fs, m) ->
      begin match ctx_get_ty ~loc ctx ty 
      with 
      | Input.CProc -> 
         if check_used ctx pid then error ~loc (AlreadyDefined pid) else 
         let lctx = List.fold_left (fun lctx' cid -> lctx_add_new_chan ~loc lctx' cid) lctx_init cargs in
         let (lctx, ldef) = List.fold_left (fun (lctx', ldef') (vid, e) -> 
            (lctx_add_new_var ~loc lctx' vid, ldef_add_new_var ldef' (vid, process_expr ctx lctx' e))) (lctx, ldef_init) cl in
         let (ctx, lctx, ldef) = List.fold_left (fun (ctx'', lctx'', ldef'') (fid, args, cs, ret) -> 
            if lctx_check_func lctx'' fid then error ~loc (AlreadyDefined fid) else 
            let lctx = List.fold_left (fun lctx' vid -> lctx_add_new_var ~loc lctx' vid) (lctx_add_frame lctx'') args in
            let (ctx', lctx', cs')  = process_stmts ctx'' lctx cs in 
            (ctx', lctx_add_new_func ~loc lctx'' (fid, List.length args), 
                  ldef_add_new_func ldef'' (fid, args, cs', Syntax.index_var ret (lctx_get_var_index ~loc lctx' ret)))) (ctx, lctx, ldef) fs in
            let (ctx, _, m') = process_stmts ctx (lctx_add_frame lctx) m in 
            (ctx_add_proc ctx (pid, lctx.lctx_chan, ty, List.hd lctx.lctx_var, lctx.lctx_func), pol, 
               def_add_proc def pid ldef m', sys)

      | _ -> error ~loc (WrongInputType) 
      end 
   | Input.DeclSys (procs, lemmas) ->
      let processed_procs = List.map (fun proc -> 
         match proc.Location.data with 
         | Input.Proc(pid, chans, fsys) -> 
            if not (ctx_check_proc ctx pid) then error ~loc (UnknownIdentifier pid) else
            if not (ctx_check_fsys ctx fsys) then error ~loc (UnknownIdentifier fsys) else
            let (_, cargs, ptype, _, _) = ctx_get_proc ctx pid in
            let (_, vl, fl, m) = def_get_proc def pid in
            let fpaths = List.fold_left (fun fpaths (fsys', path, ftype) -> if fsys = fsys' then (path, ftype) :: fpaths) [] ctx.ctx_fsys in 
            let fpaths = List.map (fun (path, ftype) -> 
                                    let (_ , _ , v) = List.find (fun (fsys', path', val') -> fsys' = fsys && path = path') def.def_fsys in 
                                    (path, v, ftype)) fpaths in 
            let fpaths = List.map (fun (path, v, ftype) -> 
                                    let accs = List.fold_left (fun accs (s, t, a) -> 
                                       if s = ptype && t = ftype then a :: accs else accs) [] pol.pol_access in
                                    let attks = List.fold_left (fun attks (t, a) -> 
                                       if t = ftype then a :: attks else attks) [] pol.pol_attack in
                                    (path,v,accs, attks)) fpaths in 
            if (List.length cargs) !=  (List.length chans) then error ~loc (ArgNumMismatch (pid, (List.length chans), (List.length cargs)))
            else
               let (chs, vl, fl, m) = List.fold_left2 
                  (fun (chs, vl, fl, m) f t -> 
                     if ctx_check_chan ctx t then 
                        let (_, chan_class, chan_ty) = List.find (fun (s, _, _) -> s = t) ctx.ctx_chan in  
                        let accesses = List.fold_left (fun acs (f', t', ac) -> if f' = ptype && t' = chan_ty then ac::acs else acs) [] pol.pol_access in 
                        (
                           (t, chan_class, accesses,
                              List.fold_left (fun attks (s, a) -> if s = t then a :: attks else attks ) [] pol.pol_attack) :: chs,
                           List.map (fun (v, e) -> (v, Substitute.expr_chan_sub e f t accesses chan_class)) vl,
                           List.map (fun (f, args, c, ret) -> (f, args, List.map (fun c -> Substitute.stmt_chan_sub c f t accesses chan_class) c, ret)) fl,
                           List.map (fun c -> Substitute.stmt_chan_sub c f t accesses chan_class) m)
                     else error ~loc (UnknownIdentifier t)) ([], vl, fl, m) cargs chans in 
               (  pid, 
                  List.fold_left (fun attks (t, a) -> if t = pid then a :: attks else attks) [] pol.pol_attack,
                  chs, fpaths, vl, fl, m)) procs in  
      let processed_procs = List.fold_left (fun (processed_procs,k) (pid, attks, chans, files, fpaths, vl, fl, m)
         -> ((k,pid, attks, chans, files, fpaths, vl, fl, m) :: processed_procs, k+1)) ([],0) processed_procs in 
      (ctx, pol, def, {sys with sys_proc=processed_procs::sys.sys_proc})

let process_init = (ctx_init, pol_init, def_init, sys_init)

let load fn ctx pol def sys =
   let decls= Lexer.read_file Parser.file fn in 
   let (ctx, pol, def, sys) = List.fold_left 
   (fun (ctx, pol, def, sys) decl -> process_decl ctx pol def sys decl) 
   (ctx, pol, def, sys) decls in (ctx, pol, def, sys)

