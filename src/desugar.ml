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
  | NegativeArity k -> Format.fprintf ppf "negative arity is given: %s" (string_of_int k)

(** A desugaring context is a list of known identifiers, which is used
    to compute de Bruijn indices. *)

let find_index f l =
   let j = snd (List.fold_right (fun a (i, j) -> let j = if f a && j < 0 then i else j in (i+1, j)) l (0,-1) ) in 
   if j < 0 then None else Some (List.length l - 1 - j)

type context = {
   ctx_ext_const : (Name.ident) list ; 
   ctx_ext_func : (Name.ident * int) list ; 
   ctx_ty : (Name.ident * Input.type_class) list ;
   ctx_const : Name.ident list ;
   ctx_fsys : (Name.ident * Name.ident * Name.ident) list ; (*fsys name, fsys path, type *)
   ctx_chan : (Name.ident * Input.chan_class * Name.ident) list ;
   ctx_proc : (Name.ident * (Name.ident list) * Name.ident * Name.ident list * (Name.ident * int) list) list;
   ctx_event : (Name.ident * int) list }

let print_type_class c = 
   match c with 
   | Input.CProc -> "Proc"
   | Input.CFsys -> "Fsys" 
   | Input.CChan -> "Chan"

let print_chan_class c = 
   match c with 
   | Input.CDatagram -> "datagram"
   | Input.CStream -> "stream"

(* type access_class = CRead |  CWrite | CSend | CRecv 
type attack_class = CEaves |  CTamper | CDrop 
type chan_class = CDatagram | CStream
 *)



let print_context  ctx =
    begin 
   "external constants:"^ (List.fold_left (fun a (v) -> a ^" "^ v) "" ctx.ctx_ext_const) ^ "\n" ^
   "external functions:"^ (List.fold_left (fun a (v, i) -> a ^" "^ v ^"."^ (string_of_int i)) "" ctx.ctx_ext_func) ^ "\n" ^
   "types:             "^ (List.fold_left (fun a (v, c) -> a ^" "^ v ^":"^ (print_type_class c)) "" ctx.ctx_ty) ^ "\n" ^
   "constants:         "^ (List.fold_left (fun a (v) -> a ^" "^ v) "" ctx.ctx_const) ^ "\n" ^
   (List.fold_left (fun a (x, y, z) -> a^"file systems:      "^ "name:"^x^" path:"^y^" type:"^z^"\n") "" ctx.ctx_fsys)^
   (List.fold_left (fun a (x, y, z) -> a^"channel:           "^ "name:"^x^" method:"^(print_chan_class y)^" type:"^z^"\n") "" ctx.ctx_chan)^
   (List.fold_left (fun a (x, args, ty, vars, funs) -> a^"procedures:        "^ "name:"^x^" chans:"^
      (List.fold_left (fun a (v) -> a ^" "^ v) "" args)^
      " type:"^ty^" variables:" ^(List.fold_left (fun a (v) -> a ^" "^ v) "" vars)^
      " functions:" ^ (List.fold_left (fun a (v, i) -> a ^" "^ v ^"."^ (string_of_int i)) "" funs) ^ "\n") "" ctx.ctx_proc)^
   "events:            "^ (List.fold_left (fun a (v, i) -> a ^" "^ v ^"."^ (string_of_int i)) "" ctx.ctx_event) ^ "\n" end


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
let ctx_check_event ctx eid = 
   List.exists (fun (s, _) -> s = eid) ctx.ctx_event
let ctx_add_event ctx (eid, k) = 
   {ctx with ctx_event=(eid,k)::ctx.ctx_event}      
let ctx_get_event_arity ~loc ctx eid =
   if ctx_check_event ctx eid then 
   let (_, k) = List.find (fun (s, _) -> s = eid) ctx.ctx_event in k
   else error ~loc (UnknownIdentifier eid)


let ctx_add_ext_func ctx (f, k) = {ctx with ctx_ext_func=(f, k)::ctx.ctx_ext_func}
let ctx_add_ext_const ctx c = {ctx with ctx_ext_const=c::ctx.ctx_ext_const}
let ctx_add_ty ctx (id, c) = {ctx with ctx_ty=(id, c)::ctx.ctx_ty}
let ctx_add_const ctx id = {ctx with ctx_const=id::ctx.ctx_const}
let ctx_add_fsys ctx (a, p, ty) = {ctx with ctx_fsys=(a, p, ty)::ctx.ctx_fsys}
let ctx_add_chan ctx (c, t, ty) = {ctx with ctx_chan=(c, t, ty)::ctx.ctx_chan}
let ctx_add_proc ctx p = {ctx with ctx_proc=p::ctx.ctx_proc}

let check_fresh ctx s =
   if ctx_check_ext_func ctx s || 
      ctx_check_ext_const ctx s || 
      ctx_check_ty ctx s || 
      ctx_check_const ctx s || 
      ctx_check_fsys ctx s ||
      ctx_check_chan ctx s then false else true 

let check_used ctx s =  
   if (check_fresh ctx s ) then false else true


type definition = {
   def_ext_eq : (Syntax.expr * Syntax.expr) list ;
   def_const : (Name.ident * Syntax.expr) list ;
   def_fsys : (Name.ident * Name.ident * Syntax.expr) list (*fsys name, fsys path, data *) ;
   def_proc : (Name.ident * (Name.ident * Syntax.expr) list * (* variablse *)
                        (Name.ident * (Name.ident list) * Syntax.stmt list * Syntax.indexed_var) list * (* member functions *)
                        Syntax.stmt list) list (* main fun *)
}

let def_add_ext_eq def x = {def with def_ext_eq=x::def.def_ext_eq}
let def_add_const def x = {def with def_const=x::def.def_const}
let def_add_fsys def x = {def with def_fsys=x::def.def_fsys}

type access_policy = {
   pol_access : (Name.ident * Name.ident * Input.access_class) list ;
   pol_attack : (Name.ident * Input.attack_class) list 
}

let pol_add_access pol x = {pol with pol_access=x::pol.pol_access}
let pol_add_attack pol x = {pol with pol_attack=x::pol.pol_attack}

(** Initial context *)
let ctx_init = {ctx_ext_func = [] ; ctx_ext_const = [] ; ctx_ty = [] ; ctx_const = [] ; ctx_fsys = [] ; ctx_chan = [] ; ctx_proc = [] ; ctx_event = []}
let def_init = {def_ext_eq = [] ; def_const = [] ; def_fsys=[] ; def_proc = []}
let pol_init = {pol_access = [] ; pol_attack = []}

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

(* list of names forbidden for operators in expr *)
let forbidden_operator = ["read" ; "write" ; "invoke";  "recv"; "send"; "open"; "close"; "close_conn"; "connect"; "accept"]

let is_forbidden_operator o = List.exists (fun s -> s = o) forbidden_operator 



let rec process_expr ctx lctx {Location.data=c; Location.loc=loc} = 
   let process_expr' ctx lctx = function
   | Input.Var id -> 
      if ctx_check_const ctx id then Syntax.Const id
      else if ctx_check_ext_const ctx id then Syntax.ExtConst id
      else if lctx_check_var lctx id then Syntax.Variable (Syntax.index_var id (lctx_get_var_index ~loc lctx id))
      else error ~loc (UnknownIdentifier id) 
   | Input.Boolean b -> Syntax.Boolean b
   | Input.String s -> Syntax.String s 
   | Input.Integer z -> Syntax.Integer z
   | Input.Float f -> Syntax.Float f
   | Input.Apply(o, el) ->
      if is_forbidden_operator o then error ~loc (ForbiddenIdentifier o) else
      if ctx_check_ext_func_and_arity ctx (o, List.length el) then Syntax.Apply (o, (List.map (fun a -> process_expr ctx lctx a) el)) else
      error ~loc (UnknownIdentifier o)
   | Input.Tuple el -> Syntax.Tuple (List.map (fun a -> process_expr  ctx lctx a) el)
  in
  let c = process_expr' ctx lctx c in
  Location.locate ~loc c


let rec process_stmt ctx lctx {Location.data=c; Location.loc=loc} = 
   let process_stmt' ctx lctx = function
   | Input.OpStmt a -> 
      let (ctx', lctx', a') = process_atomic_stmt ctx lctx a in (ctx', lctx', Syntax.OpStmt a')
   | Input.EventStmt (a, el) -> 
      let (ctx, lctx', a') = process_atomic_stmt ctx lctx a in
      let (ctx, el') = List.fold_right (fun e (ctx, el') -> 
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
               let idl = List.map (fun (v, b) -> ((Syntax.index_var v (lctx_get_var_index ~loc lctx v)), b)) idl in 
               (ctx, {Location.data=Syntax.Event (eid, idl) ; Location.loc=loc'}:: el')) el (ctx, []) in 
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
            begin match o with
            | "recv" -> 
               begin match args with
                  | [s'] -> begin match s'.Location.data with 
                           | Input.Var s -> 
                              if lctx_check_chan lctx s 
                              then (ctx, lctx'', Syntax.Instruction (vid', Syntax.IRecv, [Location.locate (Syntax.Channel s)]))
                              else error ~loc (UnknownIdentifier s)
                           | _ -> error ~loc (WrongInputType)
                           end
                  | _ -> error ~loc (ArgNumMismatch ("recv", List.length args, 1))
               end
            | _ -> (ctx, lctx'', Syntax.Let (vid', process_expr ctx lctx e))
            end
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


let process_decl ctx pol def {Location.data=c; Location.loc=loc} =
   let process_decl' ctx pol def = function
   | Input.DeclExtFun (f, k) -> 
      let ctx' =
         if check_used ctx f then error ~loc (AlreadyDefined f) else 
         if k = 0 then ctx_add_ext_const ctx f else if k > 0 then ctx_add_ext_func ctx (f, k) else error ~loc (NegativeArity k) 
      in (ctx', pol, def)

   | Input.DeclExtEq (e1, e2) -> 
      let e1' = process_expr ctx lctx_init e1 in 
      let e2' = process_expr ctx lctx_init e2 in
      (ctx, pol, def_add_ext_eq def (e1', e2'))

   | Input.DeclType (id, c) -> 
      if check_used ctx id then error ~loc (AlreadyDefined id) else (ctx_add_ty ctx (id, c), pol, def)
   
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
      in (ctx, List.fold_left f pol al, def)

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
      in (ctx, List.fold_left f pol al, def)

  | Input.DeclInit (id, e) -> 
      if check_used ctx id then error ~loc (AlreadyDefined id) else 
      let e' = process_expr ctx lctx_init e in 
      (ctx_add_const ctx id, pol, def_add_const def (id, e'))

  | Input.DeclFsys (id, fl) ->
      if check_used ctx id then error ~loc (AlreadyDefined id) else 
      let fl' = List.map (fun (a, e, b) -> (a, process_expr ctx lctx_init e, b )) fl in 
      let (ctx', def') = List.fold_left (fun (ctx', def') (a, e, b) -> (ctx_add_fsys ctx' (id, a, b), def_add_fsys def' (id, a, e))) (ctx, def) fl' in 
      (ctx', pol, def')

  | Input.DeclChan (id, c, ty) ->
      if check_used ctx id then error ~loc (AlreadyDefined id) else 
      (ctx_add_chan ctx (id, c, ty), pol, def)

  | Input.DeclProc (pid, cargs, ty, cl, fs, m) ->
      match ctx_get_ty ~loc ctx ty with 
      | Input.CProc -> 
         if check_used ctx pid then error ~loc (AlreadyDefined pid) else 
         let lctx = List.fold_right (fun cid lctx' -> lctx_add_new_chan ~loc lctx' cid) cargs lctx_init in
         let (lctx, ldef) = List.fold_right (fun (vid, e) (lctx', ldef') -> 
            (lctx_add_new_var ~loc lctx' vid, ldef_add_new_var ldef' (vid, process_expr ctx lctx' e))) cl (lctx, ldef_init) in
         let (ctx, lctx, ldef) = List.fold_right (fun (fid, args, cs, ret) (ctx'', lctx'', ldef'') -> 
            if lctx_check_func lctx'' fid then error ~loc (AlreadyDefined fid) else 
            let lctx = List.fold_right (fun vid lctx' -> lctx_add_new_var ~loc lctx' vid) args (lctx_add_frame lctx'') in
            let (ctx', lctx', cs')  = process_stmts ctx'' lctx cs in 
            (ctx', lctx_add_new_func ~loc lctx'' (fid, List.length args), 
                  ldef_add_new_func ldef'' (fid, args, cs', Syntax.index_var ret (lctx_get_var_index ~loc lctx' ret)))) fs (ctx, lctx, ldef) in
            let (ctx, _, m') = process_stmts ctx (lctx_add_frame lctx) m in 
            (ctx_add_proc ctx (pid, cargs, ty, List.hd lctx.lctx_var, lctx.lctx_func), pol, 
               def_add_proc def pid ldef m')

      | _ -> error ~loc (WrongInputType) 
   in
  let c = process_decl' ctx pol def c in
c

let process_init = (ctx_init, pol_init, def_init)

let load fn ctx pol def =
  let (decls) = Lexer.read_file Parser.file fn in 
  (* decls  *)

  let x = List.fold_left (fun (ctx, pol, def) decl ->
                           process_decl ctx pol def decl) 
            (ctx, pol, def) decls 
  in x
