(** Conversion from concrete syntax to abstract syntax.
    Here we also load all required files, which may not be
    optimal but is systematic. *)

(** Conversion errors *)
type desugar_error =
  | UnknownIdentifier of string
  | UnknownFunction of string
  | TypeDoesnotMatch of string

exception Error of desugar_error Location.located

(** [error ~loc err] raises the given runtime error. *)
let error ~loc err = Stdlib.raise (Error (Location.locate ~loc err))

(** Print error description. *)
let print_error err ppf =
  match err with
  | UnknownIdentifier x -> Format.fprintf ppf "unknown identifier %s" x
  | UnknownFunction x -> Format.fprintf ppf "unknown function %s" x

(** A desugaring context is a list of known identifiers, which is used
    to compute de Bruijn indices. *)


type filesys = {
   files : string * Syntax.expr * Name.ident
}

type context = {
   ext_fun : (Name.ident * int) list ; 
   ext_const : (Name.ident) list ; 
   ty : (Name.ident * type_class) list ;
   const : Name.ident list ;
   fsys : (Name.ident * Name.ident * Name.ident) list ; (*fsys name, fsys path, type *)
   chan : (Name.ident * transfer * Name.ident) list ;
   proc : (Name.ident * (Name.ident list) * Name.ident * Name.ident list * (Name.ident * int) list)
}

let ctx_check_ext_fun ctx o = 
   exists (fun (s, _) -> s = o) ctx.ext_fun
let ctx_check_ext_cosnt ctx o = 
   exists (fun s -> s = o) ctx.ext_const
let ctx_check_ty ctx o = 
   exists (fun (s, _) -> s = o) ctx.ty
let ctx_check_const ctx o = 
   exists (fun s -> s = o) ctx.const
let ctx_check_fsys ctx o = 
   exists (fun (s, _, _) -> s = o) ctx.fsys
let ctx_check_chan ctx o = 
   exists (fun (s, _, _) -> s = o) ctx.chan

let ctx_add_ext_fun ctx (f, k) = {ctx with ext_fun=(f, k)::ctx.ext_fun}
let ctx_add_ext_const ctx c = {ctx with ext_const=c::ctx.ext_const}
let ctx_add_ty ctx (id, c) = {ctx with ty=(id, c)::ctx.ty}
let ctx_add_const ctx id = {ctx with const=id::ctx.const}
let ctx_add_fsys ctx (a, p, ty) = {ctx with fsys=(a, p, ty)::ctx.fsys}
let ctx_add_chan ctx (c, t, ty) = {ctx with chan=(c, t, ty)::ctx.chan}

let check_fresh ctx s =
   if ctx_check_ext_fun ctx s || 
      ctx_check_ext_const ctx s || 
      ctx_check_ty ctx s || 
      ctx_check_const ctx s || 
      ctx_check_fsys ctx s ||
      ctx_check_chan ctx s then false else true 

let check_used ctx s =  
   if (check_fresh ctx s ) then false else true


type definition = {
   ext_eq : (Syntax.expr * Syntax.expr) list ;
   const : (Name.ident * Syntax.expr) list ;
   fsys : (Name.ident * Name.ident * Syntax.expr) list (*fsys name, fsys path, data *) ;
   proc : (Name.ident * (Name.ident * Syntax.expr) list * (* variablse *)
                        (Name.ident * (Name.ident list) * Sytax.stmt * Name.ident) list * (* member functions *)
                        Syntax.stmt) list (* main fun *)
}

let def_add_ext_eq def x = {def with ext_eq=x::def.ext_eq}
let def_add_const def x = {def with const=x::def.const}
let def_add_fsys def x = {def with fsys=x::def.fsys}

type access_policy = {
   access : (Name.ident * Name.ident * access_class) list ;
   attack : (Name.ident * attack_class) list 
}

let pol_add_access pol x = {pol with access=x::pol.access}
let pol_add_attack pol x = {pol with attack=x::pol.attack}

(** Initial context *)
let ctx_init = {
   ext_fun = [] ;
   ext_const = [] ;
   ty = [] ;
   const = [] ;
   fsys = [] ;
   chan = [] ;
   prac = []
}

let def_init = {   
   ext_eq = [] ;
   const = [] ;
   prac = []
}

let pol_init = {
   accesses = [] ; 
   attacks = []
}

type proc_context = { proc_const: Name.ident list ; proc_fun: (Name.ident * int) list }

let lctx_check_variable lctx id =
   exists (fun s -> s = id) lctx

let forbidden_operator = [ "invoke" ; "send" ]

let is_forbidden_operator o = exists (fun s -> s = o) forbidden_operator 

let primitive_operator = [ ("+", 2) ]

let is_primitive_operator o ar = exists (fun s -> s = (o, ar)) primitive_operator 

(** Add a new identifier to the context. *)
let add_ident x {idents; funs} = {idents = x :: idents; funs}

let rec process_expr ctx def lctx {Location.data=c; Location.loc=loc} = 
   let process_expr' ctx def lctx = function
   | Input.Var id -> 
      if ctx_check_const ctx id then Syntax.Cosnt id
      else if ctx_check_ext_cosnt ctx id then Syntax.ExtConst id
      else if lctx_check_variable lctx id then Syntax.Variable id
      else error ~loc (UnknownIdentifier id) 
   | Input.Boolean b -> Syntax.Boolean b
   | Input.String s -> Syntax.String s 
   | Input.Integer z -> Syntax.Integer z
   | Input.Float f -> Syntax.Float f
   | Input.Apply(o, el) ->
      if is_forbidden_operator o then error ~loc (UnknownIdentifier o) else
      if is_primitive_operator o (length el) then Syntax.Primitive (o, (List.fold_right (fun a b -> process_expr  a :: b) el [])) else
      if ctx_check_ext_fun ctx o (length el) then Syntax.External (o, (List.fold_right (fun a b -> process_expr  a :: b) el [])) else
      error ~loc (UnknownIdentifier o)
   | Input.Tuple el -> Syntax.Tuple (List.fold_right (fun a b -> process_expr  a :: b) el [])
  in
  let c = process_expr' ctx def e in
  Location.locate ~loc c

let rec process_stmt ctx def lctx lfun c {Location.data=c; Location.loc=loc} = 
   let process_stmt' ctx def lctx = function
   | Input.Var id -> 
      if ctx_check_const ctx id then Syntax.Cosnt id
      else if ctx_check_ext_cosnt ctx id then Syntax.ExtConst id
      else if lctx_check_variable lctx id then Syntax.Variable id
      else error ~loc (UnknownIdentifier id) 
   | Input.Boolean b -> Syntax.Boolean b
   | Input.String s -> Syntax.String s 
   | Input.Integer z -> Syntax.Integer z
   | Input.Float f -> Syntax.Float f
   | Input.Apply(o, el) ->
      if is_forbidden_operator o then error ~loc (UnknownIdentifier o) else
      if is_primitive_operator o (length el) then Syntax.Primitive (o, (List.fold_right (fun a b -> process_stmt  a :: b) el [])) else
      if ctx_check_ext_fun ctx o (length el) then Syntax.External (o, (List.fold_right (fun a b -> process_expr  a :: b) el [])) else
      error ~loc (UnknownIdentifier o)
   | Input.Tuple el -> Syntax.Tuple (List.fold_right (fun a b -> process_expr  a :: b) el [])
  in
  let c = process_stmt' ctx def e in
  Location.locate ~loc c

let ctx_get_ty ~loc ctx s =
   try let (id, ty) = find (fun (id, _) -> id = s) ctx.ty in ty 
   with Not_found -> error ~loc (UnknownIdentifier s)


let process_decl ctx pol def {Location.data=c; Location.loc=loc} =
   let process_decl' ctx pol def = function
   | DeclExtFun (f, k) -> 
      let ctx' =
         if check_used ctx f then error ~loc (UnknownIdentifier f) else 
         if k == 0 then ctx_add_ext_const f else if k > 0 then ctx_add_ext_fun (f, k) else error ~loc (UnknownIdentifier f) 
      in (ctx', pol, def)

   | DeclExtEq (e1, e2) -> 
      let e1' = process_expr ctx def [] e1 in 
      let e2' = process_expr ctx def [] e2 in
      (ctx, pol, def_add_ext_eq def e1' e2')

   | DecType (id, c) -> 
      if check_used ctx id then error ~loc (UnknownIdentifier "") else (ctx_add_ty ctx (id, c), pol, def)
   
   | DeclAccess(s, t, al) -> 
      let tys = ctx_get_ty ~loc ctx s in
      let tyt = ctx_get_ty ~loc ctx t in
      let f pol' a =
         begin
         match tys, tyt, a with
         | CProc, CFsys, CRead | CProc, CFsys, CWrite | CProc, CChan, CSend | CProc, CChan, CRecv -> pol_add_access pol' (s, t, a)
         | _, _, _ -> error ~loc (UnknownIdentifier "")
         end
      in (ctx, List.fold_left f pol al, def)

   | DeclAttack (t, al) -> 
      let tyt = ctx_get_ty ~loc ctx t in
      let f pol' a =
         begin
         match tyt, a with
         | CProc, CEaves | CProc, CTamper | CFsys, CEaves | CFsys, CTamper | CChan, CEaves | CChan, CTamper | CChan, CDrop -> pol_add_attack pol' (t, a)
         | _, _-> error ~loc (UnknownIdentifier "")
         end
      in (ctx, List.fold_left f pol al, def)

  | DeclInit (id, e) -> 
      if check_used ctx id then error ~loc (UnknownIdentifier "") else 
      let e' = process_expr ctx def [] e in 
      (ctx_add_const ctx id, pol, def_add_cosnt def (id, e))

  | DeclFsys (id, fl) ->
      if check_used ctx id then error ~loc (UnknownIdentifier "") else 
      let fl' = List.map (fun (a, e, b) -> (a, process_expr ctx def [] e, b )) fl in 
      let (ctx', def') = List.fold_left (fun (ctx', def') (a, e, b) -> (ctx_add_fsys ctx' (id, a, b), def_add_fsys def' (id, a, e))) (ctx, def) fl' in 
      (ctx', pol, def')

  | DeclChan (id, c, ty) ->
      if check_used ctx id then error ~loc (UnknownIdentifier "") else 
      (ctx_add_chan ctx (id, c, ty), pol, def)

  | DeclProc (pid, cargs, ty, cl, fs, m) ->
      List.fold_left (fun _ id -> if check_used ctx id then error ~loc (UnknownIdentifier "") else ()) () (pid :: cargs) ; 
      if exists_dup (pid :: cargs) then error ~loc (UnknownIdentifier "") else () ; 
      let pty = ctx_get_ty ~loc ctx ty in
      match pty with 
      | CProc -> 
         let (lctx, ldef) = List.fold_right (fun (id, e) (lctx, ldef) -> 
            if check_used ctx id then error ~loc (UnknownIdentifier "") else
            if List.exists (fun s -> s = id) (pid :: cargs ++ lctx) then error ~loc (UnknownIdentifier "") else
            let e' = process_expr ctx def lctx e in
            (id :: lctx, (id, e') :: ldef)) cl ([], []) in
            
         let (lfun, lfdef) =  List.fold_right 
            (fun (id, fargs, cs, ret) (lfun, lfdef) ->
               List.fold_right 
                  (fun id _ -> 
                     if check_used ctx id || List.exists (fun s -> s = id) (pid :: cargs ++ lctx) 
                                          || List.exists (fun (s, k) -> s = id) lfun 
                      then error ~loc (UnknownIdentifier "") else ()) (id::fargs) () ; 
               if exists_dup (id :: fargs) then error ~loc (UnknownIdentifier "") else () ; 
               let (lctx', cs') = process_stmts ctx def (fargs ++ lctx) lfun cs in 
               if List.exists (fun i -> i = ret ) lctx' then 
                  ((id, length(fargs)) :: lfun, (id, fargs, cs', ret) :: lfdef) else error ~loc (UnknownIdentifier ""))
            fs ([], []) in 
            m' = process_stmts ctx def lctx lfun m in 
            (ctx_add_proc ctx (pid, cargs, ty, lctx, lfun), pol, 
               def_add_proc def (pid, ldef, lfdef, m', ret))

      | _ -> error ~loc (UnknownIdentifier "")

  let c = process_decl' ctx pol def c in
  Location.locate ~loc c

let load fn =
  let (decls, sys) = Lexer.read_file Parser.file fn in
  let x = List.fold_left (fun (ctx, pol, def) decl ->
                           process_decl ctx pol def recl) 
            (ctx_init, pol_init, def_init) decls 
  in x
