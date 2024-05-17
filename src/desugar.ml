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
   chan : (Name.ident * transfer * Name.ident) list 
}

type definition = {
   ext_eq : (Syntax.expr * Syntax.expr) list ;
   const : (Name.ident * Syntax.expr) list ;
   fsys : (Name.ident * Name.ident * Syntax.expr) list (*fsys name, fsys path, data *)
}

type access_policy = {
   accesse : (Name.ident * Name.ident * access_class) list ;
   attack : (Name.ident * attack_class) list 
}


(** Initial context *)
let ctx_init = {
   ext_fun = [] ;
   ext_const = [] ;
   ty = [] ;
   const = [] ;
   fsys = [] ;
   chan = []
}

let def_init = {   
   ext_eq = [] ;
   const = [] 
}

let acp_init = {
   accesses = [] ; 
   attacks = []
}

let ctx_check_ext_fun { ext_fun; _; _; _; _; _ } o = 
   exists (fun (s, _) -> s = o) ext_fun

let ctx_check_ext_cosnt { _; ext_const; _; _; _; _ } o = 
   exists (fun s -> s = o) ext_const

let ctx_check_ty { _; _; ty; _; _; _ } o = 
   exists (fun (s, _) -> s = o) ty

let ctx_check_const { _; _; _; const; _; _ } o = 
   exists (fun s -> s = o) const

let ctx_check_fsys { _; _; _; _; fsys; _ } o = 
   exists (fun (s, _) -> s = o) fsys

let ctx_check_chan { _; _; _; _; _; chan } o = 
   exists (fun (s, _) -> s = o) chan

let check_fresh ctx s =
   if ctx_check_ext_fun ctx s || 
      ctx_check_ext_const ctx s || 
      ctx_check_ty ctx s || 
      ctx_check_const ctx s || 
      ctx_check_fsys ctx s ||
      ctx_check_chan ctx s then false else true 

let lctx_check_variable lctx id =
   exists (fun s -> s = id) lctx

let verify_fresh { ext_fun; ; _; const; _; _ } f = 

let forbidden_operator = [ "invoke" ; "send" ]

let is_forbidden_operator o = exists (fun s -> s = o) forbidden_operator 

let primitive_operator = [ ("+", 2) ]

let is_primitive_operator o ar = exists (fun s -> s = (o, ar)) primitive_operator 


(** Add a new identifier to the context. *)
let add_ident x {idents; funs} = {idents = x :: idents; funs}

(** Add many identifiers to the context. *)
let add_args xts ctx = List.fold_left (fun ctx (x, _) -> add_ident x ctx) ctx xts

(** Add a new function name to the context. *)
let add_fun f {idents; funs} = {idents; funs = f :: funs}

(** Find the de Bruijn index of [x] in the context [ctx]. *)
let index x {idents; _} =
  let rec search k = function
    | [] -> None
    | y :: ys ->
     if x = y then Some k else search (k+1) ys
  in
  search 0 idents

let index_fun f {funs; _} =
  let rec search k = function
    | [] -> None
    | g :: gs ->
     if f = g then Some k else search (k+1) gs
  in
  search 0 funs


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
  Location.locate ~loc e


let process_decl ctx pol def {Location.data=c; Location.loc=loc} =
   let process_decl' ctx pol def = function
   | DeclExtFun (f, k) -> 
      let ctx' =
         if check_fresh ctx f then error ~loc (UnknownIdentifier f) else 
         if k == 0 then ctx_add_ext_const f else if k > 0 then ctx_add_ext_fun (f, k) else error ~loc (UnknownIdentifier f) 
      in (ctx', pol, def)

   | DeclExtEq (e1, e2) -> 
      let e1' = process_expr ctx def [] e1 in 
      let e2' = process_expr ctx def [] e2 in
      (ctx, pol, def_add_ext_eq def e1' e2')

   | DecType (id, c) -> 
      if check_fresh ctx id then error ~loc (UnknownIdentifier "") else (ctx_add_ty ctx (id, c), pol, def)
   
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
      if check_fresh ctx id then error ~loc (UnknownIdentifier "") else 
      let e' = process_expr ctx def [] e in 
      (ctx_add_const ctx id, pol, def_add_cosnt def (id, e))

  | DeclFsys (id, fl) ->
      if check_fresh ctx id then error ~loc (UnknownIdentifier "") else 
      let fl' = List.map (fun (a, e, b) -> (a, process_expr ctx def [] e, b )) fl in 
      let (ctx', def') = List.fold_left (fun (ctx', def') (a, e, b) -> (ctx_add_fsys ctx' (id, a, b), def_add_fsys def' (id, a, e))) (ctx, def) fl' in 
      (ctx', pol, def')

  | DeclChan (id, c, ty) ->
      if check_fresh ctx id then error ~loc (UnknownIdentifier "") else 
      (ctx_add_chan ctx (id, c, ty), pol, def)

  | DeclProc of Name.ident * (Name.ident list) * Name.ident * 
                ((Name.ident * expr) list) * 
                (Name.ident * (Name.ident list) * stmt list * Name.ident) list* 
                stmt list

  let c = process_decl' ctx pol def c in
  Location.locate ~loc c



(** Desugar a value type *)
let valty = function
  | Input.TBoolean -> Type.Boolean
  | Input.TInteger -> Type.Integer
  | Input.TReal -> Type.Real

(** Desugar a computation type *)
let cmpty = function
  | Input.TData dt -> Type.Data (valty dt)
  | Input.TCommand -> Type.Command

(** Desugar a function type *)
let funty (dts, t) = (List.map valty dts, cmpty t)

(** Desugar a computation *)
let rec comp ctx {Location.data=c; Location.loc=loc} =

  let comp' ctx = function

    | Input.Var x ->
       begin match index x ctx with
       | None -> error ~loc (UnknownIdentifier x)
       | Some k -> Syntax.Var k
       end

    | Input.Boolean b -> Syntax.Boolean b

    | Input.Integer k -> Syntax.Integer k

    | Input.Float x -> Syntax.Float x

    | Input.Apply (f, es) ->
       begin match index_fun f ctx with
       | None -> error ~loc (UnknownFunction f)
       | Some k ->
          let es = List.map (comp ctx) es in
          Syntax.Apply (k, es)
       end

    | Input.Skip ->
       Syntax.Skip

    | Input.Trace ->
       Syntax.Trace

    | Input.Sequence (c1, c2) ->
       let c1 = comp ctx c1
       and c2 = comp ctx c2 in
       Syntax.Sequence (c1, c2)

    | Input.Case lst ->
       let rec fold = function
         | [] -> []
         | (b,c) :: lst ->
            let b = comp ctx b
            and c = comp ctx c
            and lst = fold lst in
            (b, c) :: lst
       in
       Syntax.Case (fold lst)

    | Input.If (b, c1, c2) ->
       let b = comp ctx b
       and c1 = comp ctx c1
       and c2 = comp ctx c2 in
       Syntax.If (b, c1, c2)

    | Input.While (b, c) ->
       let b = comp ctx b
       and c = comp ctx c in
       Syntax.While (b, c)

    | Input.Let (lst, c) ->
       let rec fold ctx' lst' = function
         | [] -> ctx', List.rev lst'
         | (x,c) :: lst ->
            let c = comp ctx c in
            let ctx' = add_ident x ctx'
            and lst' = (x,c) :: lst' in
            fold ctx' lst' lst
       in
       let ctx, lst = fold ctx [] lst in
       let c = comp ctx c in
       Syntax.Let (lst, c)

    | Input.Newvar (lst, c) ->
       let rec fold ctx' lst' = function
         | [] -> ctx', List.rev lst'
         | (x,c) :: lst ->
            let c = comp ctx c in
            let ctx' = add_ident x ctx'
            and lst' = (x,c) :: lst' in
            fold ctx' lst' lst
       in
       let ctx, lst = fold ctx [] lst in
       let c = comp ctx c in
       Syntax.Newvar (lst, c)

    | Input.Assign (x, e) ->
       begin match index x ctx with
         | None -> error ~loc (UnknownIdentifier x)
         | Some k ->
            let e = comp ctx e in
            Syntax.Assign (k, e)
       end

    | Input.Lim (x, e) ->
       let ctx = add_ident x ctx in
       let e = comp ctx e in
       Syntax.Lim (x, e)
  in
  let c = comp' ctx c in
  Location.locate ~loc c


let rec toplevel ctx {Location.data=c; Location.loc=loc} =

let toplevel' ctx = function

    | Input.TopDo c ->
       let c = comp ctx c in
       ctx, Syntax.TopDo c

    | Input.TopFunction (f, xts, c) ->
       let c = comp (add_args xts ctx) c
       and xts = List.map (fun (x, t) -> (x, valty t)) xts in
       let ctx = add_fun f ctx in
       ctx, Syntax.TopFunction (f, xts, c)

    | Input.TopExternal (f, s, ft) ->
       let ctx = add_fun f ctx in
       let ft = funty ft in
       ctx, Syntax.TopExternal (f, s, ft)

    | Input.TopLoad fn ->
       let ctx, cmds = load ctx fn in
       ctx, Syntax.TopFile cmds

    | Input.TopPrecision p ->
       ctx, Syntax.TopPrecision (Mpz.get_int p)

  in
  let ctx, c = toplevel' ctx c in
  ctx, Location.locate ~loc c


and load ctx fn =
  let cmds = Lexer.read_file Parser.file fn in
  let ctx, cmds = List.fold_left
                    (fun (ctx,cmds) cmd ->
                      let ctx, cmd = toplevel ctx cmd in
                      (ctx, cmd::cmds))
                    (ctx,[]) cmds
  in
  let cmds = List.rev cmds in
  ctx, cmds
