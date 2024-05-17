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

type chan = {
   transfer : Syntax.transfer ; 
   ty : Name.ident
}

type fl = {
   path : string ; 
   data : Syntax.expr ; 
   ty : Name.ident 
}

type filesys = {
   files : Name.ident * Name.ident * 
}

type context = {
   
   prim_fun : (Name.ident * Syntax.datatype list * Syntax.datatype) list ; 

   ty : (Name.ident * Syntax.type_class) list ;
   
   const : (Name.ident * Syntax.datatype) list ;

   files : (Name.ident * fl list) list ; 

   chans : (Name.ident * chan) list 
}

type definition = {
   prim_eq : (Syntax.expr * Syntax.expr) list ;
   consts : (Name.ident * expr) list
}

type access_policy = {
   accesses : (Name.ident * Name.ident * Syntax.access_class list) list ;
   attacks : (Name.ident * Syntax.attack_class) list ; 
}


(** Initial context *)
let idents_init = {
   prim_fun = [] ;
   ty = [] ;
   const = [] ;
   files = [] ;
   chans = [] ;
}

let acp_init = {
   accesses = [] ; 
   attacks = []
}

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

let process_decl ctx pol def {Location.data=c; Location.loc=loc} =

   let process_decl' ctx pol def = function
   | DeclPrimFun (f, doms, codom) -> verify_fresh ctx f; (add_prim ctx (f, doms, codom), pol, def)
   | DeclPrimEq (e1, e2) -> if infer_type ctx e1 = infer_type ctx e2 
                            then (add_prim_eq (e1, e2), pol, def) else error ~loc (UnknownIdentifier "")
   | DecType (id, c) -> verify_fresh id ctx ; (add_ty ctx (id, c), pol, def)
   | DeclAccess(s, t, al) -> 
      let tys = verify_and_get_ty ctx s in
      let tyt = verify_and_get_ty ctx f t in

      let validity_check pol' a =
         begin
         match tys, tyt, a with
         | CProc, CFsys, CRead -> add_access pol' s t a
         | CProc, CFsys, CWrite -> add_access pol' s t a
         | CProc, CChan, CSend -> add_access pol' s t a
         | CProc, CChan, CRecv -> add_access pol' s t a
         | _, _, _ -> error ~loc (UnknownIdentifier "")
         end
      in 

      let rec adds l pol' =
      begin
      match l with
      | a :: l -> adds l (validity_check pol' a)
      | [] -> pol'
      end
      in 

      (ctx, adds al pol, def)

   | DeclAttack (t, al) -> 
      let tyt = verify_and_get_ty ctx f t in

      let validity_check pol' a =
         begin
         match tyt, a with
         | CProc, CEaves -> add_attack pol' t a
         | CProc, CTamper -> add_attack pol' t a
         | CFsys, CEaves -> add_attack pol' t a
         | CFsys, CTamper -> add_attack pol' t a
         | CChan, CEaves -> add_attack pol' t a
         | CChan, CTamper -> add_attack pol' t a
         | CChan, CDrop -> add_attack pol' t a
         | _, _-> error ~loc (UnknownIdentifier "")
         end
      in 
      
      let rec adds l pol' =
      begin
      match l with
      | a :: l -> adds l (validity_check pol' a)
      | [] -> pol'
      end
      in 


      type attack_class = CEaves |  CTamper | CDrop 

      let rec adds l pol' =
      begin
      match l with
      | a :: l -> adds l (validity_check pol' a)
      | [] -> pol'
      end
      in 

      (ctx, adds al pol, def)

  | DeclInit (id, e) -> 
      verify_fresh ctx id ; let ty = infer_type ctx e in ctx_add_const ctx id ty, pol, def_add_cosnt def id e 

   of Name.ident * expr
  | DeclFsys of Name.ident * (fpath list)
  | DeclChan of Name.ident * chan_class * Name.ident
  | DeclProc of Name.ident * (Name.ident list) * Name.ident * 
                ((Name.ident * expr) list) * 
                (Name.ident * (Name.ident list) * stmt list * Name.ident) list* 
                stmt list


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
