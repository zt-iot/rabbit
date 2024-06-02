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

type process = {
   proc_pid : int ; 
   proc_name : string ; 
   proc_attack : Input.attack_class list ; 
   proc_channel : (Name.ident * Input.chan_class * Input.access_class list * Input.attack_class list) list;
   proc_file : (Name.ident * Syntax.expr * Input.access_class list * Input.attack_class list) list ;
   proc_variable : (Name.ident * Syntax.expr) list ; 
   proc_function : (Name.ident * Name.ident list * Syntax.stmt list * Syntax.indexed_var ) list ;
   proc_main : Syntax.stmt list 
}

type system = {
   sys_process : process list 
}
(* 
type system = {
   sys_proc : (int * (* process id *) Name.ident * (* name of the process template *)
               Input.attack_class list  * (* possible attackes *)
               (Name.ident * Input.chan_class * Input.access_class list * Input.attack_class list) list * (* connected channels: name, channel class, accesses, and attacks *)
               (Name.ident * Syntax.expr * Input.access_class list * Input.attack_class list) list * (* paths in the file system, its initial value, access, and attacks *)
               (Name.ident * Syntax.expr) list * (* process's internal variables and their initial values *)
               (Name.ident * Name.ident list * Syntax.stmt list * Syntax.indexed_var ) list * (* process's internal variables and their initial values *)
               Syntax.stmt list 
             ) list 
   (* ;  *)
   (* sys_requirements : Syntax.prop *)
} *)

(** Initial context *)
let ctx_init = {ctx_ext_func = [] ; ctx_ext_const = [] ; ctx_ext_ins = []; ctx_ty = [] ; ctx_const = [] ; ctx_fsys = [] ; ctx_chan = [] ; ctx_proc = [] ; ctx_event = []}
let def_init = {def_ext_eq = [] ; def_const = [] ; def_ext_ins = [] ; def_fsys=[] ; def_proc = []}
let pol_init = {pol_access = [] ; pol_attack = []}
let sys_init = []


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

let ctx_get_ty ~loc ctx s =
   try let (id, ty) = List.find (fun (id, _) -> id = s) ctx.ctx_ty in ty 
   with Not_found -> error ~loc (UnknownIdentifier s)

