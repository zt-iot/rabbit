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


(* process tempates spec and definition *)
type ctx_process_template = {
   ctx_proctmpl_id   :  Name.ident ; 
   ctx_proctmpl_param : Name.ident option ;
   ctx_proctmpl_ch   :  (bool * Name.ident * Name.ident) list ; (* true means that the channel is prametric *)
   ctx_proctmpl_ty   :  Name.ident ;
   ctx_proctmpl_var  :  Name.ident list ;
   ctx_proctmpl_func :  (Name.ident * int) list ;
}
(* declared process template name, its channel arguments, type, member variables, and
member functions and their arities *)


type def_process_template = {
   def_proctmpl_id   :  Name.ident ; 
   def_proctmpl_files : (Syntax.expr * Name.ident * Syntax.expr) list;
   def_proctmpl_var  :  (Name.ident * Syntax.expr) list ; 
   def_proctmpl_func :  (Name.ident * Name.ident list * Syntax.cmd) list ; 
   def_proctmpl_main :  Syntax.cmd   
}

let mk_ctx_proctmpl (a, f, b, c, d, e) = {ctx_proctmpl_id=a; ctx_proctmpl_param=f; ctx_proctmpl_ch=b; ctx_proctmpl_ty=c; ctx_proctmpl_var=d; ctx_proctmpl_func=e}
let mk_def_proctmpl (a, b, c, d, e) = {def_proctmpl_id=a; def_proctmpl_files=b; def_proctmpl_var=c; def_proctmpl_func=d; def_proctmpl_main=e}
let to_pair_ctx_proctmpl x = (x.ctx_proctmpl_id, x.ctx_proctmpl_param, x.ctx_proctmpl_ch, x.ctx_proctmpl_ty, x.ctx_proctmpl_var, x.ctx_proctmpl_func)
let to_pair_def_proctmpl x = (x.def_proctmpl_id, x.def_proctmpl_files, x.def_proctmpl_var, x.def_proctmpl_func, x.def_proctmpl_main)


(* ctx : context refers to the external specification of the system *)
type context = {
   ctx_ext_const  :  (Name.ident) list ; 
                     (* ext_const name *)
   ctx_ext_func   :  (Name.ident * int) list ; 
                     (* ext_func name, its arity *)
   ctx_ext_syscall:  (Name.ident * Input.func_ty_param list) list ; 
                     (* ext_syscalltruction name, its arity *)
   ctx_ext_attack :  (Name.ident * Name.ident *  Input.func_ty_param list) list ; 

   ctx_ty         :  (Name.ident * Input.ty) list ;
                     (* type name, its class *)
   ctx_const      :  Name.ident list ;
                     (* const name *)
   ctx_fsys       :  (Name.ident * Name.ident * Name.ident) list ; (*fsys name, fsys path, type *)
                     (* installed file syatem name, path, and its type *)

   ctx_ch         :  (Name.ident * Name.ident) list ;
                     (* installed channel name, method, and its type *)
   ctx_param_ch   :  (Name.ident * Name.ident) list ;
                     (* installed channel name, method, and its type *)
   ctx_param_const  :  (Name.ident) list ; 
                     (* ext_const name *)

   ctx_proctmpl   :  ctx_process_template list;
   ctx_event      :  (Name.ident * int) list ;
                     (* event predicate name, its arity *)
   ctx_fact :        (Name.ident * int * bool) list ;

   ctx_inj_fact :    (Name.ident * int) list


}

(* def : definition stores definitions of the system *)
type definition = {
   def_ext_eq  :  (Name.ident list * Syntax.expr * Syntax.expr) list ;
                  (* free variables, e1, e2  such that e1 = e2 under the free variables *)
 
   def_ext_syscall : (Name.ident *  (Input.func_ty_param * Name.ident) list * Syntax.cmd) list ;
   
   def_ext_attack  : (Name.ident * Name.ident *  (Input.func_ty_param * Name.ident) list  * Syntax.cmd) list ;

   def_const   :  (Name.ident * Syntax.expr option) list ;
                  (* const name, and its value *) 

   def_param_const   :  (Name.ident * (Name.ident * Syntax.expr) option) list ;
                  (* const name, and its value *) 


   def_fsys    :  (Name.ident * Name.ident * Syntax.expr) list ;
                  (* file system name, path, and stored value *) 
   def_proctmpl:  def_process_template list (* main fun *)
}

(* acc : access_policy records declared access policies of the system *)
type access_policy = {
   pol_access : (Name.ident * Name.ident list * Name.ident) list ;
   pol_access_all : (Name.ident * Name.ident list) list; 
   pol_attack : (Name.ident * Name.ident) list 
}

type process = {
   proc_pid       :  int ; 
   proc_name      :  string ; 
   proc_type      :  string; 
   proc_filesys   :  (Syntax.expr * Name.ident *Syntax.expr) list ;
   proc_variable  :  (Name.ident * Syntax.expr) list ; 
   proc_function  :  (Name.ident * Name.ident list * Syntax.cmd) list ;
   proc_main      :  Syntax.cmd ;
   proc_channels  :  Syntax.chan_arg list;
}

type system = {
   sys_ctx : context ; 
   sys_def : definition ;
   sys_pol : access_policy ;
   sys_proc : process list ;
   sys_param_proc : (process list) list ;
   sys_lemma : Syntax.lemma list ;
}

type local_context = {
                     lctx_chan : Name.ident list ; 

                     lctx_param_chan : Name.ident list ; 

                     lctx_path : Name.ident list ;

                     lctx_process : Name.ident list ; 

                     lctx_loc_var : (Name.ident) list ; 

                     lctx_top_var : (Name.ident) list ; 

                     lctx_meta_var : (Name.ident) list ; 

                     lctx_func : (Name.ident * int) list ;
                     
                     lctx_param : Name.ident option ;
                     }

type local_definition ={ldef_var : (Name.ident * Syntax.expr) list ; ldef_func : (Name.ident * (Name.ident list) * Syntax.cmd) list }

(** finding the frame number and the de brujin index of the given bariable *)
let find_index f l =
   let j = snd (List.fold_right (fun a (i, j) -> let j = if f a && j < 0 then i else j in (i+1, j)) l (0,-1) ) in 
   if j < 0 then None else Some (List.length l - 1 - j)


(** ctx related functions *)
(* membership checks *)
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

let ctx_check_param_const ctx o = 
   List.exists (fun s -> s = o) ctx.ctx_param_const


let ctx_check_fsys ctx o = 
   List.exists (fun (s, _, _) -> s = o) ctx.ctx_fsys
let ctx_check_ch ctx o = 
   List.exists (fun (s, _) -> s = o) ctx.ctx_ch

let ctx_check_param_ch ctx o =
   List.exists (fun (s, _) -> s = o) ctx.ctx_param_ch

let ctx_check_proctmpl ctx o = 
   List.exists (fun x -> x.ctx_proctmpl_id = o) ctx.ctx_proctmpl
let ctx_check_event ctx eid = 
   List.exists (fun (s, _) -> s = eid) ctx.ctx_event
let ctx_check_fact ctx id = 
   List.exists (fun (s, _, _) -> s = id) ctx.ctx_fact
let ctx_check_ext_syscall ctx eid = 
   List.exists (fun (s, _) -> s = eid) ctx.ctx_ext_syscall
let ctx_check_ext_attack ctx eid = 
   List.exists (fun (s, _, _) -> s = eid) ctx.ctx_ext_attack
let ctx_check_inj_fact ctx id = 
   List.exists (fun (s, _) -> s = id) ctx.ctx_inj_fact
   
(* get access *)
let ctx_get_event_arity ~loc ctx eid =
   if ctx_check_event ctx eid then 
   let (_, k) = List.find (fun (s, _) -> s = eid) ctx.ctx_event in k
   else error ~loc (UnknownIdentifier eid)

let ctx_get_ext_syscall_arity ~loc ctx eid =
   if ctx_check_ext_syscall ctx eid then 
   let (_, k) = List.find (fun (s, _) -> s = eid) ctx.ctx_ext_syscall in k
   else error ~loc (UnknownIdentifier eid)

let ctx_get_ext_attack_arity ~loc ctx eid =
   if ctx_check_ext_attack ctx eid then 
   let (_, _, k) = List.find (fun (s, _, _) -> s = eid) ctx.ctx_ext_attack in k
   else error ~loc (UnknownIdentifier eid)

let ctx_get_inj_fact_arity ~loc ctx fid =
   if ctx_check_inj_fact ctx fid then 
   let (_, k) = List.find (fun (s, _) -> s = fid) ctx.ctx_inj_fact in k
   else error ~loc (UnknownIdentifier fid)
   

let ctx_get_proctmpl ctx o = 
   List.find (fun x -> x.ctx_proctmpl_id = o) ctx.ctx_proctmpl
let ctx_get_ty ~loc ctx s =
   try let (id, ty) = List.find (fun (id, _) -> id = s) ctx.ctx_ty in ty 
   with Not_found -> error ~loc (UnknownIdentifier s)

(* check *)
let ctx_check_ty_ch ctx ty =
   List.exists (fun (s, t) -> 
      if s = ty then
      match t with
      | Input.ChannelTyp(_) -> true 
      | _ -> false
      else false) ctx.ctx_ty


(* add *)
let ctx_add_ext_func ctx (f, k) = {ctx with ctx_ext_func=(f, k)::ctx.ctx_ext_func}
let ctx_add_ext_const ctx c = {ctx with ctx_ext_const=c::ctx.ctx_ext_const}
let ctx_add_ty ctx (id, c) = {ctx with ctx_ty=(id, c)::ctx.ctx_ty}
let ctx_add_const ctx id = {ctx with ctx_const=id::ctx.ctx_const}
let ctx_add_param_const ctx id = {ctx with ctx_param_const=id::ctx.ctx_param_const}
let ctx_add_fsys ctx (a, p, ty) = {ctx with ctx_fsys=(a, p, ty)::ctx.ctx_fsys}
let ctx_add_ch ctx (c, t) = {ctx with ctx_ch=(c, t)::ctx.ctx_ch}
let ctx_add_param_ch ctx (c, t) = {ctx with ctx_param_ch=(c, t)::ctx.ctx_param_ch}
let ctx_add_proctmpl ctx p = {ctx with ctx_proctmpl=p::ctx.ctx_proctmpl}
let ctx_add_event ctx (eid, k) = 
   {ctx with ctx_event=(eid,k)::ctx.ctx_event}      
let ctx_add_ext_syscall ctx (eid, k) = 
   {ctx with ctx_ext_syscall=(eid,k)::ctx.ctx_ext_syscall}      
let ctx_add_ext_attack ctx attk = 
   {ctx with ctx_ext_attack=attk::ctx.ctx_ext_attack}      

let ctx_add_fact ctx (id, k) = 
   {ctx with ctx_fact=(id,k,false)::ctx.ctx_fact}      
let ctx_add_lfact ctx (id, k) = 
   {ctx with ctx_fact=(id,k,true)::ctx.ctx_fact}      
let ctx_add_inj_fact ctx (id, k) = 
   {ctx with ctx_inj_fact=(id,k)::ctx.ctx_inj_fact}      
   
let check_fresh ctx s =
   if ctx_check_ext_func ctx s || 
      ctx_check_ext_const ctx s || 
      ctx_check_ty ctx s || 
      ctx_check_const ctx s || 
      ctx_check_fsys ctx s ||
      ctx_check_ch ctx s || 
      ctx_check_proctmpl ctx s || 
      ctx_check_ext_syscall ctx s || 
      ctx_check_ext_attack ctx s || 
      ctx_check_event ctx s ||
      ctx_check_fact ctx s || 
      ctx_check_inj_fact ctx s ||
      ctx_check_param_ch ctx s ||
      ctx_check_param_const ctx s
      then false else true 

let check_used ctx s = if (check_fresh ctx s) then false else true

let ctx_add_or_check_fact ~loc ctx (id, k) = 
   if List.exists (fun (s, _, _)->s = id) ctx.ctx_fact then 
      let (_, k', b) = List.find (fun (s, _,_) -> s = id) ctx.ctx_fact in 
      if b then error ~loc WrongInputType else if k = k' then ctx else error ~loc (ArgNumMismatch (id, k, k'))
   else
      if check_used ctx id then error ~loc (AlreadyDefined id) else ctx_add_fact ctx (id, k)

let ctx_add_or_check_lfact ~loc ctx (id, k) = 
   if List.exists (fun (s, _, _)->s = id) ctx.ctx_fact then 
      let (_, k', b) = List.find (fun (s, _, _) -> s = id) ctx.ctx_fact in 
      if not b then error ~loc WrongInputType else if k = k' then ctx else error ~loc (ArgNumMismatch (id, k, k'))
   else
      if check_used ctx id then error ~loc (AlreadyDefined id) else ctx_add_lfact ctx (id, k)

let ctx_add_or_check_inj_fact ~loc ctx (id, k) = 
   if ctx_check_inj_fact ctx id then 
      let (_, k') = List.find (fun (s,_) -> s = id) ctx.ctx_inj_fact in 
      if k = k' then ctx else error ~loc (ArgNumMismatch (id, k, k'))
   else
      if check_used ctx id then error ~loc (AlreadyDefined id) else ctx_add_inj_fact ctx (id, k)

      

(** def related functions *)
let def_add_ext_eq def x = {def with def_ext_eq=x::def.def_ext_eq}
let def_add_const def x = {def with def_const=x::def.def_const}
let def_add_param_const def x = {def with def_param_const=x::def.def_param_const}
let def_add_fsys def x = {def with def_fsys=x::def.def_fsys}
let def_add_proctmpl def pid files ldef m = 
   {def with def_proctmpl=(mk_def_proctmpl (pid, files, ldef.ldef_var, ldef.ldef_func, m))::def.def_proctmpl}

let def_add_ext_syscall def x = 
      {def with def_ext_syscall=x::def.def_ext_syscall}

let def_add_ext_attack def x = 
      {def with def_ext_attack=x::def.def_ext_attack}



let def_get_proctmpl def pid = 
   List.find (fun x -> x.def_proctmpl_id = pid) def.def_proctmpl

let def_get_const def id = 
   List.find (fun (s, _) -> s = id) def.def_const

(** pol related funcitons *)
let pol_add_access pol x = {pol with pol_access=x::pol.pol_access}
let pol_add_access_all pol x = {pol with pol_access_all=x::pol.pol_access_all}
let pol_add_attack pol x = {pol with pol_attack=x::pol.pol_attack}

let pol_get_attack_opt pol x = 
   match List.find_opt (fun (a, b) -> a = x) pol.pol_attack with
   | Some (a, b) -> Some b
   | None -> None


(** ldef and lctx related functions *)
let ldef_add_new_var ldef (v, e) = 
   {ldef with ldef_var=(v,e) ::ldef.ldef_var}

let ldef_add_new_func ldef f = 
   {ldef with ldef_func=f::ldef.ldef_func}

let lctx_check_param lctx p = 
   match lctx.lctx_param with
   | Some s -> s = p
   | _ -> false

let lctx_check_chan lctx c = 
   List.exists (fun i -> i = c) lctx.lctx_chan

let lctx_check_param_chan lctx c =
   List.exists (fun i -> i = c) lctx.lctx_param_chan

let lctx_check_path lctx c = 
   List.exists (fun i -> i = c) lctx.lctx_path

let lctx_check_process lctx c = 
   List.exists (fun i -> i = c) lctx.lctx_process


let lctx_check_var lctx v =
   List.exists (fun s -> s = v) (lctx.lctx_loc_var @ lctx.lctx_top_var @ (match lctx.lctx_param with Some s -> [s] | None -> []))
   (* List.fold_right (fun l b -> (List.exists (fun s -> s = v) l) || b) lctx.lctx_var false  *)

   (* List.fold_right (fun l b -> (List.exists (fun s -> s = v) l) || b) lctx.lctx_loc_var false  *)

let lctx_check_meta lctx v =
   List.exists (fun s -> s = v) (lctx.lctx_meta_var)

   (* List.fold_right (fun l b -> (List.exists (fun s -> s = v) l) || b) lctx.lctx_meta false  *)
(* 
let lctx_remove_var lctx v =
   let lctx_var' = List.map (fun vl -> List.find_all (fun s -> not (s = v)) vl)  lctx.lctx_var in
   {lctx with lctx_var=lctx_var'} *)

let lctx_check_func lctx f = 
   List.exists (fun (i, _) -> i = f) lctx.lctx_func 

let lctx_check_id lctx id = 
   lctx_check_var lctx id || 
   lctx_check_meta lctx id || 
   lctx_check_chan lctx id || 
   lctx_check_param_chan lctx id || 
   lctx_check_func lctx id || 
   lctx_check_path lctx id || 
   lctx_check_process lctx id 

let lctx_add_new_chan ~loc lctx c = 
   if lctx_check_id lctx c then 
      error ~loc (AlreadyDefined c)
   else {lctx with lctx_chan=c::lctx.lctx_chan}

let lctx_add_new_param_chan ~loc lctx c = 
   if lctx_check_id lctx c then 
      error ~loc (AlreadyDefined c)
   else {lctx with lctx_param_chan=c::lctx.lctx_param_chan}
   
let lctx_add_new_path ~loc lctx c = 
   if lctx_check_id lctx c  then 
      error ~loc (AlreadyDefined c)
   else {lctx with lctx_path=c::lctx.lctx_path}

let lctx_add_new_process ~loc lctx c = 
   if lctx_check_id lctx c  then 
      error ~loc (AlreadyDefined c)
   else {lctx with lctx_process=c::lctx.lctx_process}

let lctx_add_new_var ~loc lctx v = 
   if lctx_check_id lctx v  then error ~loc (AlreadyDefined v) else 
   {lctx with lctx_loc_var=v::lctx.lctx_loc_var}

let lctx_add_new_param ~loc lctx v = 
   if lctx_check_id lctx v then error ~loc (AlreadyDefined v) else 
   {lctx with lctx_param=Some v}


let lctx_add_new_loc_var ~loc lctx v = 
   if lctx_check_id lctx v  then error ~loc (AlreadyDefined v) else 
   {lctx with lctx_loc_var=v::lctx.lctx_loc_var}

let lctx_add_new_top_var ~loc lctx v = 
   if lctx_check_id lctx v  then error ~loc (AlreadyDefined v) else 
   {lctx with lctx_top_var=v::lctx.lctx_top_var}

(*    match lctx.lctx_loc_var with 
   | f::frames -> {lctx with lctx_var=(v::f)::frames}
   | _ -> error ~loc (UnintendedError)
 *)
let lctx_add_new_meta ~loc lctx v = 
   if lctx_check_id lctx v  then error ~loc (AlreadyDefined v) else 
   {lctx with lctx_meta_var=v::lctx.lctx_meta_var}
(*    match lctx.lctx_meta with 
   | f::frames -> {lctx with lctx_meta=(v::f)::frames}
   | _ -> error ~loc (UnintendedError)
 *)

(* let lctx_add_frame lctx = {lctx with lctx_var=([]::lctx.lctx_var); lctx_meta=([]::lctx.lctx_meta)} *)

(* let lctx_pop_frame ~loc lctx = 
   match lctx.lctx_var, lctx.lctx_meta with 
   | f::frames, f'::frames' -> {lctx with lctx_var=frames; lctx_meta=frames'}
   | _, _ -> error ~loc (UnintendedError)
 *)
let lctx_get_func_arity lctx f = 
   let (_, k) = List.find (fun (i, _) -> i = f) lctx.lctx_func in k

let lctx_add_new_func ~loc lctx (f, i) = 
   if lctx_check_func lctx f then error ~loc (AlreadyDefined f) else {lctx with lctx_func=(f, i)::lctx.lctx_func}

(* let lctx_get_var_index ~loc lctx v =
   match find_index (fun l -> List.exists (fun s -> s = v) l) lctx.lctx_var with
   | Some i ->
      begin let lctxi = List.nth lctx.lctx_var i in 
      match find_index (fun s -> s = v) lctxi with 
      | Some j ->
         (i,j,
            match (find_index (fun s -> s = v) (List.fold_left (fun l vl -> l @ vl) [] lctx.lctx_var)) with Some k -> k | _ -> error ~loc (UnintendedError)
         )
         (* (List.length lctx.lctx_var - i - 1, List.length lctxi - j - 1) *)
      | None -> error ~loc (UnintendedError) end
   | None -> error ~loc (UnknownIdentifier v) *)


(** Initial contexts *)
let ctx_init = 
   {ctx_ext_func = [] ; 
   ctx_ext_const = [] ; 
   ctx_ext_syscall = []; 
   ctx_ext_attack = [] ; 
   ctx_ty = [] ; 
   ctx_const = [] ; 
   ctx_fsys = [] ; 
   ctx_ch = [] ; 
   ctx_proctmpl = [] ;
   ctx_event = []; 
   ctx_fact = [];
   ctx_inj_fact = [];
   ctx_param_ch = [];
   ctx_param_const = [];
   }

let def_init = {def_ext_eq = [] ; def_const = [] ; def_ext_syscall = [] ; def_ext_attack = [] ; def_fsys=[] ; def_proctmpl = [];  def_param_const = []}

let pol_init = {pol_access = [] ; pol_access_all=[]; pol_attack = []}
(* let sys_init = {   
   sys_ctx = []; 
   sys_def = [];
   sys_pol = [];
   sys_proc =[] }
 *)
let lctx_init = {lctx_chan = []; lctx_path = []; lctx_process = []; lctx_loc_var = []; lctx_meta_var = []; lctx_top_var = []; lctx_func = [] ; lctx_param_chan = []; lctx_param = None}
(* let lctx_init = {lctx_var=[]; lctx_meta=[]} *)
let ldef_init = {ldef_var=[]; ldef_func=[]}


