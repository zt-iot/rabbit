open Sets

type ident = Ident.t [@@deriving show]
type name = Name.t [@@deriving show]



type var_desc = Env.var_desc [@@deriving show]
type named_fact_desc = Env.named_fact_desc [@@deriving show]


type secrecy_lvl = 
  | S_Ignore (* Means: Ignore this secrecy level when type-checking *)
  | Public 
  | SNode of proc_ty_set 
[@@deriving show, eq]

type integrity_lvl = 
  | I_Ignore (* Means: "Ignore this integrity level when type-checking"  *)
  | Untrusted
  | INode of proc_ty_set
[@@deriving show, eq]


(* core type WITHOUT polymorphic types *)
type core_type = 
  | TUnit 
  | TChan of core_security_type list
  | TSimple of Name.ident * core_security_type list
  | TProd of core_security_type * core_security_type
  | Dummy     (* Just to return a value when we don't care what it is *)
              (* This should never be returned in an actual implementation *)
[@@deriving show]

and core_security_type = core_type * (secrecy_lvl * integrity_lvl) [@@deriving show]

(* core type POSSIBLY WITH polymorphic types *)
type core_function_param =
  | CFP_Unit 
  | CFP_Chan of core_security_function_param list
  | CFP_Simple of Name.ident (* name of the simple type *) * core_security_function_param list (* core security types of the associated simple type *)
  | CFP_Product of core_security_function_param * core_security_function_param
  | CFP_Poly of Name.ident
  | CFP_Dummy (* Just to return a value when we don't care what it is *)
              (* This should never be returned in an actual implementation *)
[@@deriving show, eq]

(* contructing a CFP_Poly with secrecy and integrity information should be illegal, but there is 
no way to enforce this requirement with specific constructors *)
and core_security_function_param = core_function_param * (secrecy_lvl * integrity_lvl) [@@deriving show, eq]






(* Boilerplate conversion necesary for `convert_function_param_to_core(Env.FParamSecurity(...)) *)
let rec cst_to_csfp (cst : core_security_type) : core_security_function_param = 
  let (core_ty, security_info) = cst in
  let converted_core_function_param = match core_ty with
    | TUnit -> CFP_Unit
    | TChan core_security_types -> 
        CFP_Chan (List.map cst_to_csfp core_security_types)
    | TSimple (name, core_security_types) -> 
        CFP_Simple (name, List.map cst_to_csfp core_security_types)
    | TProd (cst1, cst2) -> 
        CFP_Product (cst_to_csfp cst1, cst_to_csfp cst2)
    | Dummy -> CFP_Dummy
    
  in
  (converted_core_function_param, security_info)


type syscall_member_fun_sig = 
  | DesSMFunTyped of Ident.t list * core_security_function_param list (* when types are given *)
[@@deriving show]




  
(* we have a restriction that we cannot have constructors of `Cst_env.desc` with parameter types `expr, cmd` etc., because it would create a circular dependency *)
type desc =
  | SimpleTypeDef of name list (* simple type declaration *)
  | Var of var_desc * core_security_type option  
  | ExtFun of core_security_function_param list (* equational theory function with 0 or more function parameters *)
  | ExtSyscall of core_security_function_param list (** system call with 0 or more function parameters *)
  | MemberFunc of core_security_function_param list (** member function of a process *)
  | Const of bool (* with param or not *) * core_security_type (* conversion from Env.Const fails if type is not given *)
  | ChannelDecl of bool (* with param or not *) * ident (* channel type *)
  | Attack

  (* all these four constructors represent the <y> in `type <x> : <y>` *)
  | ProcTypeDef
  | FilesysTypeDef
  | ChanTypeDef of core_security_type list
  | SecurityTypeDef of name * core_security_type list
  
  | Process (* a process template, not to be confused with a process type (ProcessTypeDef) *)
[@@deriving show]


let proc_ty_set_to_secrecy_lvl readers all_process_typs = 
  if readers = all_process_typs then 
    Public 
  else
    SNode readers  


let proc_ty_set_to_integrity_lvl providers all_process_typs = 
  if providers = all_process_typs then
    Untrusted
  else 
    INode providers


type t = {
  vars : (Ident.t * desc) list;
  facts : (Name.ident * (named_fact_desc * int option)) list ref
  (** Fact names with descriptions and arities. Arities can be unknown
      if [delete e.S] first appear than [new x := S(args) in c]
      and [let xi := e.S in c]
  *)
} [@@deriving show]

(* Methods are copy-pasted from Env.t *)
let empty () = { vars= []; facts= ref [] }

let find_opt env name =
  List.find_opt (fun (id, _desc) -> name = fst id) env.vars

let find_opt_by_id env id = List.assoc_opt id env.vars

let mem env name = find_opt env name <> None

let add env id desc = { env with vars = (id, desc) :: env.vars }

let update_fact env name v =
  let rec update rev_facts = function
    | [] -> (name, v) :: List.rev rev_facts
    | (name', _) :: facts when name = name' ->
        List.rev_append rev_facts ((name, v) :: facts)
    | f :: facts -> update (f :: rev_facts) facts
  in
  env.facts := update [] !(env.facts)

let find_fact_opt env name = List.assoc_opt name !(env.facts)
