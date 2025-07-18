open Sets

type ident = Ident.t [@@deriving show]
type name = Name.t [@@deriving show]



type var_desc = Env.var_desc [@@deriving show]
type named_fact_desc = Env.named_fact_desc [@@deriving show]


type secrecy_lvl = 
  | S_Ignore (* Means: Ignore this secrecy level when type-checking *)
  | Public 
  | SNode of proc_ty_set 
[@@deriving show]

type integrity_lvl = 
  | I_Ignore (* Means: "Ignore this integrity level when type-checking"  *)
  | Untrusted
  | INode of proc_ty_set
[@@deriving show]

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
[@@deriving show]

(* contructing a CFP_Poly with secrecy and integrity information should be illegal, but there is 
no way to enforce this requirement with specific constructors *)
and core_security_function_param = core_function_param * (secrecy_lvl * integrity_lvl)


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




type desc =
  | SimpleTypeDef of name list (* simple type declaration *)
  | Var of var_desc
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