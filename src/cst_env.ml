open Sets

type ident = Ident.t [@@deriving show]
type name = Name.t [@@deriving show]



type var_desc = Env.var_desc [@@deriving show]
type named_fact_desc = Env.named_fact_desc [@@deriving show]




type secrecy_lvl = 
  | Public 
  | SNode of proc_ty_set 
[@@deriving show]

type integrity_lvl = 
  | Untrusted
  | INode of proc_ty_set
[@@deriving show]


type core_type = 
  | TChan of core_security_type list
  | TSimple of Name.ident * core_security_type list
  | TProd of core_security_type * core_security_type
[@@deriving show]


and core_security_type = core_type * (secrecy_lvl * integrity_lvl) [@@deriving show]

type core_function_param = 
  | CParamCore of core_security_type
  | CParamPoly of Name.ident
[@@deriving show]



type desc =
  | SimpleTypeDef of name list (* simple type declaration *)
  | Var of var_desc
  | ExtFun of core_function_param list (* equational theory function with 0 or more function parameters *)
  | ExtSyscall of core_function_param list (** system call with 0 ore mor function parameters *)
  | MemberFunc of core_function_param list (** member function of a process *)
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