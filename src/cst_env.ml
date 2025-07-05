open Sets

type ident = Ident.t [@@deriving show]
type name = Name.t [@@deriving show]



type var_desc = Env.var_desc [@@deriving show]
type named_fact_desc = Env.named_fact_desc [@@deriving show]





type core_type = 
  | TChan of core_type list
  | TSimple of name * core_type list
  | TProd of core_type * core_type
[@@deriving show]


type secrecy_lvl = 
  | Public 
  | SNode of proc_set 
[@@deriving show]

type integrity_lvl = 
  | Untrusted 
  | INode of proc_set
[@@deriving show]

type core_security_type = core_type * (secrecy_lvl * integrity_lvl) [@@deriving show]


type function_param_type = 
  | CParamCore of core_security_type
  | CParamPoly of name
[@@deriving show]



type desc =

  | SimpleTypeDef of name list (* simple type declaration *)
  | Var of var_desc
  | ExtFun of int (** external function with arity *)
  | ExtConst (** external function with arity = 0, ex.  function true 0 *)
  | ExtSyscall of int (** external system call with arity *)
  | Const of bool (* with param or not *)
  | Channel of bool (* with param or not *) * ident (* channel type *)
  | Attack

  (* all these four constructors represents the <y> in `type <x> : <y>` *)
  | ProcTypeDef
  | FilesysTypeDef

  | ChanTypeDef of core_security_type list
  | SecurityTypeDef of name * core_security_type list
  

  | Function of int (** function with definition and arity *)
  | Process (* a process template, not to be confused with a process type (ProcessTypeDef) *)
[@@deriving show]




type t = {
  vars : (Ident.t * desc) list;
  facts : (Name.ident * (named_fact_desc * int option)) list ref
  (** Fact names with descriptions and arities. Arities can be unknown
      if [delete e.S] first appear than [new x := S(args) in c]
      and [let xi := e.S in c]
  *)
} [@@deriving show]