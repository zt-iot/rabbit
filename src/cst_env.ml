(* type ident = Ident.t
type name = Name.t



type var_desc = Syntax.variable_desc =
  | Top of int
  | Loc of int
  | Meta of int
  | MetaNew of int
  | Param




type core_type = 
  | TChan of core_type list
  | TSimple of name * core_type list
  | TProd of core_type * core_type


type secrecy_lvl = 
  | Public 
  | SNode of proc_set 

type integrity_lvl = 
  | Untrusted
  | INode of proc_set

type core_security_type = core_type * (secrecy_lvl * integrity_lvl)


type function_param_type = 
  | CParamCore of core_security_type
  | CParamPoly of name



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




type t = {
  vars : (Ident.t * desc) list;
  facts : (Name.ident * (named_fact_desc * int option)) list ref
  (** Fact names with descriptions and arities. Arities can be unknown
      if [delete e.S] first appear than [new x := S(args) in c]
      and [let xi := e.S in c]
  *)
} *)