type operator = string

(* SecrecyLvl ::= public | <Ident>.S *)
type secrecy_lvl = 
  | Public 
  | S_proc of Name.ident

(* IntegrityLvl ::= untrusted | <Ident>.I *)
type integrity_lvl = 
  | Untrusted 
  | I_proc of Name.ident

type type_class = KindProc | KindFSys | KindChan
type arg_type = TyValue | TyChannel | TyProcess | TyPath

type security_lvl = secrecy_lvl * integrity_lvl

type keykind = 
  | Sym
  | Enc
  | Dec
  | Sig 
  | Chk

type typ = 
  | SecurityLvl of security_lvl
  | Pair of typ * typ
  | Channel of security_lvl * typ * typ
  | Key of security_lvl * keykind * typ
  | Process of security_lvl * typ option
  | Function of security_lvl * typ list * typ
  | PolymorphicTyp of Name.ident
  | PolymorphicSecrecyLvl of Name.ident
  | PolymorphicIntegrityLvl of Name.ident
  | PolymorphicSecurityLvl of Name.ident
  | TyString





type expr = expr' Location.located
and expr' =
  | Var of Name.ident
  | Boolean of bool
  | String of string  
  (* | Integer of Mpzf.t *)
  | Integer of int
  | Float of string (* store the string so we can correctly round later *)
  | Apply of operator * expr list
  | Tuple of expr list

type fact = fact' Location.located
and fact' = 
  | Fact of Name.ident * expr list
  | GlobalFact of Name.ident * expr list
  | ChannelFact of Name.ident * Name.ident * expr list
  | PathFact of Name.ident * Name.ident * expr list
  | ProcessFact of Name.ident * Name.ident * expr list
  | ResFact of int * expr list (* 0: eq 1: neq *)
  (* | InjFact of  *)

type cmd = cmd' Location.located
and cmd' = 
  | Skip
  | Sequence of cmd * cmd
  (* | Wait of fact list * cmd *)
  | Put of fact list
  | Let of Name.ident * expr * cmd 
  | Assign of Name.ident option * expr
  | Case of (fact list * cmd) list
  | While of (fact list * cmd) list * (fact list * cmd) list
  | Event of fact list
  | Return of expr

  | New of Name.ident * Name.ident * expr list * cmd 
  | Get of Name.ident list * expr * Name.ident * cmd
  | Del of expr * Name.ident

type proc = proc' Location.located
and proc' =
  | Proc of Name.ident * (Name.ident list) * Name.ident option

type prop = prop' Location.located
and prop' =
  | PlainString of string
  | Reachability of fact list
  | Correspondence of fact * fact

type lemma = lemma' Location.located
and lemma' =
  | Lemma of Name.ident * prop 

type decl = decl' Location.located
and decl' =
  | DeclExtFun of Name.ident * int
  | DeclExtEq of expr * expr
  | DeclExtSyscall of Name.ident * (arg_type * Name.ident) list * cmd
  | DeclExtAttack of Name.ident * Name.ident * (arg_type * Name.ident) list * cmd
  | DeclTypeKind of Name.ident * type_class
  | DeclType of Name.ident * typ
  | DeclAccess of Name.ident * Name.ident list * Name.ident list option
  | DeclAttack of Name.ident list * Name.ident list
  | DeclInit of Name.ident * expr option
  | DeclFsys of Name.ident * ((Name.ident * expr * Name.ident) list)
  | DeclChan of Name.ident * Name.ident
  | DeclProc of Name.ident * (Name.ident * Name.ident) list * Name.ident * 
                ((Name.ident * expr) list) * 
                (Name.ident * (Name.ident list) * cmd) list * cmd
  | DeclSys of proc list * lemma list 
  | DeclLoad of string

