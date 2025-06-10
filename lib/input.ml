type operator = string

(* type type_class = CProc | CFsys | CChan *)

(* Rabbit expression language *)
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

  | Param of Name.ident * expr

type fact = fact' Location.located
and fact' = 
  | Fact of Name.ident * expr list
  | GlobalFact of Name.ident * expr list
  | ChannelFact of expr * Name.ident * expr list
  | ProcessFact of expr * Name.ident * expr list
  | ResFact of int * expr list (* 0: eq 1: neq 3 : FILE*)
  (* | InjFact of  *)

(* Rabbit command language *)
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

(* system instantiation *)
type chan_arg =
  | ChanArgPlain of Name.ident
  | ChanArgParam of Name.ident
  | ChanArgParamInst of Name.ident * expr

(* system instantiation *)
type pproc = pproc' Location.located
and pproc' =
  | Proc of Name.ident * (chan_arg list)
  | ParamProc of Name.ident * expr * (chan_arg list)

(* system instantiation *)
type proc = 
| UnboundedProc of pproc 
| BoundedProc of (Name.ident * pproc list)

(* system instantiation *)
type prop = prop' Location.located
and prop' =
  | PlainString of string
  | Reachability of fact list
  | Correspondence of fact * fact



(* system instantiation *)
type lemma = lemma' Location.located
and lemma' =
  | Lemma of Name.ident * prop 

(* A Rabbit type, which can be: 
- Unit
- A Rabbit simple type 
- A Rabbit security type
- A Rabbit channel type
- A product of any Rabbit types
*)
type ty = 
  | Unit                                         (* used for syscalls that do not have a return type *)
  | ChannelTyp of ty list                        (* channel[t_1 + ... t_n] *)
  | ProdTyp of ty * ty                           
  | Typ of Name.ident * ty_param list            (* <Name.ident>[<ty_param>*] *)

and ty_param =  (* Why the separate constructor for ty_param? Because I want using a polymorphic type as the "root" type to be a syntax error *)
  | ParamPolyType of Name.ident
  | ParamTyp of ty


type func_param_secrecy_lvl = 
  | Public
  | SecPoly of Name.ident (* non-concrete secrecy level *)
  | S of func_ty_param

and func_param_integrity_lvl = 
  | Untrusted 
  | IntegPoly of Name.ident (* non-concrete integrity level *)
  | I of func_ty_param

(* function parameter of an equational theory function or system call *)
and func_ty_param = 
  | FuncParamPolyType of Name.ident (* 'a, 'b, 'n etc. *)
  | FuncParamTyp of ty * func_param_secrecy_lvl option * func_param_integrity_lvl option (* ty or ty@(s, i) or ty@(Public, i) or ty@(S(t), i) or ty@(s, Untrusted) etc. *)
  


type decl = decl' Location.located
and decl' =
  | DeclSimpleTyp of ty (* data <simple_ty> *)

  | DeclProcType of Name.ident
  | DeclFileType of Name.ident

  | DeclTyp of Name.ident * ty (* type sec_ty : simple_ty or type ch_ty : channel[<type>+] *)

  | DeclEqThyFunc of Name.ident * func_ty_param list
  | DeclEqThyEquation of expr * expr
  

  | DeclExtSyscall of Name.ident * (Name.ident * func_ty_param) list * func_ty_param * cmd
  
  (* attack <attack_name> on <syscall_name> (<syscall_arg>* )  *)
  | DeclExtAttack of Name.ident * Name.ident * Name.ident list * cmd

  (* process "Name.ident" is allowed access to resources of "Name.ident list" with system calls of "Name.ident list option" *)
  | DeclAccess of Name.ident * Name.ident list * Name.ident list option

  | DeclAllowAttack of Name.ident list * Name.ident list
  
  (* TODO unify these *)
  | DeclConst of Name.ident * ty * expr option
  | DeclParamConst of Name.ident * ty * (Name.ident * expr) option

  (* TODO unify these *)
  | DeclChanInstantiation of Name.ident * ty
  | DeclParamChanInstantiation of Name.ident * ty


  (*process <name>(ch_1 : ty_1, ..., ch_n : ty_n) : proc_ty  {
    file path_i : file_ty_i = data_i
    var x_i : ty_i = e_i

    (function <name> : <func_ty_param>* <cmd>)*
    main {
      <cmd>
    } 
  } *)
  (* bool: whether ch_i is parameterized channel type or not *)
  (* TODO unify these *)
  | DeclProc of Name.ident * (bool * Name.ident * ty) list * Name.ident * 
                ((expr * Name.ident * expr) list) * 
                ((Name.ident * ty * expr) list) * 
                (Name.ident * (func_ty_param list) * cmd) list * cmd
  | DeclParamProc of Name.ident * Name.ident * (bool * Name.ident * ty) list * Name.ident * 
                ((expr * Name.ident * expr) list) * 
                ((Name.ident * ty * expr) list) * 
                (Name.ident * (func_ty_param list) * cmd) list * cmd



  | DeclSys of proc list * lemma list 
  

  | DeclLoad of string

  
[@@deriving show]