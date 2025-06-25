type operator = string [@@deriving show]

(* type type_class = CProc | CFsys | CChan *)


(* A Rabbit type, which can be: 
- Unit
- A Rabbit simple type 
- A Rabbit security type
- A Rabbit channel type
- A product of any Rabbit types
*)



type plain_ty = 
  | Unit                                                (* used for syscalls that do not have a return type *)
  | PlainTyp of Name.ident * rabbit_ty list
  | PolyTyp of Name.ident                              (* 'a, 'b, 'k etc.*)
  | ChannelTyp of rabbit_ty list                        (* channel[t_1 + ... + t_n] *)
  | ProdTyp of rabbit_ty * rabbit_ty
[@@deriving show]

and func_param_secrecy_lvl = 
  | Public
  | SecPoly of Name.ident (* non-concrete secrecy level *)
  | S of rabbit_ty
[@@deriving show]


and func_param_integrity_lvl = 
  | Untrusted 
  | IntegPoly of Name.ident (* non-concrete integrity level *)
  | I of rabbit_ty
[@@deriving show]

and security_lvl = func_param_secrecy_lvl * func_param_integrity_lvl [@@deriving show]

and rabbit_ty = 
  | RabbitTyp of plain_ty * security_lvl option 
[@@deriving show]


(* Rabbit expression language *)
type expr = expr' Location.located [@@deriving show]
and expr' =
  | Var of Name.ident
  | Boolean of bool
  | String of string  
  (* | Integer of Mpzf.t *)
  | Integer of int
  | Float of string (* store the string so we can correctly round later *)
  | Apply of operator * expr list
  | Tuple of expr list
  | Param of Name.ident * expr (* parametric Rabbit NOT "function parameter" *)
[@@deriving show]

(* 
let vars_of_expr e =
  let module NS = Name.Set in
  let rec aux s (e : expr) =
    match e.data with
    | Var id -> NS.add id s
    | Boolean _ | String _ | Integer _ | Float _ -> s
    | Apply (_, es) | Tuple es -> List.fold_left aux s es
    | Param (id, e) -> NS.add id (aux s e)
  in
  aux NS.empty e
;;
*)


type fact = fact' Location.located [@@deriving show]
and fact' = 
  | Fact of Name.ident * expr list
  | GlobalFact of Name.ident * expr list
  | ChannelFact of expr * Name.ident * expr list
  | ProcessFact of expr * Name.ident * expr list
  | EqFact of expr * expr
  | NeqFact of expr * expr
  | FileFact of expr * expr
[@@deriving show]


(* 
let vars_of_fact (fact : fact) =
  let module NS = Name.Set in
  match fact.data with
  | Fact (_, es) -> List.fold_left (fun s e -> NS.union s (vars_of_expr e)) NS.empty es
  | GlobalFact (_, es) ->
      List.fold_left (fun s e -> NS.union s (vars_of_expr e)) NS.empty es
  | ChannelFact (e, _, es) | ProcessFact (e, _, es) ->
      List.fold_left (fun s e -> NS.union s (vars_of_expr e)) NS.empty (e :: es)
  | EqFact (e1, e2) | NeqFact (e1, e2) | FileFact (e1, e2) ->
      NS.union (vars_of_expr e1) (vars_of_expr e2)
;;

let vars_of_facts facts =
  List.fold_left (fun s fact -> Name.Set.union s (vars_of_fact fact)) Name.Set.empty facts
;;
*)

  (* | InjFact of  *)


type 'cmd case = fact list * 'cmd [@@deriving show]

(* Rabbit command language *)
type cmd = cmd' Location.located [@@deriving show]
and cmd' = 
  | Skip
  | Sequence of cmd * cmd
  (* | Wait of fact list * cmd *)
  | Put of fact list
  | Let of Name.ident * rabbit_ty option * expr * cmd 
  | Assign of Name.ident option * expr
  | Case of cmd case list
  | While of cmd case list * cmd case list
  | Event of fact list
  | Return of expr

  | New of Name.ident * rabbit_ty option * (Name.ident * expr list) option * cmd 
  (* Get only takes a single `rabbit_ty option` because it will be a product of smaller types, where each smaller type is the type of expression i *)
  | Get of Name.ident list * rabbit_ty option * expr * Name.ident * cmd
  | Del of expr * Name.ident
[@@deriving show]


(* system instantiation *)
type chan_arg = 
  | ChanArgPlain of Name.ident
  | ChanArgParam of Name.ident
  | ChanArgParamInst of Name.ident * expr
[@@deriving show]


(* system instantiation *)
type pproc = pproc' Location.located
and pproc' =
  | Proc of Name.ident * (chan_arg list)
  | ParamProc of Name.ident * expr * (chan_arg list)
[@@deriving show]


(* system instantiation *)
type proc = 
  | UnboundedProc of pproc 
  | BoundedProc of (Name.ident * pproc list)
[@@deriving show]


(* system instantiation *)
type prop = prop' Location.located [@@deriving show]
and prop' =
  | PlainString of string
  | Reachability of fact list
  | Correspondence of fact * fact
[@@deriving show]




(* system instantiation *)
type lemma = lemma' Location.located [@@deriving show]
and lemma' =
  | Lemma of Name.ident * prop 
[@@deriving show]

  


(* Used for signature of equational theory function *)
type eq_thy_func_desc = 
  | Arity of int (* when types are not given *)
  | TypeSig of rabbit_ty list (* when types are given *)
[@@deriving show]

(* Used for signature of syscalls and member function *)
type syscall_member_fun_desc = 
  | UntypedSig of Name.ident list  (* when types are not given *)
  | TypedSig of Name.ident list * rabbit_ty list * rabbit_ty (* when types are given *)
[@@deriving show]

type const_desc = 
  | Fresh 
  | Value of expr
  | Value_with_param of expr * Name.ident
  | Fresh_with_param
[@@deriving show]


type chan_param = ChanParam of { id : Name.ident; param : unit option; typ : rabbit_ty } [@@deriving show]


type decl = decl' Location.located [@@deriving show]
and decl' =
  | DeclSimpleTyp of rabbit_ty (* data <simple_ty> *)

  | DeclProcType of Name.ident (* type client_t : process *)
  | DeclFileType of Name.ident (* type readonly_t : filesys *)

  | DeclTyp of Name.ident * rabbit_ty (* type sec_ty : simple_ty or type ch_ty : channel[<type>+] *)

  | DeclEqThyFunc of Name.ident * eq_thy_func_desc
  | DeclEqThyEquation of expr * expr
  
  (* used both for syscalls and passive attacks *)
  | DeclExtSyscall of Name.ident * syscall_member_fun_desc * cmd 
  
  (* attack <attack_name> on <syscall_name> (<syscall_arg>* ) { <cmd> } *)
  | DeclActiveAttack of Name.ident * Name.ident * Name.ident list * cmd

  (* process "Name.ident" is allowed access to resources of "Name.ident list" with system calls of "Name.ident list option" *)
  | DeclAccess of Name.ident * Name.ident list * Name.ident list option

  | DeclAllowAttack of Name.ident list * Name.ident list


  | DeclConst of  Name.ident * const_desc * rabbit_ty option

  
  (* channel <name> <param yes/no> : <type> *)
  | DeclChanInstantiation of chan_param


  (*process <name>(ch_1 : ty_1, ..., ch_n : ty_n) : proc_ty  {
    file path_i : file_ty_i = data_i
    var x_i : ty_i = e_i

    (function <name> : <func_ty_param>* <cmd>)*
    main {
      <cmd>
    } 
  } *)
  (* bool: whether ch_i is parameterized channel type or not *)

  | DeclProc of 
    {
      id : Name.ident
      ; is_process_parametric : Name.ident option (* Whether process is a parameterized process or not *)
      ; params : chan_param list (* Parameters (ch_1 : ty_1, ch_2<> : ty_2 ..., ch_n : ty_n) of a process*)
      ; proc_typ : Name.ident 
      ; file_stmts : (expr * Name.ident * expr) list
      ; let_stmts : (Name.ident * expr * rabbit_ty option) list
      ; funcs : (Name.ident * syscall_member_fun_desc * cmd) list
      ; main_func : cmd
    }


  | DeclSys of proc list * lemma list 
  

  | DeclLoad of string
[@@deriving show]
