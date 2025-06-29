type operator = string

type rabbit_typ =
  | CProc                                     (* process *)
  | CFsys                                     (* filesys *)
  | CChan of rabbit_typ list                  (* channel[t_1 + ... + t_n] *)
  | CSimple of Name.ident * rabbit_typ list   (* data name[t_1, ..., t_n] *)
  | CProd of rabbit_typ * rabbit_typ          (* ty_1 * ty_2 *)
  | CPoly of Name.ident                       (* 'a or 'b  or 'c etc. *)
  (* maybe add | CSecurity of Name.ident, I'm not sure if it belongs here *)  




and func_param_secrecy_lvl = 
  | Public
  | SecPoly of Name.ident (* non-concrete secrecy level *)
  | S of rabbit_typ
[@@deriving show]


and func_param_integrity_lvl = 
  | Untrusted 
  | IntegPoly of Name.ident (* non-concrete integrity level *)
  | I of rabbit_typ
[@@deriving show]

and security_lvl = func_param_secrecy_lvl * func_param_integrity_lvl [@@deriving show]








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

type fact = fact' Location.located

and fact' =
  | Fact of Name.ident * expr list
  | GlobalFact of Name.ident * expr list
  | ChannelFact of expr * Name.ident * expr list
  | ProcessFact of expr * Name.ident * expr list
  | EqFact of expr * expr
  | NeqFact of expr * expr
  | FileFact of expr * expr

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

type 'cmd case = fact list * 'cmd

type cmd = cmd' Location.located

and cmd' =
  | Skip
  | Sequence of cmd * cmd
  (* | Wait of fact list * cmd *)
  | Put of fact list
  | Let of Name.ident * expr * cmd
  | Assign of Name.ident option * expr
  | Case of cmd case list
  | While of cmd case list * cmd case list
  | Event of fact list
  | Return of expr
  | New of Name.ident * rabbit_typ option * (Name.ident * expr list) option * cmd
  | Get of Name.ident list * expr * Name.ident * cmd
  | Del of expr * Name.ident

type chan_arg =
  | ChanArgPlain of Name.ident
  | ChanArgParam of Name.ident
  | ChanArgParamInst of Name.ident * expr

type chan_param = ChanParam of { id : Name.ident; param : unit option; typ : Name.ident }
(** [chan_name : chan_ty] or [chan_name<> : chan_ty] *)

type pproc = pproc' Location.located

and pproc' =
  | Proc of Name.ident * chan_arg list
  | ParamProc of Name.ident * expr * chan_arg list

type proc =
  | UnboundedProc of pproc
  | BoundedProc of (Name.ident * pproc list)

type prop = prop' Location.located

and prop' =
  | PlainString of string
  | Reachability of fact list
  | Correspondence of fact * fact

type lemma = lemma' Location.located
and lemma' = Lemma of Name.ident * prop



(* Used for signature of equational theory function *)
type eq_thy_func_desc = 
  | Arity of int (* when types are not given *)
  | TypeSig of rabbit_typ list (* when types are given *)
[@@deriving show]


(* Used for signature of syscalls and member function *)
type syscall_member_fun_desc = 
  | UntypedSig of Name.ident list  (* when types are not given *)
  | TypedSig of Name.ident list * rabbit_typ list * rabbit_typ (* when types are given *)
[@@deriving show]


let syscall_member_fun_desc_to_ident_list signature = match signature with 
  | UntypedSig(ids) -> ids
  | TypedSig(ids, _, _) -> ids


type init_desc =
  | Fresh
  | Value of expr
  | Value_with_param of expr * Name.ident
  | Fresh_with_param
  

type decl = decl' Location.located

and decl' =
  
  | DeclEqThyFunc of Name.ident * eq_thy_func_desc
  | DeclEqThyEquation of expr * expr
  | DeclExtSyscall of Name.ident * syscall_member_fun_desc * cmd
  | DeclExtAttack of Name.ident * Name.ident * Name.ident list * cmd
  | DeclType of Name.ident * rabbit_typ
  | DeclAccess of Name.ident * Name.ident list * Name.ident list option
  | DeclAttack of Name.ident list * Name.ident list
  | DeclInit of Name.ident * rabbit_typ option * init_desc
  | DeclChan of chan_param
  | DeclProc of
      { id : Name.ident
      ; param : Name.ident option
      ; args : chan_param list
      ; typ : Name.ident
      ; files : (expr * Name.ident * expr) list
      ; vars : (Name.ident * rabbit_typ option * expr) list
      ; funcs : (Name.ident * syscall_member_fun_desc * cmd) list
      ; main : cmd
      }
  | DeclSys of proc list * lemma list
  | DeclLoad of string
