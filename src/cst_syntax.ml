(* Syntax to which we are converting a Rabbit program from typed.ml *)

open Sets

(* type 'desc loc_env =
  { desc : 'desc
  ; loc : Location.t
  }

let pp_loc_env pp_desc fmt { desc; loc = _ } =
  Format.fprintf fmt "{ desc = %a; env = %a }"
    pp_desc desc *)


type secrecy_lvl = 
  | S_Ignore (* Means: Ignore this secrecy level when type-checking *)
  | Public 
  | SNode of proc_ty_set 


type integrity_lvl = 
  | I_Ignore (* Means: "Ignore this integrity level when type-checking" *)
  | Untrusted
  | INode of proc_ty_set



(* core type WITHOUT polymorphic types *)
type core_type = 
  | TUnit 
  | TChan of core_security_type list
  | TSimple of Ident.t * core_security_type list
  | TProd of core_security_type * core_security_type
  | Dummy     (* Just to return a value when we don't care what it is *)
              (* This should never be returned in an actual implementation *)


and core_security_type = core_type * (secrecy_lvl * integrity_lvl)

(* core type POSSIBLY WITH polymorphic types *)
type core_function_param =
  | CFP_Unit 
  | CFP_Chan of core_security_function_param list
  | CFP_Simple of Ident.t (* name of the simple type *) * core_security_function_param list (* core security types of the associated simple type *)
  | CFP_Product of core_security_function_param * core_security_function_param
  | CFP_Poly of Ident.t


(* contructing a CFP_Poly with secrecy and integrity information should be illegal, but there is 
no way to enforce this requirement with specific constructors *)
and core_security_function_param = core_function_param * (secrecy_lvl * integrity_lvl) 



type expr = expr' * Location.t 
and expr' =
  | Ident of
      { id : Ident.t
      ; param : expr option
       (** [param= Some _] iff [desc= Const true _] *)
      }
  (** [id] or [id<e>].
      [id<e>] is only possible either for [id] of [Channel {param=true}] or [Const {param=true}] *)
  | Boolean of bool (** boolean, [true]/[false] *)
  | String of string (** string, ["hello"] *)
  | Integer of int (** integer, [42] *)
  | Float of string (** float, [4.12]. Store the string so we can correctly round later *)
  | Apply of Ident.t * expr list (** application, [f(e1,..,en)]   /  [e1 op e2] *)
  | Tuple of expr list (** tuple, [(e1,..,en)] *)
  | Unit




type fact = fact' * Location.t 
and fact' =
  | Channel of
      { channel : expr
      ; name : Name.t
      ; args : expr list
      } (** Channel fact [ch :: name(args)] *)
  | Out of expr (** Attacker fact: Out *)
  | In of expr (** Attacker fact: In *)
  | Plain of Name.t * expr list
  | Eq of expr * expr
  | Neq of expr * expr
  | File of
      { path : expr
      ; contents : expr
      } (** File fact [path.contents] *)
  | Global of string * expr list


(* Cst_synax.cmd = Typed.cmd but with an embedded Cst_env.t 
Additionally, the `New` constructor needs a core_security_type
*)
type cmd = cmd' * Location.t 
(* A Cst_syntax.case represents a single branch of a `case` or `repeat` statement *)
and case =
  { fresh : Ident.t list
  ; facts : fact list
  ; cmd : cmd
  } 

and cmd' =
  | Skip (** doing nothing *)
  | Sequence of cmd * cmd (** sequencing, c1; c2 *)
  | Put of fact list (** output, put[f1,..,fn] *)
  | Let of Ident.t * expr * cmd (** let binding, let x = e in c *)
  | Assign of Ident.t option * expr (** assignment, x := e *)
  | Case of case list (** guarded cases, case [a1s] => c1 | .. | [ans] => cn end *)
  | While of case list * case list
  (** guarded loop,
      repeat [a1s] => c1 | .. | [ans] => cn
      until [a'1s] => c'1 | .. | [a'ms] => c'm
      end
  *)
  | Event of fact list (** tag, event[T] *)
  | Return of expr (** return *)
  | New of Ident.t * core_security_type option * (Name.t * expr list) option * cmd
  (** allocation, new x := S(e1,..en) in c *)
  | Get of Ident.t list * expr * Name.t * cmd (** fetch, let x1,..,xn := e.S in c *)
  | Del of expr * Name.t (** deletion , delete e.S *)






type chan_param = Typed.chan_param 
type proc = Typed.proc 


type init_desc =
  | Value of expr (** [const n = e] *)
  | Value_with_param of Ident.t * expr (** [const n<p> = e] *)
  | Fresh (** [const fresh n] *)
  | Fresh_with_param (** [const fresh n<>] *)




type process = process' * Location.t 
and process' =
  | Process of
      { id : Ident.t
      ; param : Ident.t option
      ; args : chan_param list
      ; typ : Ident.t
      ; files : (expr * Ident.t * expr) list
      ; vars : (Ident.t * expr) list (* typing information is not necessary, because we can infer the type from the expression *)
      ; funcs : (Ident.t * (Ident.t * core_security_function_param) list * cmd) list
      ; main : cmd
      }





type t_env_typ = 
  (* A core security type *)
  | CST of core_security_type
  | SimpleTypeDef of string list
  | SecurityTypeDef of string (* name of simple type upon which the security type is based *) * core_security_type list (* type parameters *)
  | ChanTypeDef of core_security_type list
  | ProcTypeDef 
  | FilesysTypeDef

  | EqThyFunc of core_security_function_param list 
  | MemberFunc of core_security_function_param list * cmd
  | Syscall of core_security_function_param list * cmd




(* a Map from Ident.t to core_security_type *)
(* because we Map from Ident.t (which is unique in the entire program), we should not encounter any problems with name shadowing *)
type typing_env = t_env_typ Maps.IdentMap.t


(* a core Rabbit program is a list of processes and an initial typing environment for each process *)
type core_rabbit_prog = (process * typing_env) list




