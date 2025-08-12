(* Syntax to which we are converting a Rabbit program from typed.ml *)

open Sets

exception CstSyntaxException of string

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





(* This datatype has 0 constructors, and thus cannot be instantiated *)
type void = |


type 'poly abstract_core_ty = 
  | TUnit 
  | TChan of ('poly abstract_core_security_ty) list
  | TSimple of Ident.t * ('poly abstract_core_security_ty) list 
  | TProd of 'poly abstract_core_security_ty * 'poly abstract_core_security_ty
  | TPoly of 'poly (* this constructor is only used when 'poly is meaningful *)

and 'poly abstract_core_security_ty = 'poly abstract_core_ty * (secrecy_lvl * integrity_lvl)

type core_ty = void abstract_core_ty
type core_function_param = string abstract_core_ty

type core_security_ty = core_ty * (secrecy_lvl * integrity_lvl)
type core_security_function_param = core_function_param * (secrecy_lvl * integrity_lvl)


(* converting a core security type to a core security function param always succeeds *)
let rec core_ty_to_f_param : core_ty -> core_function_param = function
  | TUnit -> TUnit
  | TChan ty_params -> TChan (List.map (core_sec_ty_to_core_sec_f_param) ty_params)
  | TSimple (simple_ty_ident, ty_params) -> TSimple (simple_ty_ident, (List.map (core_sec_ty_to_core_sec_f_param) ty_params))
  | TProd (ty1, ty2) -> TProd (core_sec_ty_to_core_sec_f_param ty1, core_sec_ty_to_core_sec_f_param ty2)
  (* this case is impossible, because we cannot construct members of void *)
  | TPoly _ -> .

and core_sec_ty_to_core_sec_f_param : core_security_ty -> core_security_function_param 
  = fun (ty, lvls) -> (core_ty_to_f_param ty, lvls)

(* converting a core security function param to a core securit type fails if it contains any polymorphic *)
let rec core_f_param_to_core_ty : core_function_param -> core_ty = function 
  | TUnit -> TUnit
  | TChan ty_params -> TChan (List.map (core_sec_f_param_to_core_sec_ty) ty_params)
  | TSimple (simple_ty_ident, ty_params) -> TSimple (simple_ty_ident, (List.map core_sec_f_param_to_core_sec_ty ty_params))
  | TProd (ty1, ty2) -> TProd (core_sec_f_param_to_core_sec_ty ty1, core_sec_f_param_to_core_sec_ty ty2)
  | TPoly _ -> raise (CstSyntaxException "Currently, a core security function param with polymorphic types cannot be converted to a core security type")

and core_sec_f_param_to_core_sec_ty : core_security_function_param -> core_security_ty 
 = fun (ty, lvls) -> (core_f_param_to_core_ty ty, lvls)


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
Additionally, the `New` constructor needs a core_security_ty
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
  | New of Ident.t * core_security_ty option * (Name.t * expr list) option * cmd
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
  | CST of core_security_ty
  | SimpleTypeDef of string list
  | SecurityTypeDef of string (* name of simple type upon which the security type is based *) * core_security_ty list (* type parameters *)
  | ChanTypeDef of core_security_ty list
  | ProcTypeDef 
  | FilesysTypeDef

  | EqThyFunc of core_security_function_param list 
  | MemberFunc of core_security_function_param list * cmd
  | Syscall of core_security_function_param list * cmd




(* a Map from Ident.t to core_security_ty *)
(* because we Map from Ident.t (which is unique in the entire program), we should not encounter any problems with name shadowing *)
type typing_env = t_env_typ Maps.IdentMap.t


(* a core Rabbit program is a list of processes and an initial typing environment for each process *)
type core_rabbit_prog = (process * typing_env) list




