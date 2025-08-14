(* Syntax to which we are converting a Rabbit program from typed.ml *)

exception CstSyntaxException of string

let raise_cst_syntax_exception_with_location msg loc = 
  Location.print loc Format.std_formatter;
  Format.pp_print_newline Format.std_formatter ();
  raise (CstSyntaxException msg)

(* type 'desc loc_env =
  { desc : 'desc
  ; loc : Location.t
  }

let pp_loc_env pp_desc fmt { desc; loc = _ } =
  Format.fprintf fmt "{ desc = %a; env = %a }"
    pp_desc desc *)



(* This datatype has 0 constructors, and thus cannot be instantiated *)
type void = | [@@deriving eq]


type 'poly abstract_core_ty = 
  | TUnit 
  | TChan of ('poly abstract_core_security_ty) list
  | TSimple of Ident.t * ('poly abstract_core_security_ty) list 
  | TProd of 'poly abstract_core_security_ty * 'poly abstract_core_security_ty
  | TPoly of 'poly (* this constructor is only used when 'poly is meaningful *)
[@@deriving eq]

and 'poly abstract_core_security_ty = 'poly abstract_core_ty * (Lattice_util.secrecy_lvl * Lattice_util.integrity_lvl) [@@deriving eq]

type core_ty = void abstract_core_ty [@@deriving eq]
type core_function_param = string abstract_core_ty [@@deriving eq]

type core_security_ty = core_ty * (Lattice_util.secrecy_lvl * Lattice_util.integrity_lvl)
type core_security_function_param = core_function_param * (Lattice_util.secrecy_lvl * Lattice_util.integrity_lvl)




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


 (* Whether two `core_security_ty`'s hold the same data, ignoring any (Lattice_util.secrecy_lvl * Lattice_util.integrity_lvl) *)
let rec equals_datatype (ty1 : core_security_ty) (ty2 : core_security_ty) (loc : Location.t) : bool =
  let (ct1, _) = ty1 in
  let (ct2, _) = ty2 in
  match ct1, ct2 with
  | TUnit, TUnit -> true
  | TChan lst1, TChan lst2 -> 
      let same_length = (List.length lst1 = List.length lst2) in 
      if not same_length then
        (raise_cst_syntax_exception_with_location "channels do not have the same amount of type parameters" loc);
      let same_typ_params = List.for_all2 (fun typ1 typ2 -> equals_datatype typ1 typ2 loc) lst1 lst2 in 
      same_length && same_typ_params
  | TSimple (id1, lst1), TSimple (id2, lst2) ->
      let same_type = Ident.equal id1 id2 in 
      let same_length = (List.length lst1 = List.length lst2) in 
      if not same_length then
        (raise_cst_syntax_exception_with_location "simple types do not have the same amount of type parameters" loc);
      let same_typ_params = List.for_all2 (fun typ1 typ2 -> equals_datatype typ1 typ2 loc) lst1 lst2 in 
      same_type && same_length && same_typ_params
  | TProd (a1, b1), TProd (a2, b2) ->
      equals_datatype a1 a2 loc && equals_datatype b1 b2 loc
  | _, _ -> false




let is_subtype (secrecy_lattice : Lattice_util.cst_access_policy) (integrity_lattice : Lattice_util.cst_access_policy) 
  (t1 : core_security_ty) (t2 : core_security_ty) (loc : Location.t) : bool = 
  (* for t1 to be a subtype of t2, it must hold that: 
    1.) t1 is of the same datatype as t2, and:
    2.) t1's secrecy level is smaller than or equal to the secrecy level of t2, and:
    3.) t1's integrity level is smaller than or equal to the integrity level of t2
  *)

  let (_, (t1_secrecy, t1_integrity)) = t1 in 
  let (_, (t2_secrecy, t2_integrity)) = t2 in 
  let same_datatype = equals_datatype t1 t2 loc in 
  let secrecy_cnd = begin match (t1, t2) with 
    (* For channel types, we currently do not care about secrecy levels *)
    | ((TChan _, _), (TChan _, _)) -> true 
    | _ -> Lattice_util.leq_secrecy secrecy_lattice t1_secrecy t2_secrecy 
  end in 
  let integrity_cnd = begin match (t1, t2) with 
    (* For channel types, we currently do not care about integrity levels *)
    | ((TChan _, _), (TChan _, _)) -> true
    | _ -> Lattice_util.leq_integrity integrity_lattice t1_integrity t2_integrity
  end in 
  same_datatype && secrecy_cnd && integrity_cnd


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






type core_process_param = 
  { proc_param_id : Ident.t ; proc_param_typ : core_security_function_param} 

type proc = Typed.proc 


type init_desc =
  | Value of expr (** [const n = e] *)
  | Value_with_param of Ident.t * expr (** [const n<p> = e] *)
  | Fresh (** [const fresh n] *)
  | Fresh_with_param (** [const fresh n<>] *)



type t_env_typ = 
  | CST of core_security_ty

  | EqThyFunc of core_security_function_param list 
  (* (<ident> : <param_type>)* <ret_ty> <cmd> *)
  | Syscall of (Ident.t * core_security_function_param) list * core_security_function_param 
      * cmd
  | MemberFunc of (Ident.t * core_security_function_param) list * core_security_function_param 
      * cmd
  
  (* preparation for when we might want to add mobile processes to Rabbit *)
  | Process of
      { id : Ident.t
      ; param : Ident.t option
      ; process_params : (Ident.t * core_security_function_param) list
      ; typ : Ident.t
      ; files : (expr * Ident.t * expr) list
      ; vars : (Ident.t * expr) list 
      (* * (<ident> : <param_type>)* <ret_ty> <cmd> *) 
      ; funcs : (Ident.t * (Ident.t * core_security_function_param) list
        * core_security_function_param * cmd) list
      ; main : cmd
      }

(* a Map from Ident.t to core_security_ty *)
(* because we Map from Ident.t (which is unique in the entire program), we should not encounter any problems with name shadowing *)
type typing_env = t_env_typ Maps.IdentMap.t

(* Use with care, because this returns the first Ident.t which matches the given string, which can cause name shadowing problems if used incorrectly *)
let t_env_lookup_by_name (str : string) (t_env : typing_env) : Ident.t = 
  let binding = Maps.SecurityTypeMap.find_first (fun key -> (Ident.string_part key) == str) t_env in 
  (fst binding)


let coerce_tenv_typ (typ : t_env_typ) (loc : Location.t) : core_security_ty = 
  match typ with 
    | CST (ty) -> ty 
    | _ -> (raise_cst_syntax_exception_with_location "this type is expected to be a core security type, but it unexpectedly is of a function or process type" loc)



(* a 'system' is a list of (<process_ident>, <process_parameter>* ) *)
type system = (Ident.t * Ident.t list) list * Location.t


(* a core rabbit program is a single system declaration and an initial typing environment which contains all global constants *)
type core_rabbit_prog = system * typing_env







