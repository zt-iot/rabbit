type var_desc = Syntax.variable_desc =
  | Top of int
  | Loc of int
  | Meta of int
  | MetaNew of int
  | Param

type named_fact_desc =
  | Channel
  | Structure
  | Plain
  | Global

let string_of_named_fact_desc = function
  | Channel -> "channel"
  | Structure -> "struture"
  | Plain -> "plain"
  | Global -> "global"





type 'poly processed_ty = 
  | TySecurity of Ident.t (* name of the security type *) * Ident.t (* name of the corresponding simple type *) * 'poly processed_ty list (* instantiated type parameters of the simple type *)
  | TySimple of Ident.t (* name of the corresponding simple type *) * 'poly processed_ty list (* instantiated type parameters of the simple type *)
  | TyProduct of 'poly processed_ty * 'poly processed_ty
  | TyChanPlain of 'poly processed_ty list (* channel[ty_1, ..., ty_n] *)
  | TyChan of Ident.t (* name of the channel type *) 
  | TyPoly of 'poly (* this constructor is only used when 'poly is meaningful *)

(* This datatype has 0 constructors, and thus cannot be instantiated *)
type void = |

(* To encode an instantiated_ty, we declare instantiated_ty as follows, which means we can never construct `TyPoly` *)
type instantiated_ty = void processed_ty
(* for function params, we can construct `TyPoly string` *)
type function_param = string processed_ty

(* convert instantiated_ty to function_param, always succeeds *)
let rec inst_ty_to_function_param : instantiated_ty -> function_param = function
  | TySecurity (sec_ident, simple_ident, ty_params) ->
      TySecurity (sec_ident, simple_ident, List.map inst_ty_to_function_param ty_params)
  | TySimple (simple_ty_ident, ty_params) -> 
      TySimple (simple_ty_ident, List.map inst_ty_to_function_param ty_params)
  | TyProduct (t1, t2) -> 
      TyProduct (inst_ty_to_function_param t1, inst_ty_to_function_param t2)
  | TyChanPlain ty_params -> 
      TyChanPlain (List.map inst_ty_to_function_param ty_params)
  | TyChan ch_ident -> TyChan ch_ident
  (* This case is impossible, because we cannot construct members of void *)
  | TyPoly _ -> .




(* Used for signature of equational theory function *)
type eq_thy_func_desc = 
  | DesugaredArity of int (* when types are not given *)
  | DesugaredTypeSig of function_param list (* when types are given *)


(* Used for signature of syscalls and member function *)
type syscall_member_fun_sig = 
  | DesSMFunUntyped of Ident.t list  (* when types are not given *)
  | DesSMFunTyped of Ident.t list * function_param list (* when types are given *)


let syscall_member_fun_desc_to_ident_list signature = match signature with 
  (* Description Syscall Member Function *)
  | DesSMFunUntyped(ids) -> ids
  | DesSMFunTyped(ids, _) -> ids



type desc =
  (* SimpleTypeDef of <type parameter list of the simple type> *)
  | SimpleTypeDef of string list
  | Var of var_desc * instantiated_ty option
  | ExtFun of eq_thy_func_desc
  | ExtSyscall of syscall_member_fun_sig
  | Function of syscall_member_fun_sig
  | Const of bool * instantiated_ty option
  | Channel of bool (* parameterized channel or not *)* Ident.t (* corresponding channel type *)
  | Attack
  
  | ProcTypeDef
  | FilesysTypeDef 
  | ChanTypeDef of instantiated_ty list

  (* SecurityTypeDef of <name of the simple type> * <instantiated type parameter list of the simple type> *)
  | SecurityTypeDef of Ident.t * instantiated_ty list
  
  | Process


let print_desc desc ppf =
  let f = Format.fprintf in
  match desc with
  | Var (Top i, _) -> f ppf "Top %d" i
  | Var (Loc i, _) -> f ppf "Loc %d" i
  | Var (Meta i, _) -> f ppf "Meta %d" i
  | Var (MetaNew i, _) -> f ppf "MetaNew %d" i
  | Var (Param, _) -> f ppf "Param"
  | ExtFun _ -> f ppf "ExtFun"
  | ExtSyscall _ -> f ppf "ExtSyscall"
  | Const (b, _) -> f ppf "Const (param=%b)" b
  | Channel (b, id) -> f ppf "Channel (param=%b) : %t" b (Ident.print id)
  | Attack -> f ppf "Attack"
  | ProcTypeDef -> f ppf "ty process"
  | FilesysTypeDef -> f ppf "ty filesys"
  | ChanTypeDef _ -> f ppf "ty channel"
  | Function _ -> f ppf "Function"
  | Process -> f ppf "Process"

  | SimpleTypeDef _ -> f ppf "SimpleTypeDef"
  | SecurityTypeDef (_, _) -> f ppf "SecurityTypeDef"

type t = {
  vars : (Ident.t * desc) list;
  facts : (Name.ident * (named_fact_desc * int option)) list ref
  (* The fact environment is global therefore implemented as mutable *)
} 

let empty () = { vars= []; facts= ref [] }

let find_opt env name =
  List.find_opt (fun (id, _desc) -> name = fst id) env.vars

let find_opt_by_id env id = List.assoc_opt id env.vars

let mem env name = find_opt env name <> None

let add env id desc = { env with vars = (id, desc) :: env.vars }

let update_fact env name v =
  let rec update rev_facts = function
    | [] -> (name, v) :: List.rev rev_facts
    | (name', _) :: facts when name = name' ->
        List.rev_append rev_facts ((name, v) :: facts)
    | f :: facts -> update (f :: rev_facts) facts
  in
  env.facts := update [] !(env.facts)

let find_fact_opt env name = List.assoc_opt name !(env.facts)
