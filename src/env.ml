type var_desc = Syntax.variable_desc =
  | Top of int
  | Loc of int
  | Meta of int
  | MetaNew of int
  | Param
[@@deriving show]

type named_fact_desc =
  | Channel
  | Structure
  | Plain
  | Global
[@@deriving show]

let string_of_named_fact_desc = function
  | Channel -> "channel"
  | Structure -> "struture"
  | Plain -> "plain"
  | Global -> "global"



(* an instantiated_ty is used to type expression terms in Rabbit *)
type instantiated_ty = 
  | TySecurity of Name.ident (* name of the security type *) * Name.ident (* name of the corresponding simple type *) * instantiated_ty list (* instantiated type parameters of the simple type *)
  | TySimple of Name.ident (* name of the corresponding simple type *) * instantiated_ty list (* instantiated type parameters of the simple type *)
  | TyProduct of instantiated_ty * instantiated_ty
  | TyChan of instantiated_ty list
[@@deriving show]


(* a function_param is used to type equational theory functions/syscalls/member functions *)
type function_param = 
  | FParamSecurity of Name.ident (* name of security type *) * Name.ident (* name of simple type *) * instantiated_ty list (* instantiated type parameters of the simple type *)
  | FParamSimple of Name.ident * function_param list
  | FParamProduct of function_param * function_param
  | FParamPoly of Name.ident 
  | FParamChannel of function_param list
[@@deriving show]


(* Boilerplate conversion from instantiated_ty to function_param, which is required by 
convert_rabbit_typ_to_env_function_param(CSimpleOrSecurity(...)) *)
let rec instantiated_ty_to_function_param (ty : instantiated_ty) : function_param =
  match ty with
  | TySecurity (sec_ty_name, simple_ty_name, params) ->
      FParamSecurity (sec_ty_name, simple_ty_name, params)

  | TySimple (simple_ty_name, params) ->
      let param_fparams = List.map instantiated_ty_to_function_param params in
      FParamSimple (simple_ty_name, param_fparams)

  | TyProduct (ty1, ty2) ->
      let f1 = instantiated_ty_to_function_param ty1 in
      let f2 = instantiated_ty_to_function_param ty2 in
      FParamProduct (f1, f2)

  | TyChan params ->
      let param_fparams = List.map instantiated_ty_to_function_param params in
      FParamChannel param_fparams


(* Used for signature of equational theory function *)
type eq_thy_func_desc = 
  | DesugaredArity of int (* when types are not given *)
  | DesugaredTypeSig of function_param list (* when types are given *)
[@@deriving show]


(* Used for signature of syscalls and member function *)
type syscall_member_fun_sig = 
  | DesSMFunUntyped of Ident.t list  (* when types are not given *)
  | DesSMFunTyped of Ident.t list * function_param list (* when types are given *)
[@@deriving show]

let syscall_member_fun_desc_to_ident_list signature = match signature with 
  (* Description Syscall Member Function *)
  | DesSMFunUntyped(ids) -> ids
  | DesSMFunTyped(ids, _) -> ids



type desc =
  (* SimpleTypeDef of <type parameter list of the simple type> *)
  | SimpleTypeDef of Name.ident list
  | Var of var_desc * instantiated_ty option
  | ExtFun of eq_thy_func_desc
  | ExtSyscall of syscall_member_fun_sig
  | Function of syscall_member_fun_sig
  | Const of bool * instantiated_ty option
  | Channel of bool * Ident.t
  | Attack
  
  | ProcTypeDef
  | FilesysTypeDef 
  | ChanTypeDef of instantiated_ty list

  (* SecurityTypeDef of <name of the simple type> * <instantiated type parameter list of the simple type> *)
  | SecurityTypeDef of Name.ident * instantiated_ty list
  
  | Process
[@@deriving show]

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
} [@@deriving show]

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
