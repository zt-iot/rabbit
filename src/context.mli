type desugar_error =
  | UnknownIdentifier of string
  | UnknownFunction of string
  | AlreadyDefined of string
  | ForbiddenIdentifier of string
  | ArgNumMismatch of string * int * int
  | NegativeArity of int
  | ForbiddenFresh
  | WrongInputType

include Sig.ERROR with type error := desugar_error

type ctx_process_template =
  { ctx_proctmpl_id : Name.ident
  ; ctx_proctmpl_param : Name.ident option
  ; ctx_proctmpl_ch : (bool * Name.ident * Name.ident) list
  ; ctx_proctmpl_ty : Name.ident
  ; ctx_proctmpl_var : Name.ident list
  ; ctx_proctmpl_func : (Name.ident * int) list
  }

type def_process_template =
  { def_proctmpl_id : Name.ident
  ; def_proctmpl_files : (Syntax.expr * Name.ident * Syntax.expr) list
  ; def_proctmpl_var : (Name.ident * Syntax.expr) list
  ; def_proctmpl_func : (Name.ident * Name.ident list * Syntax.cmd) list
  ; def_proctmpl_main : Syntax.cmd
  }

type context =
  { ctx_ext_const : Name.ident list
  ; ctx_ext_func : (Name.ident * int) list
  ; ctx_ext_syscall : (Name.ident * Input.arg_type list) list
  ; ctx_ext_attack : (Name.ident * Name.ident * Input.arg_type list) list
  ; ctx_ty : (Name.ident * Input.type_class) list
  ; ctx_const : Name.ident list
  ; ctx_fsys : (Name.ident * Name.ident * Name.ident) list
  ; ctx_ch : (Name.ident * Name.ident) list
  ; ctx_param_ch : (Name.ident * Name.ident) list
  ; ctx_param_const : Name.ident list
  ; ctx_proctmpl : ctx_process_template list
  ; ctx_event : (Name.ident * int) list
  ; ctx_fact : (Name.ident * int * bool) list
  ; ctx_inj_fact : (Name.ident * int) list
  }

type definition =
  { def_ext_eq : (Name.ident list * Syntax.expr * Syntax.expr) list
  ; def_ext_syscall : (Name.ident * (Input.arg_type * Name.ident) list * Syntax.cmd) list
  ; def_ext_attack :
      (Name.ident * Name.ident * (Input.arg_type * Name.ident) list * Syntax.cmd) list
  ; def_const : (Name.ident * Syntax.expr option) list
  ; def_param_const : (Name.ident * (Name.ident * Syntax.expr) option) list
  ; def_fsys : (Name.ident * Name.ident * Syntax.expr) list
  ; def_proctmpl : def_process_template list
  }

type access_policy =
  { pol_access : (Name.ident * Name.ident list * Name.ident) list
  ; pol_access_all : (Name.ident * Name.ident list) list
  ; pol_attack : (Name.ident * Name.ident) list
  }

type process =
  { proc_pid : int
  ; proc_name : string
  ; proc_type : string
  ; proc_filesys : (Syntax.expr * Name.ident * Syntax.expr) list
  ; proc_variable : (Name.ident * Syntax.expr) list
  ; proc_function : (Name.ident * Name.ident list * Syntax.cmd) list
  ; proc_main : Syntax.cmd
  ; proc_channels : Syntax.chan_arg list
  }

type system =
  { sys_ctx : context
  ; sys_def : definition
  ; sys_pol : access_policy
  ; sys_proc : process list
  ; sys_param_proc : process list list
  ; sys_lemma : Syntax.lemma list
  }

type local_context =
  { lctx_chan : Name.ident list
  ; lctx_param_chan : Name.ident list
  ; lctx_path : Name.ident list
  ; lctx_process : Name.ident list
  ; lctx_loc_var : Name.ident list
  ; lctx_top_var : Name.ident list
  ; lctx_meta_var : Name.ident list
  ; lctx_func : (Name.ident * int) list
  ; lctx_param : Name.ident option
  }

type local_definition =
  { ldef_var : (Name.ident * Syntax.expr) list
  ; ldef_func : (Name.ident * Name.ident list * Syntax.cmd) list
  }

val find_index : ('a -> bool) -> 'a list -> int option
val ctx_check_ext_func : context -> Name.ident -> bool
val ctx_check_ext_func_and_arity : context -> Name.ident * int -> bool
val ctx_check_ext_const : context -> Name.ident -> bool
val ctx_check_ty : context -> Name.ident -> bool
val ctx_check_const : context -> Name.ident -> bool
val ctx_check_param_const : context -> Name.ident -> bool
val ctx_check_fsys : context -> Name.ident -> bool
val ctx_check_ch : context -> Name.ident -> bool
val ctx_check_param_ch : context -> Name.ident -> bool
val ctx_check_proctmpl : context -> Name.ident -> bool
val ctx_check_event : context -> Name.ident -> bool
val ctx_check_fact : context -> Name.ident -> bool
val ctx_check_ext_syscall : context -> Name.ident -> bool
val ctx_check_ext_attack : context -> Name.ident -> bool
val ctx_check_inj_fact : context -> Name.ident -> bool
val ctx_get_event_arity : loc:Location.t -> context -> Name.ident -> int

val ctx_get_ext_syscall_arity
  :  loc:Location.t
  -> context
  -> Name.ident
  -> Input.arg_type list

val ctx_get_ext_attack_arity
  :  loc:Location.t
  -> context
  -> Name.ident
  -> Input.arg_type list

val ctx_get_inj_fact_arity : loc:Location.t -> context -> Name.ident -> int
val ctx_get_proctmpl : context -> Name.ident -> ctx_process_template
val ctx_get_ty : loc:Location.t -> context -> Name.ident -> Input.type_class
val ctx_check_ty_ch : context -> Name.ident -> bool
val ctx_add_ext_func : context -> Name.ident * int -> context
val ctx_add_ext_const : context -> Name.ident -> context
val ctx_add_ty : context -> Name.ident * Input.type_class -> context
val ctx_add_const : context -> Name.ident -> context
val ctx_add_param_const : context -> Name.ident -> context
val ctx_add_fsys : context -> Name.ident * Name.ident * Name.ident -> context
val ctx_add_ch : context -> Name.ident * Name.ident -> context
val ctx_add_param_ch : context -> Name.ident * Name.ident -> context
val ctx_add_proctmpl : context -> ctx_process_template -> context
val ctx_add_event : context -> Name.ident * int -> context
val ctx_add_ext_syscall : context -> Name.ident * Input.arg_type list -> context

val ctx_add_ext_attack
  :  context
  -> Name.ident * Name.ident * Input.arg_type list
  -> context

val ctx_add_fact : context -> Name.ident * int -> context
val ctx_add_lfact : context -> Name.ident * int -> context
val ctx_add_inj_fact : context -> Name.ident * int -> context
val check_fresh : context -> Name.ident -> bool
val check_used : context -> Name.ident -> bool
val ctx_add_or_check_fact : loc:Location.t -> context -> Name.ident * int -> context
val ctx_add_or_check_lfact : loc:Location.t -> context -> Name.ident * int -> context
val ctx_add_or_check_inj_fact : loc:Location.t -> context -> Name.ident * int -> context

val def_add_ext_eq
  :  definition
  -> Name.ident list * Syntax.expr * Syntax.expr
  -> definition

val def_add_const : definition -> Name.ident * Syntax.expr option -> definition

val def_add_param_const
  :  definition
  -> Name.ident * (Name.ident * Syntax.expr) option
  -> definition

val def_add_fsys : definition -> Name.ident * Name.ident * Syntax.expr -> definition

val def_add_proctmpl
  :  definition
  -> Name.ident
  -> (Syntax.expr * Name.ident * Syntax.expr) list
  -> local_definition
  -> Syntax.cmd
  -> definition

val def_add_ext_syscall
  :  definition
  -> Name.ident * (Input.arg_type * Name.ident) list * Syntax.cmd
  -> definition

val def_add_ext_attack
  :  definition
  -> Name.ident * Name.ident * (Input.arg_type * Name.ident) list * Syntax.cmd
  -> definition

val def_get_proctmpl : definition -> Name.ident -> def_process_template
val def_get_const : definition -> Name.ident -> Name.ident * Syntax.expr option

val pol_add_access
  :  access_policy
  -> Name.ident * Name.ident list * Name.ident
  -> access_policy

val pol_add_access_all : access_policy -> Name.ident * Name.ident list -> access_policy
val pol_add_attack : access_policy -> Name.ident * Name.ident -> access_policy
val pol_get_attack_opt : access_policy -> Name.ident -> Name.ident option
val ldef_add_new_var : local_definition -> Name.ident * Syntax.expr -> local_definition

val ldef_add_new_func
  :  local_definition
  -> Name.ident * Name.ident list * Syntax.cmd
  -> local_definition

val lctx_check_param : local_context -> Name.ident -> bool
val lctx_check_chan : local_context -> Name.ident -> bool
val lctx_check_param_chan : local_context -> Name.ident -> bool
val lctx_check_path : local_context -> Name.ident -> bool
val lctx_check_process : local_context -> Name.ident -> bool
val lctx_check_var : local_context -> Name.ident -> bool
val lctx_check_meta : local_context -> Name.ident -> bool
val lctx_check_func : local_context -> Name.ident -> bool
val lctx_check_id : local_context -> Name.ident -> bool
val lctx_add_new_chan : loc:Location.t -> local_context -> Name.ident -> local_context

val lctx_add_new_param_chan
  :  loc:Location.t
  -> local_context
  -> Name.ident
  -> local_context

val lctx_add_new_path : loc:Location.t -> local_context -> Name.ident -> local_context
val lctx_add_new_process : loc:Location.t -> local_context -> Name.ident -> local_context
val lctx_add_new_var : loc:Location.t -> local_context -> Name.ident -> local_context
val lctx_add_new_param : loc:Location.t -> local_context -> Name.ident -> local_context
val lctx_add_new_loc_var : loc:Location.t -> local_context -> Name.ident -> local_context
val lctx_add_new_top_var : loc:Location.t -> local_context -> Name.ident -> local_context
val lctx_add_new_meta : loc:Location.t -> local_context -> Name.ident -> local_context
val lctx_get_func_arity : local_context -> Name.ident -> int

val lctx_add_new_func
  :  loc:Location.t
  -> local_context
  -> Name.ident * int
  -> local_context

val ctx_init : context
val def_init : definition
val pol_init : access_policy
val lctx_init : local_context
val ldef_init : local_definition
