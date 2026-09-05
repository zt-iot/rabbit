open Rabbit_proverif_pv_parse
open Pitptree

include module type of Proverif_compiler_support

type syscall_def =
  { pv_id : ident
  ; args : T.ident list
  ; cmd : T.cmd
  ; passive : bool
  }

type attack_def =
  { syscall : T.ident
  ; args : T.ident list
  ; cmd : T.cmd
  }

type allow_entry =
  { rabbit_process_type : T.ident
  ; rabbit_target_type : T.ident
  ; rabbit_syscall : T.ident option
  ; pv_process_type : ident
  ; pv_target_type : ident
  ; pv_syscall : ident option
  }

type event_kind =
  | Global
  | Plain

val compile_event_name : T.name -> event_kind -> ident

type comparison_event_kind =
  | Equality
  | Inequality

val compile_comparison_event_name : comparison_event_kind -> ident

module GEnv : sig
  type t

  val create : Env.t -> t

  val tyenv : t -> Env.t

  val strings : t -> (string * ident) list
  val fresh_string_ident : t -> string -> ident
  val add_decl_strings : t -> T.decl -> unit

  val integers : t -> (int * ident) list
  val fresh_integer_ident : t -> int -> ident

  val parameters : t -> (string * ident) list
  val fresh_parameter_ident : t -> T.expr -> ident

  val add_param_init : t -> T.ident -> T.ident -> T.expr -> unit
  val find_param_init : t -> T.ident -> (T.ident * T.expr) option

  val syscalls : t -> (T.ident * syscall_def) list
  val find_syscall_def : t -> T.ident -> syscall_def option

  val add_syscall_def :
    loc:Location.t ->
    passive:bool ->
    t ->
    T.ident ->
    T.ident list ->
    T.cmd ->
    unit

  val add_attack_def : loc:Location.t -> t -> T.ident -> attack_def -> unit

  val find_allowed_attacks :
    loc:Location.t ->
    t ->
    process_typ_id:T.ident ->
    syscall_id:T.ident ->
    attack_def list

  val add_allowed_attacks : t -> T.ident -> T.ident list -> unit

  val allow_entries : t -> allow_entry list
  val add_allow_entry : t -> allow_entry -> unit

  val find_process_type : loc:Location.t -> t -> T.ident -> ident
  val add_process_type : loc:Location.t -> t -> T.ident -> T.ident -> unit

  val channel_facts : t -> (T.name * Type.type_ list) list
  val structure_facts : t -> (T.name * Type.type_ list) list

  val events : t -> (T.name * (event_kind * Type.type_ list)) list
  val add_event : loc:Location.t -> t -> T.name -> event_kind -> Type.type_ list -> unit

  val comparison_events : t -> (comparison_event_kind * Type.type_) list
  val add_comparison_event : loc:Location.t -> t -> comparison_event_kind -> Type.type_ -> unit

  val top_process : t -> tprocess_e option
  val set_top_process : t -> tprocess_e -> unit
end

module PEnv : sig
  type t

  val create_process_env :
    local_func_defs:(T.ident * (T.ident list * T.cmd)) list ->
    process_typ_id:T.ident ->
    proc_type:pterm_e ->
    curr_syscall:pterm_e ->
    file_channel:pterm_e option ->
    t

  val bindings : t -> (T.ident * pterm_e) list
  val binding_type_exn : loc:Location.t -> t -> T.ident -> Type.type_
  val find_process_var : t -> T.ident -> pterm_e option
  val find_process_var_exn : loc:Location.t -> t -> T.ident -> pterm_e
  val define_process_var : t -> T.ident -> Type.type_ -> pterm_e -> t
  val assign_process_var : t -> T.ident -> pterm_e -> t
  val remove_process_vars : t -> T.ident list -> t

  val find_local_func_def : t -> T.ident -> (T.ident list * T.cmd) option

  val process_typ_id : t -> T.ident
  val proc_type : t -> pterm_e

  val curr_syscall : t -> pterm_e
  val with_curr_syscall : t -> pterm_e -> t

  val file_channel : t -> pterm_e option

  val result : t -> pterm_e
  val result_type : t -> Type.type_
  val with_result : t -> Type.type_ -> pterm_e -> t
end
