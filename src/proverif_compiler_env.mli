open Rabbit_proverif_pv_parse
open Pitptree

include module type of Proverif_compiler_support

type syscall_def =
  { pv_id : ident
  ; args : T.ident list
  ; cmd : T.cmd
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

module GEnv : sig
  type t

  val create : unit -> t

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

  val structures : t -> (T.name * int) list
  val add_structure : loc:Location.t -> t -> T.name -> int -> unit

  val facts : t -> (T.name * int) list
  val add_fact : loc:Location.t -> t -> T.name -> int -> unit

  val events : t -> (string * int) list
  val add_event : loc:Location.t -> t -> T.name -> int -> unit

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
  val find_process_var : t -> T.ident -> pterm_e option
  val find_process_var_exn : loc:Location.t -> t -> T.ident -> pterm_e
  val bind_process_var : t -> T.ident -> pterm_e -> t

  val restore_process_vars :
    t ->
    (T.ident * pterm_e option) list ->
    t

  val find_local_func_def : t -> T.ident -> (T.ident list * T.cmd) option

  val process_typ_id : t -> T.ident
  val proc_type : t -> pterm_e

  val curr_syscall : t -> pterm_e
  val with_curr_syscall : t -> pterm_e -> t

  val file_channel : t -> pterm_e option

  val return_cont : t -> (pterm_e -> tprocess_e) option
  val with_process_return_cont : t -> (pterm_e -> tprocess_e) -> t
end
