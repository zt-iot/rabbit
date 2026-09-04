module T = Typed

open Rabbit_proverif_pv_parse
open Pitptree

module Error : sig
  val unsupported : loc:Location.t -> ('a, unit, string, 'b) format4 -> 'a
  val invalid_input : loc:Location.t -> ('a, unit, string, 'b) format4 -> 'a
  val internal : loc:Location.t -> ('a, unit, string, 'b) format4 -> 'a
end

val pv_ident : string -> ident
val compile_ident : T.ident -> ident
val compile_ident_kind : T.ident -> string -> ident

val bitstring_ident : ident
val channel_ident : ident
val param_data_ident : ident
val proc_t_ident : ident
val acc_data_t_ident : ident
val syscall_t_ident : ident
val access_control_table_ident : ident
val file_type_table_ident : ident
val channel_table_ident : ident
val deleted_address_table_ident : ident
val attacker_channel_ident : ident
val true_ident : ident
val false_ident : ident
val ptype_arg_ident : ident
val none_syscall_ident : ident
val precise_ident : ident
val compile_value_type : Type.type_ -> ident

val term_e : term -> term_e
val pterm_e : pterm -> pterm_e
val gterm_e : gterm -> gterm_e
val process_e : tprocess -> tprocess_e
val tquery_e : tquery -> tquery_e
val add_comment : string -> 'a * 'b * string list -> 'a * 'b * string list

val compile_name : T.name -> string -> ident
val structure_ctor_ident : T.name -> ident
val structure_addr_ident : T.name -> ident
val structure_arg_ident : T.name -> int -> ident

module Int : sig
  val to_term_e : int -> term_e
  val to_pterm_e : int -> pterm_e
  val to_gterm_e : int -> gterm_e
end
