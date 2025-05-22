(** Conversion from concrete syntax to abstract syntax.
    This module handles the loading and desugaring of Rabbit programs.
    It converts input syntax into abstract syntax while maintaining context and type information. *)

include Sig.ERROR

type env =
  { context : Context.context
  ; access_policy : Context.access_policy
  ; definition : Context.definition
  ; system : Context.system list
  ; used_idents : string list
  ; used_strings : string list
  }

(** Initial state for loading and desugaring *)
val process_init : env

(** Load and process a Rabbit source file
    @param filename The file to load
    @param env The current environment
    @return Updated environment *)
val load : string -> env -> env
