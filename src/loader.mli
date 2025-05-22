(** Conversion from concrete syntax to abstract syntax.
    This module handles the loading and desugaring of Rabbit programs.
    It converts input syntax into abstract syntax while maintaining context and type information. *)

include Sig.ERROR

(** Initial state for loading and desugaring *)
val process_init : Context.context * Context.access_policy *
  Context.definition * Context.system list * string list * string list

(** Load and process a Rabbit source file
    @param filename The file to load
    @param context The current context
    @param policy The access policy
    @param definition The current definition
    @param systems List of systems
    @return Updated context, policy, definition, systems, and lists of strings *)
val load :
  string ->
  Context.context ->
  Context.access_policy ->
  Context.definition ->
  Context.system list ->
  Context.context * Context.access_policy *
  Context.definition * Context.system list *
  string list * string list
