(** Conversion from concrete syntax to abstract syntax.
    This module handles the loading and desugaring of Rabbit programs.
    It converts input syntax into abstract syntax while maintaining context and type information. *)

type desugar_error =
  | UnknownVariable of string
  (** Raised when a variable is used but not defined in the current scope *)
  | UnknownIdentifier of string
  (** Raised when an identifier is used but not defined *)
  | UnknownIdentifier_ch of string
  (** Raised when a channel identifier is used but not defined *)
  | UnknownIdentifier_path of string
  (** Raised when a path identifier is used but not defined *)
  | UnknownIdentifier_process of string
  (** Raised when a process identifier is used but not defined *)
  | UnknownIdentifier2 of string
  (** Internal error for unknown identifiers *)
  | UnknownFunction of string
  (** Raised when a function is used but not defined *)
  | AlreadyDefined of string
  (** Raised when trying to redefine an identifier *)
  | ForbiddenIdentifier of string
  (** Raised when using a reserved identifier *)
  | ArgNumMismatch of string * int * int
  (** Raised when the number of arguments doesn't match the expected number *)
  | NegativeArity of int
  (** Raised when a negative arity is specified *)
  | OtherError of string
  (** Generic error with a custom message *)
  | ForbiddenFresh
  (** Raised when using the reserved 'fresh' identifier *)
  | UnintendedError
  (** Internal error indicating unexpected behavior *)
  | WrongInputType
  (** Raised when input type doesn't match expected type *)
  | NoBindingVariable
  (** Raised when trying to use a variable without binding *)
  | WrongChannelType of string * string
  (** Raised when channel type doesn't match expected type *)
  | UnstagedConst of string
  (** Internal error for unstaged constants *)
  | UnstagedParamConst of string
  (** Internal error for unstaged parameter constants *)

include Sig.ERROR with type error := desugar_error

(** Initial state for loading and desugaring *)
val process_init : Context.context * Context.access_policy *
  Context.definition * Context.system list * (string list * string list)

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
  (string list * string list)
