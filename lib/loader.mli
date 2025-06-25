(** Type of desugaring errors. *)
type desugar_error =
  | UnknownVariable of string
  | UnknownIdentifier of string
  | UnknownIdentifier_ch of string
  | UnknownIdentifier_path of string
  | UnknownIdentifier_process of string
  | UnknownIdentifier2 of string
  | UnknownFunction of string
  | AlreadyDefined of string 
  | ForbiddenIdentifier of string
  | ArgNumMismatch of string * int * int
  | NegativeArity of int
  | OtherError of string
  | ForbiddenFresh 
  | UnintendedError 
  | WrongInputType
  | NoBindingVariable
  | WrongChannelType of string * string
  | UnstagedConst of string
  | UnstagedParamConst of string

(** Exception raised on desugaring error. *)
exception Error of desugar_error Location.located

(** [error ~loc err] raises the given runtime error. *)
val error : loc:Location.t -> desugar_error -> 'a

(** [print_error err ppf] pretty-prints a desugaring error to the formatter. *)
val print_error : desugar_error -> Format.formatter -> unit


val rabbit_ty_to_simple_ty_params : Input.rabbit_ty -> Context.simple_ty_param list

(* val process_decl_as_context : Input.decl -> Context.env -> Context.env *)

val initialize_global_context : Input.decl list -> Context.decl list * Context.env

(** Convert a rabbit type to a simple type parameter.
    @raise ConversionException if the rabbit type cannot be converted to a simple type parameter *)
val convert_rabbit_ty_to_simple_ty_param : Input.rabbit_ty -> Context.simple_ty_param

(** Convert a rabbit type to a channel type parameter.
    @raise ConversionException if the rabbit type cannot be converted to a channel type parameter *)
val convert_rabbit_ty_to_chan_ty_param : Input.rabbit_ty -> Context.chan_ty_param

(** Convert a rabbit type to a security type parameter.
    @raise ConversionException if the rabbit type cannot be converted to a security type parameter *)
val convert_rabbit_ty_to_security_ty_param : Input.rabbit_ty -> Context.security_ty_param

val load_just_parse : string -> int