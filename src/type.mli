type type_ =
  | TValue
  | TChannel
  | TParameter
  | TVar of type_var ref

and type_var =
  | Unbound of int
  | Link of type_

type callable_type =
  { argument_types : type_ list
  ; result_type : type_
  }

exception Cannot_unify of type_ * type_

val fresh_type : unit -> type_
val repr : type_ -> type_
val unify : type_ -> type_ -> unit
val default_type : type_ -> type_
val print_type : type_ -> Format.formatter -> unit
