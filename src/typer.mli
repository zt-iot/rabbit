include Sig.ERROR

val load : Env.t -> string -> Env.t * Typed.decl list
(** [load env fn] loads a Rabbit code of file [fn] and checks the names
    occur in the code.

    If successful, it returns an updated environment and the list of
    declaraitons found in the code.

    The function raises an exception [Error _] when the check fails.
*)
