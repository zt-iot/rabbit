val load : Env.t -> string -> Env.t * Typed.decl list
(** [load env fn] loads a Rabbit source file [fn], resolves names, and performs
    monomorphic type inference.

    If successful, it returns an updated environment and the list of
    declaraitons found in the code.

    The function raises an exception [Error _] when the check fails.
*)
