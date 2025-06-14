module Index : sig
  type t = private (int * int) list

  val add : t -> int -> t
  val push : t -> int -> t
  val to_string : t -> string
end

type fact = Typed.fact

type update =
  { register : Typed.expr option
  ; mutable_overrides : (Ident.t * Typed.expr) list
  }

type edge =
  { source : Index.t
  ; source_env : Env.t
  ; pre : fact list
  ; update : update
  ; tag : fact list
  ; post : fact list
  ; target : Index.t
  ; target_env : Env.t
  }

type graph = edge list

val graph_cmd : process:Name.t -> Index.t -> Typed.cmd -> graph * Index.t
