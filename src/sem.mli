module Index : sig
  type t = private (int * int) list

  val compare : t -> t -> int

  val zero : t

  (** [add i n] for $i + n$ *)
  val add : t -> int -> t

  (** [push i n] for $i_n$ *)
  val push : t -> int -> t

  val to_string : t -> string

  module Map : Map.S with type key = t
end

type fact = fact' Typed.loc_env

and fact'

val string_of_fact : fact -> string

val fact_of_typed : Typed.fact -> fact

(** State update.

    - [None] is for $\rho$: the register value of the last command execution
    - [mutable_overrides] only list the updated fields:
*)
type update =
  { register : Typed.expr option
  ; mutable_overrides : (Ident.t * Typed.expr option) list
  ; drops : Ident.t list
  }

val string_of_update : update -> string

type edge =
  { id : Ident.t
  ; source : Index.t
  ; source_env : Env.t
  ; pre : fact list
  ; update : update
  ; tag : fact list
  ; post : fact list
  ; target : Index.t
  ; target_env : Env.t
  }

val check_edge_invariants : edge -> unit

type graph = edge list

type signature =
  { functions : (Ident.t * int) list
  ; equations : (Typed.expr * Typed.expr) list
  }
type model =
  { id : Ident.t
  ; edges : edge list }

type tamarin =
  { signature : signature
  ; models : model list
  ; constants : (Ident.t * Typed.init_desc) list
  ; lemmas : (Ident.t * Typed.lemma) list
  }

val models_system : Typed.decl list -> Typed.decl (* system *) -> model list

type rule =
  { name : string
  ; role : string
  ; pre : fact list
  ; label : fact list
  ; post : fact list
  }

val const_rules : Typed.decl list -> rule list

val check_edges : graph -> (Ident.t * bool * Env.t) Index.Map.t

val tamarin_of_decls : Typed.decl list -> tamarin
