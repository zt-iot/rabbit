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

and fact' (*
=
  | Channel of
      { channel : Typed.expr
      ; name : Typed.name
      ; args : Typed.expr list
      } (** Channel fact [ch :: name(args)] *)
  | Out of Typed.expr (** Attacker fact: Out *)
  | In of Typed.expr (** Attacker fact: In *)
  | Plain of Typed.name * Typed.expr list
  | Eq of Typed.expr * Typed.expr
  | Neq of Typed.expr * Typed.expr
  | File of
      { path : Typed.expr
      ; contents : Typed.expr
      } (** File fact [path.contents] *)
  | Fresh of Typed.expr
  | Global of string * Typed.expr list
  | Structure of
      { name : Typed.name
      ; process : Typed.ident
      ; address : Typed.expr
      ; args : Typed.expr list
      } (** Structure fact [name(process, address, args)] *)
  | Loop of
      { mode : Typed.loop_mode
      ; process : Typed.ident
      ; index : Typed.name
      }
*)

val fact_of_typed : Typed.fact -> fact

type update =
  { register : Typed.expr option
  ; mutable_overrides : (Ident.t * Typed.expr option) list
  }
(** [None] is for $\rho$: the register value of the last command execution *)

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

type graph = edge list

val graph_cmd : (Ident.t -> Ident.t list * Typed.cmd) -> process:Ident.t -> Index.t -> Typed.cmd -> graph * Index.t * Env.t

val graph_system : Typed.decl list -> Typed.decl (* system *) -> graph list

type rule =
  { name : string
  ; role : string
  ; pre : fact list
  ; label : fact list
  ; post : fact list
  }

val graph_consts : Typed.decl list -> rule list

val check_edges : graph -> (Ident.t * bool * Env.t) Index.Map.t
