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

(* Typed.fact' + internal facts *)
and fact' =
  | Channel of
      { channel : Typed.expr
      ; name : Name.t
      ; args : Typed.expr list
      } (** Channel fact [ch :: name(args)] *)
  | Out of Typed.expr (** Attacker fact: Out *)
  | In of Typed.expr (** Attacker fact: In *)
  | Plain of Name.t * Typed.expr list
  | Eq of Typed.expr * Typed.expr
  | Neq of Typed.expr * Typed.expr
  | File of
      { path : Typed.expr
      ; contents : Typed.expr
      } (** File fact [path.contents] *)
  | Global of Name.t * Typed.expr list

  (* New additions at Sem level *)

  | Fresh of Ident.t
  | Structure of
      { name : Name.t
      ; proc_id : Subst.proc_id
      ; address : Typed.expr
      ; args : Typed.expr list
      } (** Structure fact [name(process, address, args)] *)
  | Loop of
      { mode : Typed.loop_mode
      ; proc_id : Subst.proc_id
      ; param : Subst.param_id option
      ; index : Index.t
      }
  | Access of
      { proc_id: Subst.proc_id (** process id *)
      ; param : Subst.param_id option
      ; channel: Typed.expr (** channel or file *)
      ; syscall: Ident.t option (** system call performs this access *)
      }

val string_of_fact : fact -> string

val fact_of_typed : Typed.fact -> fact

(** State update.

    - [None] is for $\rho$: the register value of the last command execution
    - [mutable_overrides] only list the updated fields:
*)
type update_desc =
  | New of Typed.expr option (* None: \rho *)
  | Update of Typed.expr option (* None: \rho *)
  | Drop

type update =
  { register : Typed.expr option (* None: \rho *)
  ; items : (Ident.t * update_desc) list
  }


val string_of_update : update -> string

type edge_id = private Ident.t

val edge_id : Ident.t -> edge_id

type edge =
  { id : edge_id
  ; source : Index.t
  ; source_env : Env.t
  ; source_vars : Ident.t list
  ; pre : fact list
  ; update : update
  ; tag : fact list
  ; post : fact list
  ; target : Index.t
  ; target_env : Env.t
  ; target_vars : Ident.t list
  ; loop_back : bool (** Loops back and triggers an increment of transition counter if [true] *)
  }

type signature =
  { functions : (Ident.t * int) list
  ; equations : (Typed.expr * Typed.expr) list
  }

type model =
  { id : Subst.proc_id
  ; param : Subst.param_id option
  ; edges : edge list }

type modeled_proc_group_desc =
  | Unbounded of model
  | Bounded of Subst.param_id * model list

type t =
  { signature : signature
  ; proc_groups : (Subst.proc_group_id * modeled_proc_group_desc) list
  ; access_controls :
      (Subst.proc_group_id
       * (Subst.proc_id
          * [ `Attacks of Ident.t list
            | `Channel of Typed.chan_arg * Ident.t option ] list) list) list
  ; constants : (Ident.t * Typed.init_desc) list
  ; lemmas : (Ident.t * Typed.lemma) list
  }

val t_of_decls : Typed.decl list -> t
