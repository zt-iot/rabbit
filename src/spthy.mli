(** Expressions for transition counting *)
type transition =
  | One (** [%1] *)
  | Var (** [%v] *)
  | Inc (** [%v %+ %1] *)

(** Subset of Tamarin expression *)
type expr =
  | Unit (** ['unit'] *)
  | String of string (** ['str:contents'] *)
  | Integer of int (** ['42'] *)
  | Ident of Ident.t (** [name__stamp] *)
  | Tuple of expr list (** [<e1, .., en>] *)
  | Apply of Ident.t * expr list (** [f(e1, .., en)] *)
  | Index of Sem.Index.t (** Node index ['index:1.2__3.4'] *)
  | Transition of transition (** Transition count *)

type signature =
  { functions : (Ident.t * int) list
  ; equations : (expr * expr) list
  }

type fact =
  | Channel of
      { channel : expr
      ; name : Name.t
      ; args : expr list
      } (** Channel fact [ch :: name(args)] *)
  | Plain of Name.t * expr list (** [n(e1,..,en)] *)
  | Eq of expr * expr (** [e1 = e2] *)
  | Neq of expr * expr (** [e1 != e2] *)
  | File of { path : expr; contents : expr; } (** File fact [path.contents] *)
  | Global of Name.t * expr list (** [:: n(e1,..,en)] *)

  (* New additions at Sem level *)

  | Fresh of Ident.t (** Fresh variable *)
  | Structure of
      { name : Name.t
      ; proc_id : Subst.proc_id
      ; param : Subst.param_id option
      ; address : expr
      ; args : expr list
      } (** Structure fact [name(process, address, args)] *)
  | Loop of
      { mode : Typed.loop_mode
      ; proc_id : Subst.proc_id
      ; param : Subst.param_id option
      ; index : Sem.Index.t
      }
  | Access of
      { proc_id : Subst.proc_id
      ; param : Subst.param_id option
      ; channel : expr (** channel or file *)
      ; syscall : Ident.t option (** System call allowed the access.
                                    [None] allows the access out of syscalls.   *)
      }

  (* New additions at Spthy level *)

  | Const of
      { id : Ident.t
      ; param : expr option
      ; value : expr
      } (** Constant definition/dependency *)
  | Initing_const of
      { id : Ident.t
      ; param : Subst.param_id option
      } (** Constant initialization event *)
  | Initing_proc_group of Subst.proc_group_id * Subst.param_id option (** Process group initialization event *)
  | Initing_proc_access of
      { proc_id : Subst.proc_id
      ; param : Subst.param_id option
      } (** Process access initialization event *)
  | Inited_proc_group of Subst.proc_group_id * Subst.param_id option (** Process group initialized *)
  | State of
      { proc_id : Subst.proc_id
      ; param : Subst.param_id option
      ; index : Sem.Index.t
      ; mapping : (Ident.t * expr) list (** The values of the mutable variables *)
      ; transition : transition option
      } (** Process status *)
  | Transition of
      { proc_id : Subst.proc_id
      ; param : Subst.param_id option
      ; source : Sem.Index.t; transition : transition option
      } (** Transition event *)

val string_of_fact : fact -> string

type 'a compiled =
  { deps : fact list (** Constants dependencies *)
  ; result : 'a;
  }
(** Compilation result of type ['a] and the extracted constant fact from the compilation *)

(** Tamarin lemma *)
type lemma =
  | Plain of string
  | Reachability of fact list compiled
  | Correspondence of
      { premise : fact compiled
      ; conclusion : fact compiled
      }

(** Tamarin rule *)
type rule =
  { id : Ident.t
  ; role : Ident.t option
  ; pre : fact list
  ; label : fact list
  ; post : fact list
  ; comment : string option
  }

(** Rabbit system compiled to Tamarin *)
type t =
  { signature : signature
  ; constants : rule list
  ; proc_group_inits : rule list
  ; access_controls : rule list
  ; models : (Subst.proc_id * rule list) list
  ; lemmas : (Ident.t * lemma) list
  }

val print : Format.formatter -> t -> unit

val compile_sem : Sem.t -> t
(** [compile_sem sem] compiles semantics [sem] to a Tamarin system. *)
