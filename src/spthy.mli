(** Expressions for transition counting *)
type transition =
  | One (** [%1] *)
  | Var (** [%v] *)
  | Inc (** [%v %+ %1] *)

(** Subset of Tamarin expression *)
type expr =
  | Unit
  | String of string
  | Integer of int
  | Ident of Ident.t
  | Tuple of expr list
  | Apply of Ident.t * expr list
  | Index of Sem.Index.t (** Node index *)
  | Transition of transition (** Transition count *)

type signature =
  { functions : (Ident.t * int) list
  ; equations : (expr * expr) list
  }

type fact =
  | Channel of { channel : expr; name : Name.t; args : expr list }
  | Out of expr
  | In of expr
  | Plain of Name.t * expr list
  | Eq of expr * expr
  | Neq of expr * expr
  | File of { path : expr; contents : expr; }
  | Global of Name.t * expr list

  (* New additions at Sem level *)

  | Fresh of Ident.t
  | Structure of
      { name : Name.t
      ; proc_id : Subst.proc_id
      ; address : expr
      ; args : expr list
      }
  | Loop of
      { mode : Typed.loop_mode
      ; proc_id : Subst.proc_id
      ; param : Subst.param_id option
      ; index : Sem.Index.t
      }
  | Access of
      { proc_id : Subst.proc_id
      ; param : Subst.param_id option
      ; channel : expr
      ; syscall : Ident.t option
      }

  (* New additions at Spthy level *)

  | Const of
      { id : Ident.t
      ; param : expr option
      ; value : expr
      }
  | Initing_const of
      { id : Ident.t
      ; param : Subst.param_id option
      }
  | Initing_proc_group of Subst.proc_group_id
  | Initing_proc_access of
      { proc_id : Subst.proc_id
      ; param : Subst.param_id option
      }
  | Inited_proc_group of Subst.proc_group_id * Subst.param_id option
  | State of
      { proc_id : Subst.proc_id
      ; param : Subst.param_id option
      ; index : Sem.Index.t
      ; mapping : (Ident.t * expr) list
      ; transition : transition option
      }
  | Transition of
      { proc_id : Subst.proc_id
      ; param : Subst.param_id option
      ; source : Sem.Index.t; transition : transition option
      }

val string_of_fact : fact -> string

type 'a compiled = { deps : fact list; result : 'a; }
(** Compilation result of type ['a]
    and the extracted constant fact from the compilation *)

type lemma =
  | Plain of string
  | Reachability of fact list compiled
  | Correspondence of
      { premise : fact compiled
      ; conclusion : fact compiled
      }

type rule =
  { id : Ident.t
  ; role : Ident.t option
  ; pre : fact list
  ; label : fact list
  ; post : fact list
  ; comment : string option
  }

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
