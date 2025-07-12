open Typed

type t =
  { channels : (ident * ident) list
  ; parameters : (ident * expr) list
  }

val expr : t -> expr -> expr
val fact : t -> fact -> fact
val cmd : t -> cmd -> cmd

(* proc and pproc in Syntax and Typed are so confusing.
   Subst and later modules use different words, proc_group and proc respectively *)
(* These "process ids" are so confusing without types *)
type proc_group_id = private Ident.t
type proc_id = private Ident.t
type param_id = private Ident.t

val param_id : Ident.t -> param_id

type instantiated_proc =
  { id : proc_id
  ; param : param_id option
  ; typ : ident
  ; files : (expr * ident * expr) list
  ; vars : (ident * expr) list
  ; funcs : (ident * ident list * cmd) list
  ; main : cmd
  ; template : Typed.pproc (** Original pproc *)
    (* XXX should be removed if possible. Why required? *)
  }

type instantiated_proc_group_desc =
  | Unbounded of instantiated_proc
  | Bounded of param_id * instantiated_proc list

type instantiated_proc_group =
  { id : proc_group_id
  ; desc : instantiated_proc_group_desc
  }

val instantiate_proc_group : decl list -> Typed.proc -> instantiated_proc_group
