(** Instantiated processes *)

open Typed

type t =
  { channels : (ident * (ident * expr option)) list
  ; parameters : (ident * expr) list
  }

val expr : t -> expr -> expr
val fact : t -> fact -> fact
val cmd : t -> cmd -> cmd

(** [proc] and [pproc] in [Syntax] and [Typed] are so confusing.
    [Subst] and later modules use different wordings, [proc_group] and [proc] respectively

    We use private types to distinguish the ids for different tpyes.
*)

type proc_group_id = private Ident.t
type proc_id = private Ident.t
type param_id = private Ident.t

val param_id : Ident.t -> param_id

(** Instantiated proc *)
type proc =
  { id : proc_id
  ; param : param_id option
  ; args : chan_arg list
  ; typ : ident
  ; files : (expr * ident * expr) list
  ; vars : (ident * expr) list
  ; funcs : (ident * ident list * cmd) list
  ; main : cmd
  }

(** Instantiated proc group desc *)
type proc_group_desc =
  | Unbounded of proc
  | Bounded of param_id * proc list

(** Instantiated proc group *)
type proc_group = proc_group_id * proc_group_desc

val instantiate_proc_group : decl list -> Typed.proc -> proc_group
