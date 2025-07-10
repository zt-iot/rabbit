module StringSet : Set.S with type elt = string
module ProcTySet : Set.S with type elt = string


type proc_ty_set = ProcTySet.t

val pp_proc_ty_set : Format.formatter -> proc_ty_set -> unit

val equal_proc_ty_set : proc_ty_set -> proc_ty_set -> bool