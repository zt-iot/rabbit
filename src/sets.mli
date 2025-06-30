module ProcSet : Set.S with type elt = string

type proc_set = ProcSet.t

val pp_proc_set : Format.formatter -> proc_set -> unit

val equal_proc_set : proc_set -> proc_set -> bool