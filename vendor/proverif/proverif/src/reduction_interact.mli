open Types
val max_proc_nb: int
val do_one_reduction_step : term Pitypes.reduc_state -> int -> (unit -> unit) -> (unit -> unit) -> term Pitypes.reduc_state
val do_all_auto_reduction: term Pitypes.reduc_state -> (unit -> unit) -> (unit -> unit) -> term Pitypes.reduc_state
val up_proc_nb: int -> unit
val get_proc_nb: unit -> int
