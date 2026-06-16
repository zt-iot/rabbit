open Types

val initialize : t_solver_kind -> unit

(* [is_standard_clause r] returns true when the clause [r] 
   must be preserved from transformations *)
val is_standard_clause : reduction -> bool
val simplify : (reduction -> unit) -> (reduction -> unit) -> reduction -> unit
val selfun : reduction -> int
val remove_equiv_events : (reduction -> unit) -> reduction -> unit
