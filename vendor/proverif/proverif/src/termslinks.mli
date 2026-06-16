val equal_terms_with_links : Types.term -> Types.term -> bool
val equal_facts_with_links : Types.fact -> Types.fact -> bool

val equal_closed_terms : Types.term -> Types.term -> bool

val equal_tags : Types.label -> Types.label -> bool
val equal_constra : Types.constraints -> Types.constraints -> bool

val match_terms : Types.term -> Types.term -> unit

val get_vars : Types.binder list ref -> Types.term -> unit
val has_vars : Types.term -> bool
