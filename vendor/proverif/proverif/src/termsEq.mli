(* This module contains basic functions to manipulate terms modulo
   an equational theory *)

open Types

(* returns true when at least one equation has been registered *)
val hasEquations : unit -> bool

val hasConvergentEquations : unit -> bool

(* Transforms equations into rewrite rules on constructors
   When !Param.html_output is set, an HTML file must be open to receive
   the display. *)
val record_eqs : t_horn_state -> unit

val collect_unset_vars : binder list ref -> term -> unit

(* Close clauses modulo the equational theory *
 close_rule_eq is used for clauses entered by the user in Horn-clause
 front-ends,
 close_fact_eq is used for closing the goals *)
val close_term_eq : (term -> unit) -> term -> unit
val close_term_list_eq : (term list -> unit) -> term list -> unit
val close_fact_eq : (fact -> unit) -> fact -> unit
val close_fact_list_eq : (fact list -> unit) -> fact list -> unit
val close_rule_eq : (reduction -> unit) -> reduction -> unit
val close_rule_hyp_eq : (reduction -> unit) -> reduction -> unit

(* Close terms by rewrite rules of constructors and destructors. *)
val close_term_destr_eq : constraints -> (constraints -> term -> unit) -> term -> unit

(* Close clauses by rewrite rules of constructors and destructors. *
   Used for clauses that define predicates (for LetFilter). *)
val close_rule_destr_eq : (fact list * fact * constraints -> unit) -> fact list * fact * constraints -> unit

(* [f_has_no_eq f] returns [true] when the function symbol [f]
   has no equation. *)
val f_has_no_eq : funsymb -> bool

(* Unification modulo the equational theory *)
val close_term_eq_synt : (term -> 'a) -> term -> 'a
val close_constraints_eq_synt : (constraints -> 'a) -> constraints -> 'a
val unify_modulo : (unit -> 'a) -> term -> term -> 'a
val unify_modulo_list : (unit -> 'a) -> term list -> term list -> 'a

val unify_modulo_save : (unit -> 'a) -> term -> term -> 'a
val unify_modulo_list_save : (unit -> 'a) -> term list -> term list -> 'a

val copy_remove_syntactic : term -> term
val copy_remove_syntactic_fact : fact -> fact
val copy_remove_syntactic_conclusion_query : Pitypes.conclusion_query -> Pitypes.conclusion_query
val copy_remove_syntactic_realquery : Pitypes.realquery -> Pitypes.realquery
val remove_syntactic_term : term -> term
val remove_syntactic_fact : fact -> fact
val remove_syntactic_constra : constraints -> constraints
val remove_syntactic_rule : reduction -> reduction

(* [gather_nat_vars constra] returns the list of natural number variables
   in [constra] *)
val gather_nat_vars : constraints -> binder list

(* Treatment of inequality constraints *)

(* Remove inequalities of the form x <> caught-fail as they are always true in
  the generated clauses.*)
val remove_caught_fail : constraints -> constraints

exception FalseConstraint

(* [check_constraints constra] checks that the constraints [constra]
   are still satisfiable. It raises [FalseConstraint] when they are not. *)
val check_constraints : constraints -> unit

(* [check_closed_constraints constra] checks that the constraints [constra]
   are still satisfiable. Returns [true] when they are.
   Assumes that the constraints are closed.
   Used to evaluate destructors in trace reconstruction. *)
val check_closed_constraints : constraints -> bool

(* [simplify_constraints f_next f_next_inst fact_list constralist]
   simplifies the constraints [constralist] knowing that
   they occur in a clause containing the facts in the list [fact_list].
   Raises [FalseConstraint] when the constraints are not satisfiable.
   Calls [f_next] when the constraints are simplified without instantiating
   variables.
   Calls [f_next_inst] when the simplification instantiated some
   variables, so the facts may contain links to be copied. *)

val simplify_constraints : (constraints -> 'a) -> (constraints -> 'a) -> fact list -> constraints -> 'a

(* May contain links. *)
val simple_simplify_constraints : constraints -> constraints

(* May not contain link *)
val simple_simplify_constraints_rule : reduction -> reduction

(* [simplify_constraints_keepvars f_next f_next_inst keep_vars constralist]
   simplifies the constraints [constralist].
   Variables in [keep_vars] occur elsewhere, so they should be preserved.
   Raises [FalseConstraint] when the constraints are not satisfiable.
   Calls [f_next] when the constraints are simplified without instantiating
   variables.
   Calls [f_next_inst] when the simplification instantiated some
   variables, so the facts may contain links to be copied. *)
val simplify_constraints_keepvars : (constraints -> 'a) -> (constraints -> 'a) -> binder list -> constraints -> 'a


(* [simplify_constraints_rule f_next f_next_inst clause]
   simplifies the constraints of clause [clause].
   Calls [f_next] when the constraints are simplified without instantiating
   variables.
   Calls [f_next_inst] when the simplification instantiated some
   variables.
   Calls no function when the constraints are not satisfiable.*)
val simplify_constraints_rule : (reduction -> unit) -> (reduction -> unit) -> reduction -> unit

(* [implies_constraints_keepvars* factlist constraint1 constraint2]
   checks that the constraints [constraint1] imply the constraints [constraint2].
   It returns unit when the check succeeds and raises [NoMatch] when it fails.
   [constraint2] is supposed to contain links that come from a previous matching.
   [factlist] is a list of facts of the clause that contains [constraint1].
   (The argument [factlist] is used to know which variables should be preserved in
   the simplification of the instance of [constraint2], which after substitution
   uses variables of the clause [factlist, constraint1].)

   These functions differ by how they copy the constraint [constraint2]:
   - [implies_constraints_keepvars] makes no copy.
   - [implies_constraints_keepvars3] uses [Terms.copy_constra3], so it copies
   one level of links: it is suitable after matching.
   - [implies_constraints_keepvars4] uses [Terms.copy_constra4], so it copies
   links recursively. *)


val implies_constraints_keepvars : fact list -> constraints -> constraints -> unit
val implies_constraints_keepvars3 : fact list -> constraints -> constraints -> unit
val implies_constraints_keepvars4 : fact list -> constraints -> constraints -> unit

(* [implies_constraints_keepvars_binders vlist constraint1 constraint2] is similar
   to [implies_constraints_keepvars factlist constraint1 constraint2] except that
   the variables preserved in the simplifcation of the instance of [constraint2]
   are the variables in [vlist] rather than the variables in the list of fact
   [factlist]. *)
val implies_constraints_keepvars_binders : binder list -> constraints -> constraints -> unit

(* [get_solution f_next constra] calls [f_next] after linking variables to
   a solution of the constraints [constra].
   Raises [FalseConstraint] when there is no solution. *)
val get_solution : (unit -> 'a) -> constraints -> 'a

(* Transforms equations into rewrite rules on constructors, also closing
   the rewrite rules of destructors modulo equations.
   When !Param.html_output is set, an HTML file must be open to receive
   the display. *)
val record_eqs_with_destr : Pitypes.t_pi_state -> unit

(* Simplifies a term using the equations *)
exception Reduces
val simp_eq : term -> unit
