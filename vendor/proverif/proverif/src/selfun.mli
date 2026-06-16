open Types

val never_select_weight : int
val weight_of_user_weight : nounif_value -> int

(* Replaces [FAny x] with [FVar x] when there is an [FVar x] elsewhere
   in the format. This is how the format is understood. *)
val homogeneous_format : fact_format -> fact_format

val initialize : (fact_format * nounif_value * nounif_op) list -> t_solver_kind -> unit
val guess_no_unif : Database.QueueClause.t -> unit
val selection_fun : reduction -> int
val selection_fun_nostatechange : reduction -> int

(* [exists_ignored_nounif ()] returns [true] if and only if some nounif have been
   declared with the option [ignoreOnce]. *)
val exists_ignored_nounif : unit -> bool

(* The i-th element of [induc_auth] indicates whether we can apply a resolution on
  the i-th hypothesis of the clause despite the declaration of a nounif. Note that
  such application can only occur if the matching nounif has been declared with the
  option [ignoreOnce].

  [selection_with_ignore_nounif hyp order_data] checks whether one hypothesis of hyp can be
  matched with a nounif declared with option [ignoreOnce] and the application
  is authorized by [induc_auth]. When it is the case, the function returns the position [i]
  of the hypothesis in [hyp] as well as an updated [order_data] list in which the
  authorization for the [i]th hypothesis has been decreased by 1. Typically, this new
  authorization list will be used after the resolution on the [i]th hypothesis
  to enforce that such resolution is applied only a limited number of times per hypothesis.

  When no hypothesis is authorized, the function returns -1 and [induc_auth].
*)
val selection_with_ignore_nounif : fact list -> ('a * int) list -> int * ('a * int) list

(* [find_inductive_variable_to_remove nextf rule] tries to find two facts in the
   hypotheses of [rule] that match the same nounif declared with the option
   [inductionOn]. When it is the case, by definition of the nounif, it extracts
   the two lists of variables in the hypotheses of [rule] corresponding to the
   nounif declaration, say v11,...,v1n and v21,...,v2n, and checks whether
     1) v11 >= v21 && v12 >= v22 && ... && v1n >= v2n
     2) or, v11 <= v21 && v12 <= v22 && ... && v1n <= v2n
   is implied by the constraints in [rule].
   In case 1: the function applies [nextf] to the list v21,...,v2n
   In case 2: the function applies [nextf] to the list v11,...,v1n
   Otherwise it raises Not_found. *)
val find_inductive_variable_to_remove : (binder list -> 'a) -> reduction -> 'a
