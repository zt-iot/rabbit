(* Translation from the applied pi calculus to Horn clauses,
   for processes without choice (correspondences, noninterf, weaksecret) *)

val transl : Pitypes.t_pi_state -> Types.t_horn_state * Pitypes.t_pi_state
