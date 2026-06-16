(* [solve_auth horn_state queries] solves the correspondence queries [queries]
   using the Horn clauses and other information for resolution in
   [horn_state] obtained by translation from the process.

   This function takes as argument pairs of queries.
   The first component of the pair is the original query as entered by the user, for display.
   The second component is the encoded query, used for resolution. *)

val solve_auth : Types.t_horn_state -> Pitypes.t_pi_state -> (Pitypes.query_res * Pitypes.t_query) list
