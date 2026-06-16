open Types
open Pitypes

(* Encode queries of the form "query secret .. [public_vars ...]"
   and "query ...==>... public_vars ..." into correspondence queries
   without public_vars. The process may need to be modified, 
   and groups of queries may need to be split. *)
val encode_secret_public_vars : (t_pi_state -> unit) -> t_pi_state -> unit

(* Encode destructors in queries, lemmas and restrictions. Destructors 
   in hypothesis are not allowed; hence this function returns the same number
   of queries as before *)
val encode_destructors : t_pi_state -> t_pi_state

(* Give the fact to query from the detailed query
   This is used only to create a resembling specification for SPASS

   This function takes as argument the pi state. *)
val query_to_facts : t_pi_state -> fact list
