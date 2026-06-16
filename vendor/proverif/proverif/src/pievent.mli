open Types
open Pitypes
open Stringmap

(* [set_event_status pi_state] records the status of events (injective,
   non-injective, or not used, in hypothesis or in conclusion of
   of the queries) for the queries in [pi_state].
   This function must be called before translating the
   process into clauses. *)
val set_event_status : t_pi_state -> t_pi_state

(* [get_event_status pi_state e] returns the status for event [e]. *)
val get_event_status : t_pi_state -> funsymb -> eventstatus

(* [update_event_status_with_lemmas] updates the status of events occuring in
   in the lemmas. Must be applied after [Lemma.simplify_lemmas]. *)
val update_event_status_with_lemmas : t_pi_state -> unit
