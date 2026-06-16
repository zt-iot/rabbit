open Pitypes

(* [move lets_never_fail pi_state] moves "new" and "let" downwards
   in the process inside [pi_state].
   [lets_never_fail] is true when it is known that "let"s never fail
   (so they can all be moved). *)
val move : bool -> t_pi_state -> t_pi_state
