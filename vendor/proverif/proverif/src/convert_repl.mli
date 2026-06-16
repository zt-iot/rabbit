open Pitypes

(* This function converts replications in the style of interactive
   simulator (each replication of !P creates one copy P and keeps the
   initial process !P) to the style used in trace reconstruction
   (replication of !P n times creates n copies of P and !P disappears).
   To be used before graphical display of traces. *)
       
val convert_repl : 'a reduc_state -> 'a reduc_state 
