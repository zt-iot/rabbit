open Types
module GtkInteract :
sig
  val display_term : term -> string
  val display_fact : fact -> string
  val display_process: process -> string list
  val display_public : (term * term) list -> term list -> string list
  val display_pattern: pattern -> string
end
