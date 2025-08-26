(** Configuration options for Rabbit *)

(** Maximum number of boxes to display in output *)
val max_boxes : int ref

(** Number of columns for output formatting *)
val columns : int ref

(** Flag to enable developer mode features *)
val dev : bool ref

(** Flag to enable optimization passes *)
val optimize : bool ref

(** Flag to enable transition tagging in output *)
val tag_transition : bool ref
