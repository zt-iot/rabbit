(** Configuration options for Rabbit *)

(** Type representing different prelude options
    - PreludeNone: No prelude file loaded
    - PreludeDefault: Load default prelude
    - PreludeFile: Load custom prelude file *)
type prelude = PreludeNone | PreludeDefault | PreludeFile of string

(** Reference to store the prelude configuration *)
val prelude_file : prelude ref

(** Flag to enable/disable interactive shell mode *)
val interactive_shell : bool ref

(** Optional wrapper command to run Rabbit with *)
val wrapper : string list option ref

(** Maximum number of boxes to display in output *)
val max_boxes : int ref

(** Number of columns for output formatting *)
val columns : int ref

(** Flag to enable/disable tracing *)
val trace : bool ref

(** Flag to enable/disable verbose output *)
val verbose : bool ref

(** Flag to enable developer mode features *)
val dev : bool ref

(** Flag to enable optimization passes *)
val optimize : bool ref

(** Flag to enable transition tagging in output *)
val tag_transition : bool ref
