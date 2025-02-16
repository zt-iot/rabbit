type prelude = PreludeNone | PreludeDefault | PreludeFile of string
val prelude_file : prelude ref
val interactive_shell : bool ref
val wrapper : string list option ref
val max_boxes : int ref
val columns : int ref
val trace : bool ref
val verbose : bool ref
val dev : bool ref
val optimize : bool ref
