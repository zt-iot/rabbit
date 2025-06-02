(** Configuration parameters *)

type prelude =
  | PreludeNone
  | PreludeDefault
  | PreludeFile of string

let prelude_file = ref PreludeDefault

let interactive_shell = ref true

let wrapper = ref (Some ["rlwrap"; "ledit"])

let max_boxes = ref 42

let columns = ref (Format.get_margin ())

let trace = ref false

let verbose = ref false

let dev = ref true

let optimize = ref false

let tag_transition = ref false

