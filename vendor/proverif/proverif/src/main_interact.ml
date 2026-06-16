open Types
open Parsing_helper
open GMain
open GdkKeysyms

let file = ref None

let set_file s =
  file := Some s

let _ =
  Arg.parse
    [ "-lib", Arg.String (fun s -> Param.lib_name := s :: (!Param.lib_name) ),
        "<filename> \tchoose the library file (for pitype front-end only)";
      "-commandGraph", Arg.String (fun s ->
        Param.interactive_dot_command := s;),
      "\t\t\tDefine the command for the creation of the graph trace from the dot file";
    ]
    set_file ("Simulator for Proverif " ^ Version.version ^ ", by Bruno Blanchet, Vincent Cheval, and Marc Sylvestre");
  Menu_interact.main_window (!file)
