(** Clerial main program *)

(** The usage message. *)
let usage = "Usage: Rabbit [option] ... [file] ..."

(** A list of files to be loaded and run, together with information on whether they should
    be loaded in interactive mode. *)
let files = ref []

(** Add a file to the list of files to be loaded, and record whether it should
    be processed in interactive mode. *)
let add_file quiet filename = (files := (filename, quiet) :: !files)

(** Command-line options *)
let options = Arg.align [

    ("--columns",
     Arg.Set_int Config.columns,
     " Set the maximum number of columns of pretty printing");

(*     ("--no-prelude",
     Arg.Unit (fun () -> Config.prelude_file := Config.PreludeNone),
     " Do not load the prelude.m31 file");

    ("--prelude",
     Arg.String (fun str -> Config.prelude_file := Config.PreludeFile str),
     "<file> Specify the prelude file to load initially");
 *)
    ("-v",
     Arg.Unit (fun () ->
         Format.printf "Rabbit- %s (%s)@." Build.version Sys.os_type ;
         exit 0),
     " Print version information and exit");

(*     ("-n",
     Arg.Clear Config.interactive_shell,
     " Do not run the interactive toplevel");
 *)
(*     ("-l",
     Arg.String (fun str -> add_file true str),
     "<file> Load <file> into the initial environment");
 *)

     ("--trace",
     Arg.Set Config.trace,
     " Print trace information during evaluation");
 
    ("--verbose",
     Arg.Set Config.verbose,
     " Print information during computation")
  ]

(** Main program *)
let _main =
  Sys.catch_break true ;
  (* Parse the arguments. *)
  Arg.parse
    options
    (fun str -> add_file false str)
    usage ;
  (* Files were accumulated in the wrong order, so we reverse them *)
  files := List.rev !files ;

  (* Set the maximum depth of pretty-printing, after which it prints ellipsis. *)
  Format.set_max_boxes !Config.max_boxes ;
  Format.set_margin !Config.columns ;
  Format.set_ellipsis_text "..." ;
  try
    (* Run and load all the specified files. *)
    let topstate =
      List.fold_left
        (fun topstate (fn, quiet) -> Toplevel.load_file ~quiet topstate fn)
        Toplevel.initial !files in ()

  with
  | Ulexbuf.Error {Location.data=err; Location.loc} ->
     Print.message ~loc "Syntax error" "%t" (Ulexbuf.print_error err)
  | Desugar.Error {Location.data=err; Location.loc} ->
     Print.message ~loc "Syntax error" "%t" (Desugar.print_error err)
  | Typecheck.Error {Location.data=err; Location.loc} ->
     Print.message ~loc "Type error" "%t" (Typecheck.print_error err)
  | Runtime.Error {Location.data=err; Location.loc} ->
     Print.message ~loc "Runtime error" "%t" (Runtime.print_error err)
