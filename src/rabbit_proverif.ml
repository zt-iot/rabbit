(** ProVerif compiler main program *)

let usage = "Usage: rabbit-proverif [option] ... [file] ..."

let files = ref []

let ofile = ref None

let add_file filename = files := filename :: !files

let add_ofile filename = ofile := Some filename

let options =
  Arg.align
    [ ("--columns",
       Arg.Set_int Config.columns,
       " Set the maximum number of columns of pretty printing")
    ; ("-v",
       Arg.Unit (fun () ->
           Format.printf "Rabbit- %s (%s)@." Build.version Sys.os_type;
           exit 0),
       " Print version information and exit")
    ; ("-l",
       Arg.String add_file,
       "<file> Load <file> into the initial environment")
    ; ("--debug",
       Arg.Set Config.debug,
       "Print debugging messages")
    ; ("-o",
       Arg.String add_ofile,
       "<file> Write the translated ProVerif program into <file>")
    ]

let load_file fn =
  try
    Ok (snd @@ Typer.load (Env.empty ()) fn)
  with
  | (Typer.Error _ as exn) -> Error exn
  | exn ->
      Format.eprintf "Typer unexpected exception: %s@." (Printexc.to_string exn);
      Error exn

let compile_files files =
  List.iter
    (fun fn ->
       match load_file fn with
       | Ok decls ->
           ignore (Proverif_compiler.compile_program decls)
       | Error exn -> raise exn)
    files

let run () =
  let files = List.rev !files in
  compile_files files;
  match !ofile with
  | None ->
      Print.message ~loc:Location.Nowhere "Warning:" "%s"
        "output file not specified"
  | Some ofile ->
      Print.message ~loc:Location.Nowhere "Target output" "%s" ofile

let () =
  Sys.catch_break true;
  Arg.parse options add_file usage;
  Format.set_max_boxes !Config.max_boxes;
  Format.set_margin !Config.columns;
  Format.set_ellipsis_text "...";
  try
    run ()
  with
  | Ulexbuf.Error {Location.data = err; Location.loc} ->
      Print.message ~loc "Parsing error" "%t" (Ulexbuf.print_error err);
      exit 1
  | Typer.Error err ->
      Print.message ~loc:err.loc "Typer error" "%t" (Typer.print_error err.data);
      exit 1
  | Proverif_compiler.Error.Error err ->
      Print.message ~loc:err.loc "ProVerif compiler error" "%t"
        (Proverif_compiler.Error.print_error err.data);
      exit 1
