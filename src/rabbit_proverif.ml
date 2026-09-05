(** ProVerif compiler main program *)

let usage = "Usage: rabbit-proverif [option] ... [file] ..."

let files = ref []

let input_files = ref []

let ofile = ref None

let add_file filename = files := filename :: !files

let add_input_file filename =
  add_file filename;
  input_files := filename :: !input_files

let add_ofile filename = ofile := Some filename

let default_output_file filename = Filename.remove_extension filename ^ ".pv"

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
    Ok (Typer.load (Env.empty ()) fn)
  with
  | Error.Error _ as exn -> Error exn
  | exn ->
      Format.eprintf "Typer unexpected exception: %s@." (Printexc.to_string exn);
      Error exn

let compile_files files =
  List.map
    (fun fn ->
       match load_file fn with
       | Ok (env, decls) ->
           Proverif_compiler.compile_program env decls
       | Error exn -> raise exn)
    files

let write_programs filename programs =
  Out_channel.with_open_text filename @@ fun oc ->
  let ppf = Format.formatter_of_out_channel oc in
  List.iter
    (fun program ->
       Format.fprintf ppf "%a@." Rabbit_proverif_pv.Pv_pp.pp_program program)
    programs

let run () =
  let files = List.rev !files in
  let programs = compile_files files in
  match !ofile with
  | None ->
      Print.message ~loc:Location.Nowhere "Warning:" "%s"
        "output file not specified"
  | Some ofile ->
      write_programs ofile programs;
      Print.message ~loc:Location.Nowhere "Translated into" "%s" ofile

let () =
  Sys.catch_break true;
  Arg.parse options add_input_file usage;
  (match !ofile, !input_files with
   | None, filename :: _ -> ofile := Some (default_output_file filename)
   | Some _, _ | None, [] -> ());
  Format.set_max_boxes !Config.max_boxes;
  Format.set_margin !Config.columns;
  Format.set_ellipsis_text "...";
  try
    run ()
  with
  | Error.Error err ->
      Format.eprintf "Error: %t@." (Error.print err);
      exit 1
