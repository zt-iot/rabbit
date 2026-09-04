let usage = "Usage: test_proverif file1.rab [file2.rab ...]"

let rev_files = ref []

let add_file filename =
  rev_files := filename :: !rev_files

let pv_filename rab_filename =
  Filename.remove_extension rab_filename ^ ".pv"

let load_file fn =
  try
    Ok (snd @@ Typer.load (Env.empty ()) fn)
  with
  | Error.Error _ as exn -> Error exn
  | exn ->
      Format.eprintf "Typer unexpected exception: %s@." (Printexc.to_string exn);
      Error exn

let write_program filename program =
  Out_channel.with_open_text filename @@ fun oc ->
  let ppf = Format.formatter_of_out_channel oc in
  Rabbit_proverif_pv.Pv_pp.pp_program ppf program;
  Format.pp_print_flush ppf ()

let compile_file rab_filename =
  match load_file rab_filename with
  | Error exn -> raise exn
  | Ok decls ->
      let program = Proverif_compiler.compile_program decls in
      let pv_file = pv_filename rab_filename in
      write_program pv_file program;
      Format.printf "%s -> %s@." rab_filename pv_file

let () =
  Sys.catch_break true;
  Arg.parse [] add_file usage;
  let files = List.rev !rev_files in
  Format.set_max_boxes !Config.max_boxes;
  Format.set_margin !Config.columns;
  Format.set_ellipsis_text "...";
  try
    List.iter compile_file files
  with
  | Error.Error err ->
      Format.eprintf "Error: %t@." (Error.print err);
      exit 1
