let has_suffix s suffix =
  let s_len = String.length s in
  let suffix_len = String.length suffix in
  s_len >= suffix_len
  && String.sub s (s_len - suffix_len) suffix_len = suffix

let is_test_target filename =
  has_suffix filename ".rab"
  && not (has_suffix filename ".rab~")
  && not (has_suffix filename "_unsupported.rab")
  && not
       (List.mem
          filename
          [ "camserver_with_comment.rab"
          ; "issue11_2.rab"
          ; "issue20_2.rab"
          ])

let pv_filename rab_filename =
  Filename.remove_extension rab_filename ^ ".pv"

let error_filename rab_filename =
  Filename.remove_extension rab_filename ^ ".error"

let current_pv_filename rab_filename =
  let dir = Filename.dirname rab_filename in
  let base = Filename.basename rab_filename |> Filename.remove_extension in
  Filename.concat dir ("_" ^ base ^ "_current.pv")

let load_file fn =
  try
    Ok (snd @@ Typer.load (Env.empty ()) fn)
  with
  | Ulexbuf.Error _ as exn -> Error exn
  | Typer.Error _ as exn -> Error exn
  | Proverif_compiler.Error.Error _ as exn -> Error exn
  | exn ->
      Format.eprintf "Unexpected exception while loading %s: %s@." fn (Printexc.to_string exn);
      Error exn

let compile_to_string rab_filename =
  try
    match load_file rab_filename with
    | Error exn -> Error exn
    | Ok decls ->
        let program = Proverif_compiler.compile_program decls in
        let buf = Buffer.create 1024 in
        let ppf = Format.formatter_of_buffer buf in
        Rabbit_proverif_pv.Pv_pp.pp_program ppf program;
        Format.pp_print_flush ppf ();
        Ok (Buffer.contents buf)
  with exn -> Error exn

let read_text_file filename =
  In_channel.with_open_text filename In_channel.input_all

let write_text_file filename contents =
  Out_channel.with_open_text filename (fun oc -> output_string oc contents)

let remove_if_exists filename =
  if Sys.file_exists filename then Unix.unlink filename

let string_of_loc loc =
  match loc with
  | Location.Nowhere -> ""
  | Location.Location _ -> Format.asprintf " at %t" (Location.print loc)

let string_of_failure rab_filename = function
  | Ulexbuf.Error {Location.data = err; Location.loc} ->
      Format.asprintf "Parsing error%s:@ %t" (string_of_loc loc) (Ulexbuf.print_error err)
  | Typer.Error err ->
      Format.asprintf "Typer error%s:@ %t" (string_of_loc err.loc) (Typer.print_error err.data)
  | Proverif_compiler.Error.Error err ->
      Format.asprintf "ProVerif compiler error%s:@ %t"
        (string_of_loc err.loc) (Proverif_compiler.Error.print_error err.data)
  | exn ->
      Printf.sprintf "%s: %s" rab_filename (Printexc.to_string exn)

type test_result =
  | Match
  | Mismatch of string
  | Test_failure of string

let contains_string haystack needle =
  let haystack_len = String.length haystack in
  let needle_len = String.length needle in
  let rec loop index =
    index + needle_len <= haystack_len
    && (String.sub haystack index needle_len = needle || loop (index + 1))
  in
  needle_len = 0 || loop 0

let test_file ~update rab_filename =
  let expected_pv = pv_filename rab_filename in
  let expected_error = error_filename rab_filename in
  let current_pv = current_pv_filename rab_filename in
  match compile_to_string rab_filename with
  | Error exn ->
      remove_if_exists current_pv;
      let actual_error = string_of_failure rab_filename exn in
      if not (Sys.file_exists expected_error) then
        Test_failure actual_error
      else
        let expected = read_text_file expected_error |> String.trim in
        if contains_string actual_error expected then Match
        else
          Test_failure
            (Printf.sprintf
               "%s: expected error containing %S, got: %s"
               rab_filename
               expected
               actual_error)
  | Ok actual ->
      if Sys.file_exists expected_error then (
        remove_if_exists current_pv;
        Test_failure
          (Printf.sprintf
             "%s: compilation succeeded but %s expects an error"
             rab_filename
             expected_error)
      ) else if update then (
        write_text_file expected_pv actual;
        remove_if_exists current_pv;
        Match
      ) else if not (Sys.file_exists expected_pv) then (
        write_text_file current_pv actual;
        Test_failure (Printf.sprintf "%s: expected file %s is missing" rab_filename expected_pv)
      ) else
        let expected = read_text_file expected_pv in
        if String.equal expected actual then (
          remove_if_exists current_pv;
          Match
        ) else (
          write_text_file current_pv actual;
          Mismatch current_pv
        )

let collect_rab_files dir =
  Sys.readdir dir
  |> Array.to_list
  |> List.filter is_test_target
  |> List.map (Filename.concat dir)
  |> List.sort String.compare

let () =
  Format.set_max_boxes !Config.max_boxes;
  Format.set_margin !Config.columns;
  Format.set_ellipsis_text "...";
  let update = ref false in
  let examples_dir = ref "examples/proverif" in
  Arg.parse
    ["--update", Arg.Set update, "Rewrite expected .pv files"]
    (fun dir -> examples_dir := dir)
    "test_proverif_examples.exe [--update] [DIR]";
  let rab_files = collect_rab_files !examples_dir in
  let results =
    List.map (fun rab_filename -> rab_filename, test_file ~update:!update rab_filename) rab_files
  in
  List.iter
    (function
      | rab_filename, Match ->
          Format.printf "PASS %s@." rab_filename
      | rab_filename, Mismatch current_pv ->
          Format.printf "FAIL %s: output differs; wrote %s@." rab_filename current_pv
      | _rab_filename, Test_failure message ->
          Format.printf "FAIL %s@." message)
    results;
  let has_failure =
    List.exists
      (function
        | _, Match -> false
        | _, (Mismatch _ | Test_failure _) -> true)
      results
  in
  exit (if has_failure then 1 else 0)
