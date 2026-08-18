let has_suffix s suffix =
  let s_len = String.length s in
  let suffix_len = String.length suffix in
  s_len >= suffix_len
  && String.sub s (s_len - suffix_len) suffix_len = suffix

let replace_suffix filename ~suffix ~replacement =
  String.sub filename 0 (String.length filename - String.length suffix) ^ replacement

let read_lines filename =
  In_channel.with_open_text filename In_channel.input_lines

let expected_results rab_filename =
  let rec find_blocks rev_blocks = function
    | [] -> List.concat (List.rev rev_blocks)
    | line :: lines ->
        if String.trim line = "(* PROVERIF EXPECTED" then
          let block, lines = read_block [] lines in
          find_blocks (block :: rev_blocks) lines
        else
          find_blocks rev_blocks lines
  and read_block rev_lines = function
    | [] ->
        failwith
          (Printf.sprintf
             "Unterminated (* PROVERIF EXPECTED ... *) block in %s"
             rab_filename)
    | line :: lines ->
        if String.trim line = "*)" then
          List.rev rev_lines, lines
        else
          read_block (line :: rev_lines) lines
  in
  let blocks = find_blocks [] (read_lines rab_filename) in
  if blocks = [] then
    failwith
      (Printf.sprintf
         "Missing (* PROVERIF EXPECTED ... *) block in %s"
         rab_filename);
  blocks
  |> List.map String.trim
  |> List.filter (fun line -> line <> "" && line.[0] <> '#')

let contains_string haystack needle =
  let haystack_len = String.length haystack in
  let needle_len = String.length needle in
  let rec loop index =
    index + needle_len <= haystack_len
    && (String.sub haystack index needle_len = needle || loop (index + 1))
  in
  needle_len = 0 || loop 0

let rec reachability_flags decls =
  List.concat_map
    (fun (decl : Typed.decl) ->
       match decl.desc with
       | Typed.System (_, lemmas) ->
           List.map
             (fun (_, lemma) ->
                match lemma.Typed.desc with
                | Typed.Reachability _ -> true
                | Typed.Plain _ | Typed.Correspondence _ -> false)
             lemmas
       | Load (_, loaded_decls) -> reachability_flags loaded_decls
       | _ -> [])
    decls

let compile_to_file rab_filename pv_filename =
  let decls = snd @@ Typer.load (Env.empty ()) rab_filename in
  let program = Proverif_compiler.compile_program decls in
  Out_channel.with_open_text pv_filename @@ fun oc ->
  let ppf = Format.formatter_of_out_channel oc in
  Rabbit_proverif_pv.Pv_pp.pp_program ppf program;
  Format.pp_print_flush ppf ();
  reachability_flags decls

let result_of_line line =
  if not (String.starts_with ~prefix:"RESULT " line) then
    None
  else if String.ends_with ~suffix:" is true." line then
    Some "true"
  else if String.ends_with ~suffix:" is false." line then
    Some "false"
  else if String.ends_with ~suffix:" cannot be proved." line then
    Some "unknown"
  else
    None

let run_proverif_process proverif pv_filename =
  let argv = [|proverif; "-set"; "color"; "false"; pv_filename|] in
  let ic = Unix.open_process_args_in proverif argv in
  let output = In_channel.input_all ic in
  Unix.close_process_in ic, output

let run_proverif proverif pv_filename =
  match run_proverif_process proverif pv_filename with
  | Unix.WEXITED 0, output ->
      String.split_on_char '\n' output |> List.filter_map result_of_line
  | status, output ->
      let status =
        match status with
        | Unix.WEXITED code -> Printf.sprintf "exit %d" code
        | Unix.WSIGNALED signal -> Printf.sprintf "signal %d" signal
        | Unix.WSTOPPED signal -> Printf.sprintf "stopped by signal %d" signal
      in
      failwith (Printf.sprintf "ProVerif failed (%s):\n%s" status output)

let normalize_results reachability_flags results =
  if List.length reachability_flags <> List.length results then
    failwith
      (Printf.sprintf
         "Expected %d ProVerif results, got %d"
         (List.length reachability_flags)
         (List.length results));
  List.map2
    (fun is_reachability result ->
       match is_reachability, result with
       | true, "true" -> "false"
       | true, "false" -> "true"
       | _ -> result)
    reachability_flags
    results

let string_of_exception = function
  | Ulexbuf.Error {Location.data = err; _} ->
      Format.asprintf "Parsing error: %t" (Ulexbuf.print_error err)
  | Typer.Error err ->
      Format.asprintf "Typer error: %t" (Typer.print_error err.data)
  | Proverif_compiler.Error.Error err ->
      Format.asprintf "ProVerif compiler error: %t"
        (Proverif_compiler.Error.print_error err.data)
  | exn -> Printexc.to_string exn

let test_file proverif rab_filename =
  let expected = expected_results rab_filename in
  let pv_filename = Filename.temp_file "rabbit-proverif-verification-" ".pv" in
  Fun.protect
    ~finally:(fun () -> Sys.remove pv_filename)
    (fun () ->
       let reachability_flags = compile_to_file rab_filename pv_filename in
       let actual =
         run_proverif proverif pv_filename
         |> normalize_results reachability_flags
       in
       if actual <> expected then
         failwith
           (Printf.sprintf
              "%s: expected [%s], got [%s]"
              rab_filename
              (String.concat "; " expected)
              (String.concat "; " actual)))

let test_unsupported_file proverif rab_filename =
  let error_filename =
    replace_suffix rab_filename ~suffix:".rab" ~replacement:".error"
  in
  if not (Sys.file_exists error_filename) then
    failwith (Printf.sprintf "Missing expected-error file %s" error_filename);
  let expected_error = In_channel.with_open_text error_filename In_channel.input_all |> String.trim in
  let pv_filename = Filename.temp_file "rabbit-proverif-unsupported-" ".pv" in
  Fun.protect
    ~finally:(fun () -> Sys.remove pv_filename)
    (fun () ->
       let actual_error =
         try
           ignore (compile_to_file rab_filename pv_filename);
           match run_proverif_process proverif pv_filename with
           | Unix.WEXITED 0, _output ->
               failwith "Compilation and ProVerif verification unexpectedly succeeded"
           | _status, output -> output
         with exn -> string_of_exception exn
       in
       if not (contains_string actual_error expected_error) then
         failwith
           (Printf.sprintf
              "%s: expected error containing %S, got:\n%s"
              rab_filename expected_error actual_error))

let collect_rab_files dir =
  Sys.readdir dir
  |> Array.to_list
  |> List.filter (fun filename ->
      has_suffix filename ".rab"
      && not (has_suffix filename "_library.rab")
      && not (has_suffix filename "_unsupported.rab"))
  |> List.sort String.compare
  |> List.map (Filename.concat dir)

let collect_unsupported_files dir =
  Sys.readdir dir
  |> Array.to_list
  |> List.filter (fun filename -> has_suffix filename "_unsupported.rab")
  |> List.sort String.compare
  |> List.map (Filename.concat dir)

let () =
  if Array.length Sys.argv <> 3 then (
    Format.eprintf "Usage: %s PROVERIF EXAMPLES_DIR@." Sys.argv.(0);
    exit 2
  );
  let proverif =
    if Filename.is_relative Sys.argv.(1) then
      Filename.concat (Sys.getcwd ()) Sys.argv.(1)
    else
      Sys.argv.(1)
  in
  let examples_dir = Sys.argv.(2) in
  let failures = ref [] in
  collect_rab_files examples_dir
  |> List.iter (fun rab_filename ->
      try
        test_file proverif rab_filename;
        Format.printf "PASS %s@." rab_filename
      with exn ->
        failures := (rab_filename, Printexc.to_string exn) :: !failures;
        Format.printf "FAIL %s: %s@." rab_filename (Printexc.to_string exn));
  collect_unsupported_files examples_dir
  |> List.iter (fun rab_filename ->
      try
        test_unsupported_file proverif rab_filename;
        Format.printf "PASS (unsupported) %s@." rab_filename
      with exn ->
        failures := (rab_filename, Printexc.to_string exn) :: !failures;
        Format.printf "FAIL %s: %s@." rab_filename (Printexc.to_string exn));
  exit (if !failures = [] then 0 else 1)
