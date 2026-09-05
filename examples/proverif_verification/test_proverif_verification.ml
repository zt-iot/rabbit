let has_suffix s suffix =
  let s_len = String.length s in
  let suffix_len = String.length suffix in
  s_len >= suffix_len
  && String.sub s (s_len - suffix_len) suffix_len = suffix

let replace_suffix filename ~suffix ~replacement =
  String.sub filename 0 (String.length filename - String.length suffix) ^ replacement

let read_lines filename =
  In_channel.with_open_text filename In_channel.input_lines

let expected_block_results rab_filename =
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

let expected_marker_results rab_filename =
  let marker_re =
    Re.Pcre.regexp
      {|^\s*lemma\s+\w+\s*:\s*\(\*\s*(verified|falsified)\s*\*\)|}
  in
  let proverif_expected_re =
    Re.Pcre.regexp {|\(\*\s*PROVERIF\s+EXPECTED\s+(true|false|unknown)\s*\*\)|}
  in
  read_lines rab_filename
  |> List.filter_map (fun line ->
      match Re.exec_opt marker_re line with
      | None -> None
      | Some groups ->
          (match Re.exec_opt proverif_expected_re line with
           | Some proverif_groups -> Some (Re.Group.get proverif_groups 1)
           | None ->
               match Re.Group.get groups 1 with
               | "verified" -> Some "true"
               | "falsified" -> Some "false"
               | _ -> assert false))

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
  let env, decls = Typer.load (Env.empty ()) rab_filename in
  let program = Proverif_compiler.compile_program env decls in
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
  | Error.Error err -> Format.asprintf "%t" (Error.print err)
  | exn -> Printexc.to_string exn

let test_file proverif rab_filename =
  let expected = expected_block_results rab_filename in
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

let test_snapshot_file proverif rab_filename =
  let expected = expected_marker_results rab_filename in
  let decls = snd @@ Typer.load (Env.empty ()) rab_filename in
  let reachability_flags = reachability_flags decls in
  let pv_filename = replace_suffix rab_filename ~suffix:".rab" ~replacement:".pv" in
  let actual =
    run_proverif proverif pv_filename
    |> normalize_results reachability_flags
  in
  if actual <> expected then
    failwith
      (Printf.sprintf
         "%s: expected [%s], got [%s] from %s"
         rab_filename
         (String.concat "; " expected)
         (String.concat "; " actual)
         pv_filename)

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

let collect_snapshot_files dir =
  Sys.readdir dir
  |> Array.to_list
  |> List.filter (fun filename -> has_suffix filename ".pv")
  |> List.sort String.compare
  |> List.map (fun filename ->
      replace_suffix filename ~suffix:".pv" ~replacement:".rab")
  |> List.map (Filename.concat dir)

let () =
  let use_markers = ref false in
  let rev_args = ref [] in
  Arg.parse
    [ "--expect-markers", Arg.Set use_markers,
      "Read (* verified *) and (* falsified *) lemma expectations and verify sibling .pv files"
    ]
    (fun arg -> rev_args := arg :: !rev_args)
    "test_proverif_verification.exe [--expect-markers] PROVERIF EXAMPLES_DIR";
  let proverif_arg, examples_dir =
    match List.rev !rev_args with
    | [proverif; examples_dir] -> proverif, examples_dir
    | _ ->
        Format.eprintf
          "Usage: %s [--expect-markers] PROVERIF EXAMPLES_DIR@."
          Sys.argv.(0);
        exit 2
  in
  let proverif =
    if Filename.is_relative proverif_arg then
      Filename.concat (Sys.getcwd ()) proverif_arg
    else
      proverif_arg
  in
  let failures = ref [] in
  if !use_markers then
    collect_snapshot_files examples_dir
    |> List.iter (fun rab_filename ->
        try
          test_snapshot_file proverif rab_filename;
          Format.printf "PASS (ProVerif) %s@." rab_filename
        with exn ->
          let message = string_of_exception exn in
          failures := (rab_filename, message) :: !failures;
          Format.printf "FAIL %s: %s@." rab_filename message)
  else (
    collect_rab_files examples_dir
    |> List.iter (fun rab_filename ->
        try
          test_file proverif rab_filename;
          Format.printf "PASS %s@." rab_filename
        with exn ->
          let message = string_of_exception exn in
          failures := (rab_filename, message) :: !failures;
          Format.printf "FAIL %s: %s@." rab_filename message);
    collect_unsupported_files examples_dir
    |> List.iter (fun rab_filename ->
        try
          test_unsupported_file proverif rab_filename;
          Format.printf "PASS (unsupported) %s@." rab_filename
        with exn ->
          let message = string_of_exception exn in
          failures := (rab_filename, message) :: !failures;
          Format.printf "FAIL %s: %s@." rab_filename message)
  );
  exit (if !failures = [] then 0 else 1)
