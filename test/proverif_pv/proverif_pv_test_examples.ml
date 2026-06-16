open Rabbit_proverif_pv
module Parse = Rabbit_proverif_pv_parse
open Parse

let proverif_examples_dir_candidates =
  [
    "vendor/proverif/proverif/examples";
    "../vendor/proverif/proverif/examples";
    "../../vendor/proverif/proverif/examples";
  ]

let proverif_examples_dir =
  match List.find_opt Sys.file_exists proverif_examples_dir_candidates with
  | Some dir -> dir
  | None ->
      Proverif_pv_test_support.failwithf
        "ProVerif examples directory not found. Tried: %s"
        (String.concat ", " proverif_examples_dir_candidates)

let indentation_example_file_candidates =
  [
    [
      "src/proverif_pv/indentation_example.pv";
      "src/proverif_pv/indentation_example_process.pv";
    ];
    [
      "../../src/proverif_pv/indentation_example.pv";
      "../../src/proverif_pv/indentation_example_process.pv";
    ];
    [
      "../../../src/proverif_pv/indentation_example.pv";
      "../../../src/proverif_pv/indentation_example_process.pv";
    ];
  ]

let indentation_example_files =
  match List.find_opt (List.for_all Sys.file_exists) indentation_example_file_candidates with
  | Some files -> files
  | None ->
      Proverif_pv_test_support.failwithf
        "Indentation example files not found. Tried: %s"
        (String.concat " | "
           (List.map (String.concat ", ") indentation_example_file_candidates))

let rec collect_pv_files dir =
  Sys.readdir dir
  |> Array.to_list
  |> List.sort String.compare
  |> List.concat_map (fun entry ->
         let path = Filename.concat dir entry in
         if Sys.is_directory path then
           collect_pv_files path
         else if Filename.check_suffix path ".pv" && not (Filename.check_suffix path ".m4.pv") then
           [path]
         else
           [])

let rec strip_parent_prefix path =
  if String.length path >= 3 && String.sub path 0 3 = "../" then
    strip_parent_prefix (String.sub path 3 (String.length path - 3))
  else
    path

let pretty_output_root = "_build/proverif_pv_pretty"

let workspace_root =
  match Sys.getenv_opt "DUNE_SOURCEROOT" with
  | Some root -> root
  | None -> Sys.getcwd ()

let rec ensure_dir path =
  if path = "" || path = "." || path = "/" then
    ()
  else if Sys.file_exists path then
    ()
  else begin
    ensure_dir (Filename.dirname path);
    Unix.mkdir path 0o755
  end

let write_pretty_output source_path contents =
  let relative_path = strip_parent_prefix source_path in
  let output_path =
    Filename.concat workspace_root (Filename.concat pretty_output_root relative_path)
  in
  ensure_dir (Filename.dirname output_path);
  let oc = open_out_bin output_path in
  Fun.protect
    ~finally:(fun () -> close_out_noerr oc)
    (fun () ->
      output_string oc contents;
      output_char oc '\n')

let parse_file path =
  try
    let ast1 = Pv_parser.parse_file path in
    let s1 = Pv_pp.to_string ast1 in
    write_pretty_output path s1;
    let ast2 = Pv_parser.parse_string ~filename:(path ^ "#roundtrip") s1 in
    let s2 = Pv_pp.to_string ast2 in
    if not (String.equal s1 s2) then
      Some
        (Printf.sprintf "%s\nRound-trip printer mismatch.\n--- first print ---\n%s\n--- second print ---\n%s"
           path s1 s2)
    else if Pv_ast_equal.equal_program ast1 ast2 then
      None
    else
      Some
        (Printf.sprintf "%s\nRound-trip AST mismatch after equal canonical prints.\n--- canonical print ---\n%s"
           path s1)
  with
  | Parsing_helper.InputError (message, extent) ->
      Some
        (Printf.sprintf "%s\n%s" path
           (Parsing_helper.get_mess_from true "Error: " message extent))
  | Sys_error message ->
      Some (Printf.sprintf "%s\n%s" path message)
  | exn ->
      Some (Printf.sprintf "%s\n%s" path (Printexc.to_string exn))

let run () =
  let files = collect_pv_files proverif_examples_dir in
  if files = [] then
    Proverif_pv_test_support.failwithf "No .pv files found under %s" proverif_examples_dir;
  let all_files = files @ indentation_example_files in
  let roundtrip_failures = List.filter_map parse_file all_files in
  let failures = roundtrip_failures in
  if failures <> [] then begin
    List.iter prerr_endline failures;
    Proverif_pv_test_support.failwithf
      "Failed to parse %d/%d ProVerif files"
      (List.length failures)
      (List.length all_files)
  end;
  Printf.printf "Round-tripped %d ProVerif files successfully.\n" (List.length all_files)

let () =
  run ()
