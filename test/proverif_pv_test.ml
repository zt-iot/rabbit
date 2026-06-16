let failwithf fmt = Printf.ksprintf failwith fmt

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
      failwithf "ProVerif examples directory not found. Tried: %s"
        (String.concat ", " proverif_examples_dir_candidates)

let indentation_example_file_candidates =
  [
    [
      "src/proverif_pv/indentation_example.pv";
      "src/proverif_pv/indentation_example_process.pv";
    ];
    [
      "../src/proverif_pv/indentation_example.pv";
      "../src/proverif_pv/indentation_example_process.pv";
    ];
    [
      "../../src/proverif_pv/indentation_example.pv";
      "../../src/proverif_pv/indentation_example_process.pv";
    ];
  ]

let indentation_example_files =
  match List.find_opt (List.for_all Sys.file_exists) indentation_example_file_candidates with
  | Some files -> files
  | None ->
      failwithf "Indentation example files not found. Tried: %s"
        (String.concat " | "
           (List.map (String.concat ", ") indentation_example_file_candidates))

let indentation_pretty_file_candidates =
  [
    [
      ("src/proverif_pv/indentation_example.pv", "src/proverif_pv/indentation_example.pretty.pv");
      ("src/proverif_pv/indentation_example_process.pv", "src/proverif_pv/indentation_example_process.pretty.pv");
    ];
    [
      ("../src/proverif_pv/indentation_example.pv", "../src/proverif_pv/indentation_example.pretty.pv");
      ("../src/proverif_pv/indentation_example_process.pv", "../src/proverif_pv/indentation_example_process.pretty.pv");
    ];
    [
      ("../../src/proverif_pv/indentation_example.pv", "../../src/proverif_pv/indentation_example.pretty.pv");
      ("../../src/proverif_pv/indentation_example_process.pv", "../../src/proverif_pv/indentation_example_process.pretty.pv");
    ];
  ]

let indentation_pretty_files =
  match List.find_opt (List.for_all (fun (src, pretty) -> Sys.file_exists src && Sys.file_exists pretty)) indentation_pretty_file_candidates with
  | Some files -> files
  | None ->
      failwithf "Indentation pretty files not found. Tried: %s"
        (String.concat " | "
           (List.map
              (fun pairs ->
                String.concat ", " (List.map (fun (src, pretty) -> src ^ " -> " ^ pretty) pairs))
              indentation_pretty_file_candidates))

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
    let ast1 = Rabbit_proverif_pv.Pv_parser.parse_file path in
    let s1 = Rabbit_proverif_pv.Pv_pp.to_string ast1 in
    write_pretty_output path s1;
    let ast2 = Rabbit_proverif_pv.Pv_parser.parse_string ~filename:(path ^ "#roundtrip") s1 in
    let s2 = Rabbit_proverif_pv.Pv_pp.to_string ast2 in
    if not (String.equal s1 s2) then
      Some
        (Printf.sprintf "%s\nRound-trip printer mismatch.\n--- first print ---\n%s\n--- second print ---\n%s"
           path s1 s2)
    else if Rabbit_proverif_pv.Pv_ast_equal.equal_program ast1 ast2 then
      None
    else
      Some
        (Printf.sprintf "%s\nRound-trip AST mismatch after equal canonical prints.\n--- canonical print ---\n%s"
           path s1)
  with
  | Rabbit_proverif_pv.Parsing_helper.InputError (message, extent) ->
      Some
        (Printf.sprintf "%s\n%s" path
           (Rabbit_proverif_pv.Parsing_helper.get_mess_from true "Error: " message extent))
  | Sys_error message ->
      Some (Printf.sprintf "%s\n%s" path message)
  | exn ->
      Some (Printf.sprintf "%s\n%s" path (Printexc.to_string exn))

let compare_pretty_file (source_path, pretty_path) =
  try
    let source_ast = Rabbit_proverif_pv.Pv_parser.parse_file source_path in
    let pretty_ast = Rabbit_proverif_pv.Pv_parser.parse_file pretty_path in
    let source_pp = Rabbit_proverif_pv.Pv_pp.to_string source_ast in
    let pretty_pp = Rabbit_proverif_pv.Pv_pp.to_string pretty_ast in
    if String.equal source_pp pretty_pp
       && Rabbit_proverif_pv.Pv_ast_equal.equal_program source_ast pretty_ast
    then
      None
    else
      Some
        (Printf.sprintf
           "%s\nPretty print golden mismatch against %s.\n--- source canonical ---\n%s\n--- pretty canonical ---\n%s\n"
           source_path pretty_path source_pp pretty_pp)
  with
  | Rabbit_proverif_pv.Parsing_helper.InputError (message, extent) ->
      Some
        (Printf.sprintf "%s\n%s" source_path
           (Rabbit_proverif_pv.Parsing_helper.get_mess_from true "Error: " message extent))
  | Sys_error message ->
      Some (Printf.sprintf "%s\n%s" source_path message)
  | exn ->
      Some (Printf.sprintf "%s\n%s" source_path (Printexc.to_string exn))

let () =
  let files = collect_pv_files proverif_examples_dir in
  if files = [] then
    failwithf "No .pv files found under %s" proverif_examples_dir;
  let all_files = files @ indentation_example_files in
  let roundtrip_failures = List.filter_map parse_file all_files in
  let pretty_failures = List.filter_map compare_pretty_file indentation_pretty_files in
  let failures = roundtrip_failures @ pretty_failures in
  if failures <> [] then begin
    List.iter prerr_endline failures;
    failwithf "Failed to parse %d/%d ProVerif files" (List.length failures) (List.length all_files)
  end;
  Printf.printf "Round-tripped %d ProVerif files successfully.\n" (List.length all_files)
