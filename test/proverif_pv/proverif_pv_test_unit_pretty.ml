open Rabbit_proverif_pv
module Parse = Rabbit_proverif_pv_parse
open Parse

let input_separator = "=== INPUT ==="

let parsed_separator = "=== PARSED ==="

let expected_separator = "=== EXPECTED ==="

let is_unit_pretty_case_file name =
  let len = String.length name in
  let starts_ok =
    len > 4 &&
    match name.[0] with
    | 'A' .. 'Z' | 'a' .. 'z' | '0' .. '9' -> true
    | _ -> false
  in
  starts_ok && Filename.check_suffix name ".txt"

let workspace_root =
  match Sys.getenv_opt "DUNE_SOURCEROOT" with
  | Some root -> root
  | None -> Sys.getcwd ()

let cases_dir_candidates =
  [
    Filename.concat workspace_root "test/proverif_pv/unit_pretty_cases";
    "test/proverif_pv/unit_pretty_cases";
    "unit_pretty_cases";
  ]

let cases_dir =
  match List.find_opt Sys.file_exists cases_dir_candidates with
  | Some dir -> dir
  | None ->
      Proverif_pv_test_support.failwithf
        "Unit pretty cases directory not found. Tried: %s"
        (String.concat ", " cases_dir_candidates)

let read_file path =
  let ic = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () ->
      let len = in_channel_length ic in
      really_input_string ic len)

let write_file path contents =
  let oc = open_out_bin path in
  Fun.protect
    ~finally:(fun () -> close_out_noerr oc)
    (fun () -> output_string oc contents)

let split_once ~sep s =
  let sep_len = String.length sep in
  let len = String.length s in
  let rec find i =
    if i + sep_len > len then
      None
    else if String.sub s i sep_len = sep then
      Some i
    else
      find (i + 1)
  in
  match find 0 with
  | None -> None
  | Some i ->
      let left = String.sub s 0 i in
      let right =
        String.sub s (i + sep_len) (len - i - sep_len)
      in
      Some (left, right)

let trim_edge_newlines s =
  let len = String.length s in
  let rec left i =
    if i < len && s.[i] = '\n' then
      left (i + 1)
    else
      i
  in
  let rec right i =
    if i > 0 && s.[i - 1] = '\n' then
      right (i - 1)
    else
      i
  in
  let i = left 0 in
  let j = right len in
  if i >= j then
    ""
  else
    String.sub s i (j - i)

let line_col_at s pos =
  let rec loop i line col =
    if i >= pos then
      (line, col)
    else if s.[i] = '\n' then
      loop (i + 1) (line + 1) 1
    else
      loop (i + 1) line (col + 1)
  in
  loop 0 1 1

let first_difference a b =
  let rec loop i =
    if i >= String.length a || i >= String.length b then
      if String.length a = String.length b then
        None
      else
        Some i
    else if Char.equal a.[i] b.[i] then
      loop (i + 1)
    else
      Some i
  in
  loop 0

let quoted_char_at s i =
  if i < 0 || i >= String.length s then
    "<eof>"
  else
    Printf.sprintf "%C" s.[i]

let explain_difference expected actual =
  match first_difference expected actual with
  | None -> "No textual difference found."
  | Some pos ->
      let line, col = line_col_at expected pos in
      Printf.sprintf
        "First difference at line %d, column %d.\n\
         expected char: %s\n\
         actual char:   %s"
        line col
        (quoted_char_at expected pos)
        (quoted_char_at actual pos)

let parse_or_fail ~filename ~context source =
  try Pv_parser.parse_string ~filename source with
  | Parsing.Parse_error ->
      Proverif_pv_test_support.failwithf
        "%s could not be parsed.\n--- source ---\n%s"
        context
        source

let load_unit_pretty_case path =
  let contents = read_file path in
  match split_once ~sep:expected_separator contents with
  | None ->
      Proverif_pv_test_support.failwithf
        "Unit pretty case %s is missing separator %S"
        path expected_separator
  | Some (before_expected, expected_pretty) ->
      begin match split_once ~sep:parsed_separator before_expected with
      | None ->
          Proverif_pv_test_support.failwithf
            "Unit pretty case %s is missing separator %S"
            path parsed_separator
      | Some (before_parsed, parsed_pretty) ->
          begin match split_once ~sep:input_separator before_parsed with
          | None ->
              Proverif_pv_test_support.failwithf
                "Unit pretty case %s is missing separator %S"
                path input_separator
          | Some (header, source) ->
              if trim_edge_newlines header <> "" then
                Proverif_pv_test_support.failwithf
                  "Unit pretty case %s has unexpected text before %S"
                  path input_separator;
              ( path,
                Filename.basename path,
                trim_edge_newlines source,
                trim_edge_newlines parsed_pretty,
                trim_edge_newlines expected_pretty )
          end
      end

let unit_pretty_cases =
  Sys.readdir cases_dir
  |> Array.to_list
  |> List.sort String.compare
  |> List.filter is_unit_pretty_case_file
  |> List.map (fun name -> load_unit_pretty_case (Filename.concat cases_dir name))

let fail_pretty_mismatch ~label ~name ~source ~expected ~actual =
  Proverif_pv_test_support.failwithf
    "Unit pretty test %s failed for %s.\n\
     %s\n\
     \n\
     --- input ---\n\
     %s\n\
     \n\
     --- expected %s ---\n\
     %s\n\
     \n\
     --- actual %s ---\n\
     %s"
    name
    label
    (explain_difference expected actual)
    source
    label
    expected
    label
    actual

let save_unit_pretty_case path ~source ~parsed ~expected =
  let contents =
    Printf.sprintf
      "%s\n%s\n%s\n%s\n%s\n%s\n"
      input_separator
      source
      parsed_separator
      parsed
      expected_separator
      expected
  in
  write_file path contents

let report_autofill path ~parsed_is_blank ~pretty_is_blank =
  let fields =
    match (parsed_is_blank, pretty_is_blank) with
    | true, true -> "PARSED and EXPECTED"
    | true, false -> "PARSED"
    | false, true -> "EXPECTED"
    | false, false -> assert false
  in
  Printf.eprintf "Autofilled %s in %s\n%!" fields path

let autofill_if_blank ~path ~source ~expected_parsed ~expected_pretty ~actual_parsed ~actual_pretty =
  let parsed_is_blank = String.equal expected_parsed "" in
  let pretty_is_blank = String.equal expected_pretty "" in
  if parsed_is_blank || pretty_is_blank then (
    let parsed =
      if parsed_is_blank then
        actual_parsed
      else
        expected_parsed
    in
    let expected =
      if pretty_is_blank then
        actual_pretty
      else
        expected_pretty
    in
    save_unit_pretty_case path ~source ~parsed ~expected;
    report_autofill path ~parsed_is_blank ~pretty_is_blank
  );
  let filled_parsed =
    if parsed_is_blank then
      actual_parsed
    else
      expected_parsed
  in
  let filled_pretty =
    if pretty_is_blank then
      actual_pretty
    else
      expected_pretty
  in
  (filled_parsed, filled_pretty)

let run_unit_pretty_case (path, name, source, expected_parsed, expected_pretty) =
  let ast1 =
    parse_or_fail
      ~filename:("<unit:" ^ name ^ ">")
      ~context:(Printf.sprintf "Unit pretty test %s input" name)
      source
  in
  let actual_parsed = Pv_pp.to_string_with_parens true ast1 |> trim_edge_newlines in
  let actual_pretty = Pv_pp.to_string ast1 |> trim_edge_newlines in
  let expected_parsed, expected_pretty =
    autofill_if_blank
      ~path
      ~source
      ~expected_parsed:(trim_edge_newlines expected_parsed)
      ~expected_pretty:(trim_edge_newlines expected_pretty)
      ~actual_parsed
      ~actual_pretty
  in
  if not (String.equal actual_parsed expected_parsed) then
    fail_pretty_mismatch
      ~label:"parsed"
      ~name
      ~source
      ~expected:expected_parsed
      ~actual:actual_parsed;
  if not (String.equal actual_pretty expected_pretty) then
    fail_pretty_mismatch
      ~label:"pretty"
      ~name
      ~source
      ~expected:expected_pretty
      ~actual:actual_pretty;
  let ast2 =
    parse_or_fail
      ~filename:("<unit:" ^ name ^ "#pretty>")
      ~context:(Printf.sprintf "Unit pretty test %s pretty output" name)
      actual_pretty
  in
  if not (Pv_ast_equal.equal_program ast1 ast2) then
    Proverif_pv_test_support.failwithf
      "Unit pretty test %s reparses to a different AST.\n\
       \n\
       --- input ---\n\
       %s\n\
       \n\
       --- parsed ---\n\
       %s\n\
       \n\
       --- pretty ---\n\
       %s"
      name
      source
      actual_parsed
      actual_pretty

let run () =
  List.iter run_unit_pretty_case unit_pretty_cases

let () =
  run ()
