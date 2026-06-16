let failwithf fmt = Printf.ksprintf failwith fmt

module Parse = Rabbit_proverif_pv_parse

let workspace_root =
  match Sys.getenv_opt "DUNE_SOURCEROOT" with
  | Some root -> root
  | None -> Sys.getcwd ()

let output_root =
  Filename.concat workspace_root "_build/proverif_pv_pretty_examples"

let example_candidates =
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

let examples =
  match
    List.find_opt
      (List.for_all Sys.file_exists)
      example_candidates
  with
  | Some files -> files
  | None ->
      failwithf "Indentation example files not found. Tried: %s"
        (String.concat " | "
           (List.map
              (fun files ->
                String.concat ", " files)
              example_candidates))

let rec ensure_dir path =
  if path = "" || path = "." || path = "/" then
    ()
  else if Sys.file_exists path then
    ()
  else begin
    ensure_dir (Filename.dirname path);
    Unix.mkdir path 0o755
  end

let write_file path contents =
  ensure_dir (Filename.dirname path);
  let oc = open_out_bin path in
  Fun.protect
    ~finally:(fun () -> close_out_noerr oc)
    (fun () ->
      output_string oc contents;
      output_char oc '\n')

let parse_file path =
  let ic = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () ->
      Parse.Param.reset ();
      let lexbuf = Lexing.from_channel ic in
      lexbuf.Lexing.lex_curr_p <-
        { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = path };
      try
        Parse.Pitparser.all Parse.Pitlexer.token lexbuf
      with
      | Parsing.Parse_error ->
          let p = lexbuf.Lexing.lex_curr_p in
          failwithf "Parse error in %s at line %d, column %d"
            path
            p.Lexing.pos_lnum
            (p.Lexing.pos_cnum - p.Lexing.pos_bol)
      | Parse.Parsing_helper.InputError (message, extent) ->
          failwith
            (Parse.Parsing_helper.get_mess_from true "Error: " message extent))

let generate_one src =
  let ast = parse_file src in
  let pretty = Rabbit_proverif_pv.Pv_pp.to_string ast in
  let dst =
    Filename.concat output_root (Filename.basename src ^ ".pretty.pv")
  in
  write_file dst pretty;
  Printf.printf "Wrote %s from %s\n" dst src

let () = List.iter generate_one examples
