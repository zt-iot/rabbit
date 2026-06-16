let failwithf fmt = Printf.ksprintf failwith fmt

let example_candidates =
  [
    [
      ( "src/proverif_pv/indentation_example.pv",
        "src/proverif_pv/indentation_example.pretty.pv" );
      ( "src/proverif_pv/indentation_example_process.pv",
        "src/proverif_pv/indentation_example_process.pretty.pv" );
    ];
    [
      ( "../src/proverif_pv/indentation_example.pv",
        "../src/proverif_pv/indentation_example.pretty.pv" );
      ( "../src/proverif_pv/indentation_example_process.pv",
        "../src/proverif_pv/indentation_example_process.pretty.pv" );
    ];
    [
      ( "../../src/proverif_pv/indentation_example.pv",
        "../../src/proverif_pv/indentation_example.pretty.pv" );
      ( "../../src/proverif_pv/indentation_example_process.pv",
        "../../src/proverif_pv/indentation_example_process.pretty.pv" );
    ];
  ]

let examples =
  match
    List.find_opt
      (List.for_all (fun (src, _) -> Sys.file_exists src))
      example_candidates
  with
  | Some files -> files
  | None ->
      failwithf "Indentation example files not found. Tried: %s"
        (String.concat " | "
           (List.map
              (fun pairs ->
                String.concat ", " (List.map fst pairs))
              example_candidates))

let write_file path contents =
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
      Rabbit_proverif_pv.Param.reset ();
      let lexbuf = Lexing.from_channel ic in
      lexbuf.Lexing.lex_curr_p <-
        { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = path };
      try
        Rabbit_proverif_pv.Pitparser.all Rabbit_proverif_pv.Pitlexer.token lexbuf
      with
      | Parsing.Parse_error ->
          let p = lexbuf.Lexing.lex_curr_p in
          failwithf "Parse error in %s at line %d, column %d"
            path
            p.Lexing.pos_lnum
            (p.Lexing.pos_cnum - p.Lexing.pos_bol)
      | Rabbit_proverif_pv.Parsing_helper.InputError (message, extent) ->
          failwith
            (Rabbit_proverif_pv.Parsing_helper.get_mess_from true "Error: " message extent))

let generate_one (src, dst) =
  let ast = parse_file src in
  let pretty = Rabbit_proverif_pv.Pv_pp.to_string ast in
  write_file dst pretty;
  Printf.printf "Wrote %s from %s\n" dst src

let () = List.iter generate_one examples
