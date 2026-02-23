let usage = "-o [output_file] [file]"
let file = ref None
let ofile = ref None
let auxfile = ref None
let add_file filename = file := Some filename
let add_ofile filename = ofile := Some filename
let add_auxfile filename = auxfile := Some filename

let options =
  Arg.align
    [ ( "-o"
      , Arg.String (fun str -> add_ofile str)
      , "<file> Printing the trace graph into <file>" )
    ; "--with", Arg.String (fun str -> add_auxfile str), " Use auxiliary metadata"
    ]
;;

let load_file fn =
  try Ok (Input.load fn) with
  | exn -> Error exn
;;

let translate_graph metadata str decl =
  let out_graph = Translate.translate decl metadata in
  let out_string = Graph.string_of_graph out_graph in
  str ^ out_string ^ "\n"
;;

let run file =
  let decls =
    match load_file file with
    | Ok decls -> decls
    | Error exn -> raise exn
  in
  let decls, metadata =
    match !auxfile with
    | None -> decls, None
    | Some filename ->
        let metadata = Usemeta.load_file filename in
        List.map (Usemeta.use_metadata metadata) decls, Some metadata
  in
  let output = List.fold_left (translate_graph metadata) "" decls in
  match !ofile with
  | None -> ()
  | Some ofile ->
      let oc = open_out ofile in
      Printf.fprintf oc "%s\n" output;
      close_out oc
;;

let () =
  Sys.catch_break true;
  Arg.parse options (fun str -> add_file str) usage;
  try
    match !file with
    | Some filename ->
        run filename;
        Format.printf "Success.";
        (match !ofile with
         | None -> ()
         | Some ofile -> Format.printf " (Output: %s)" ofile);
        Format.printf "@."
    | None ->
        Format.eprintf "Error: No input file specified.@.";
        Arg.usage options usage;
        exit 1
  with
  | Ulexbuf.Error { Location.data = err; Location.loc } ->
      Print.message ~loc "Parsing error" "%t" (Ulexbuf.print_error err);
      exit 1
  | exn ->
      Format.eprintf "%s@." (Printexc.to_string exn);
      exit 1
;;
