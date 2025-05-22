(** Clerial main program *)

(** The usage message. *)
let usage = "Usage: Rabbit [option] ... [file] ..."

(** A list of files to be loaded and run, together with information on whether they should
    be loaded in interactive mode. *)
let files = ref []

let ofile = ref ("", false)

(** Add a file to the list of files to be loaded, and record whether it should
    be processed in interactive mode. *)
let add_file quiet filename = (files := (filename, quiet) :: !files)
let add_ofile quiet filename = (ofile := (filename, quiet))

(** Command-line options *)
let options = Arg.align [

    ("--columns",
     Arg.Set_int Config.columns,
     " Set the maximum number of columns of pretty printing");

    ("-v",
     Arg.Unit (fun () ->
         Format.printf "Rabbit- %s (%s)@." Build.version Sys.os_type ;
         exit 0),
     " Print version information and exit");

    ("-l",
     Arg.String (fun str -> add_file true str),
     "<file> Load <file> into the initial environment");
(*
    ("--dev",
     Arg.Set Config.dev,
     "use the development version of tamarin"); *)

    ("--post-process",
     Arg.Set Config.optimize,
     "post-process to optimize the produced tamarin model");

     ("--tag-transition",
     Arg.Set Config.tag_transition,
     "post-process to optimize the produced tamarin model");

    ("-o",
     Arg.String (fun str -> add_ofile true str),
     "<file> Printing the translated program into <file>");
    ]

(** Main program *)
let _main =
  Sys.catch_break true ;
  (* Parse the arguments. *)
  Arg.parse
    options
    (fun str -> add_file false str)
    usage ;
  (* Files were accumulated in the wrong order, so we reverse them *)
  files := List.rev !files ;

  (* Set the maximum depth of pretty-printing, after which it prints ellipsis. *)
  Format.set_max_boxes !Config.max_boxes ;
  Format.set_margin !Config.columns ;
  Format.set_ellipsis_text "..." ;
  (* try *)
    (* Run and load all the specified files. *)
    (* let _ = Desugar.load (fst (List.hd !files)) Desugar.ctx_init Desugar.pol_init Desugar.def_init in  *)
  try
      let Loader.{ system= sys; used_idents; used_strings; _ } =
        List.fold_left (fun (env : Loader.env) (fn, _quiet) -> Loader.load fn env)
          Loader.process_init !files
      in
      print_string "Loading complete..\n";
      List.fold_left (fun _ s ->
          let t = Totamarin.translate_sys s (used_idents, used_strings) in
          let t =
            if !Config.optimize then Tamarin.{ t with models= List.map Postprocessing.optimize t.models }
            else t
          in
          let tamarin = (Tamarin.print_tamarin t !Config.dev !Config.tag_transition) in
          if fst !ofile = "" then Print.message ~loc:Location.Nowhere "Error" "%s" "output file not specified"
          else let oc = open_out (fst !ofile) in
            Printf.fprintf oc "%s\n" tamarin;
            close_out oc;
            Print.message ~loc:Location.Nowhere "Translated into" "%s" (fst !ofile)
        ) () sys;
    ()

  with
  | Ulexbuf.Error {Location.data=err; Location.loc} ->
    Print.message ~loc "Parsing error" "%t" (Ulexbuf.print_error err)
  | Loader.Error {Location.data=err; Location.loc} ->
    Print.message ~loc "Syntax error" "%t" (Loader.print_error err)
  | Context.Error {Location.data=err; Location.loc} ->
    Print.message ~loc "Context error" "%t" (Context.print_error err)
  (* | Toxml.Error {Location.data=err; Location.loc} ->
    Print.message ~loc "ToXml error" "%t" (Toxml.print_error err) *)
  | Substitute.Error {Location.data=err; Location.loc} ->
    Print.message ~loc "Substitute error" "%t" (Substitute.print_error err)
  | Postprocessing.Error err ->
    Print.message ~loc:Location.Nowhere "Translate error" "%t" (Postprocessing.print_error err)
