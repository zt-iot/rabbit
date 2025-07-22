(** Clerial main program *)

(** The usage message. *)
let usage = "Usage: Rabbit [option] ... [file] ..."

(** A list of files to be loaded and run, together with information on whether they should
    be loaded in interactive mode. *)
let files = ref []

let ofile = ref None

let svg_file = ref false

(** Add a file to the list of files to be loaded, and record whether it should
    be processed in interactive mode. *)
let add_file filename = files := filename :: !files
let add_ofile filename = ofile := Some filename

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
     Arg.String (fun str -> add_file str),
     "<file> Load <file> into the initial environment");
(*
    ("--dev",
     Arg.Set Config.dev,
     "use the development version of tamarin"); *)

    ("--post-process",
     Arg.Set Config.optimize,
     " post-process to optimize the produced tamarin model");

     ("--tag-transition",
     Arg.Set Config.tag_transition,
     " post-process to optimize the produced tamarin model");

    ("-o",
     Arg.String (fun str -> add_ofile str),
     "<file> Printing the translated program into <file>");

    ("--svg",
     Arg.Set svg_file,
     " Output graph SVGs (requires graphviz)");
    ]

(** Main program *)
let _main =
  Sys.catch_break true ;
  (* Parse the arguments. *)
  Arg.parse
    options
    (fun str -> add_file str)
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
        List.fold_left (fun (env : Loader.env) fn ->
            let loader_result =
              try
                Ok (Loader.load fn env)
              with
              | exn -> Error exn
            in
            let typer_result =
              try
                let _, decls = Typer.load (Env.empty ()) fn in
                Ok decls
              with
              | (Typer.Error _ as exn) -> Error exn
              | exn ->
                  Format.eprintf "Typer unexpected exception: %s@." (Printexc.to_string exn);
                  Error exn
            in
            let res =
              match loader_result, typer_result with
              | Ok res, Ok _ ->
                  prerr_endline "TyperSuccess";
                  res
              | Error exn, Error (Typer.Error e) ->
                  Format.eprintf "TyperFail: %t: %t@." (Location.print e.loc) (Typer.print_error e.data);
                  raise exn
              | Error exn, Error exn' ->
                  Format.eprintf "TyperFail: %s@." (Printexc.to_string exn');
                  raise exn
              | Ok res, Error (Typer.Error e) ->
                  Format.eprintf "Unexpected TyperFail: %t: %t@." (Location.print e.loc) (Typer.print_error e.data); res
              | Ok res, Error exn ->
                  Format.eprintf "Unexpected TyperFail: %s@." (Printexc.to_string exn); res
              | Error exn, Ok _ ->
                  prerr_endline "Unexpected TyperSuccess";
                  raise exn
            in
            (* Semantics test *)
            (match typer_result with
             | Error _ -> ()
             | Ok decls ->
                 let compile_sem_to_spthy ext sem =
                   let spthy = Spthy.compile_sem sem in
                   match !ofile with
                   | None -> ()
                   | Some ofile ->
                       let ofile = ofile ^ ext in
                       Out_channel.with_open_text ofile @@ fun oc ->
                       let ppf = Format.formatter_of_out_channel oc in
                       Format.fprintf ppf "%a@." Spthy.print spthy;
                       if !svg_file then
                         Sem_debug.write_models_svg (ofile ^ ".svg")
                         @@ List.concat_map (function
                             | _id, Sem.Unbounded model -> [model]
                             | _id, Bounded (_p, models) -> models) sem.proc_groups
                 in

                 let sem = Sem.compile decls in

                 if not !Config.optimize then
                   compile_sem_to_spthy ".2" sem
                 else (
                   compile_sem_to_spthy ".1" sem;
                   let sem = Sem.optimize sem in
                   compile_sem_to_spthy ".2" sem
                 )
            );
            res
          )
          Loader.process_init !files
      in
      print_string "Loading complete..\n";
      (* XXX What happens if there are multiple systems? *)
      List.fold_left (fun _ s ->
          let t = Totamarin.translate_sys s (used_idents, used_strings) in
          let t =
            if !Config.optimize then
              { t with models= List.map (fun m -> Postprocessing.(move_eq_facts @@ optimize m)) t.models }
            else
              { t with models= List.map Postprocessing.move_eq_facts t.models }
          in
          let tamarin = Tamarin.print_tamarin t ~dev:!Config.dev ~print_transition_label:!Config.tag_transition in
          match !ofile with
          | None ->
              Print.message ~loc:Location.Nowhere "Warning:" "%s" "output file not specified"
          | Some ofile ->
              let oc = open_out ofile in
              Printf.fprintf oc "%s\n" tamarin;
              close_out oc;
              Print.message ~loc:Location.Nowhere "Translated into" "%s" ofile;
              if !svg_file then
                Tamarin_debug.write_tamarin_svg (ofile ^ ".svg") t
        ) () sys;
    ()

  with
  | Ulexbuf.Error {Location.data=err; Location.loc} ->
      Print.message ~loc "Parsing error" "%t" (Ulexbuf.print_error err);
      exit 1
  | Loader.Error {Location.data=err; Location.loc} ->
      Print.message ~loc "Syntax error" "%t" (Loader.print_error err);
      exit 1
  | Context.Error {Location.data=err; Location.loc} ->
      Print.message ~loc "Context error" "%t" (Context.print_error err);
      exit 1
  (* | Toxml.Error {Location.data=err; Location.loc} ->
    Print.message ~loc "ToXml error" "%t" (Toxml.print_error err) *)
  | Substitute.Error {Location.data=err; Location.loc} ->
      Print.message ~loc "Substitute error" "%t" (Substitute.print_error err);
      exit 1
  | Postprocessing.Error err ->
      Print.message ~loc:Location.Nowhere "Translate error" "%t" (Postprocessing.print_error err);
      exit 1
