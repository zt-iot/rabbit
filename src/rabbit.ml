(** Clerial main program *)

(** The usage message. *)
let usage = "Usage: Rabbit [option] ... [file] ..."

(** A list of files to be loaded and run, together with information on whether they should
    be loaded in interactive mode. *)
let files = ref []

let ofile = ref None

let svg_file = ref false

(** [Some `Main] to use the new compiler pipeline: [Typer], [Sem], [Spthy]
    [Some `Test] to run it along with the original one.
*)
let new_compiler = ref (Some `Main) (* default is using the new compiler by Jun *)

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

    ("--compress",
     Arg.Set Config.optimize,
     "<bool> Enable of disable compressing produced Tamarin model");

    ("--tag-transition",
     Arg.Bool (fun b -> Config.tag_transition := b),
     "<bool> Enable or disable tagging transitions in produced Tamarin model");

    ("-o",
     Arg.String (fun str -> add_ofile str),
     "<file> Printing the translated Tamarin program into <file>");

    ("--svg",
     Arg.Set svg_file,
     " Output graph SVGs (requires graphviz)");

    ("--old",
     Arg.Unit (fun () -> new_compiler := Some `Main),
     " Use the legacy compiler");

    ("--test-new",
     Arg.Unit (fun () -> new_compiler := Some `Test),
     " Test new compiler along with the legacy compiler for develop purpose");
    ]

let load_file (env : Loader.env) fn =
  try
    Ok (Loader.load fn env)
  with
  | exn -> Error exn

let new_load_file fn =
  try
    (* The new compiler loads each file with the empty env *)
    Ok (snd @@ Typer.load (Env.empty ()) fn)
  with
  | (Typer.Error _ as exn) -> Error exn
  | exn ->
      Format.eprintf "Typer unexpected exception: %s@." (Printexc.to_string exn);
      Error exn

let compare_load_results res new_res =
  (* Compare the results of the original and new and report them to stderr *)
  match res, new_res with
  | Ok _, Ok _ ->
      prerr_endline "TyperSuccess"
  | Error _exn, Error (Typer.Error e) ->
      Format.eprintf "TyperFail: %t: %t@." (Location.print e.loc) (Typer.print_error e.data);
  | Error _exn, Error exn' ->
      Format.eprintf "TyperFail: %s@." (Printexc.to_string exn');
  | Ok _, Error (Typer.Error e) ->
      Format.eprintf "Unexpected TyperFail: %t: %t@." (Location.print e.loc) (Typer.print_error e.data)
  | Ok _, Error exn ->
      Format.eprintf "Unexpected TyperFail: %s@." (Printexc.to_string exn)
  | Error _, Ok _ ->
      prerr_endline "Unexpected TyperSuccess"

let translate_system (used_idents, used_strings) s =
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

(* [ext] is to give a different path than the original output files
   when [!new_copmiler = Some `Test] *)
let new_translate_system ext decls =
  let sem = Sem.compile decls in
  let sem = if !Config.optimize then Sem.optimize sem else sem in
  (match !ofile, !svg_file with
   | Some ofile, true ->
       Sem_debug.write_models_svg (ofile ^ ext ^ ".svg")
       @@ List.concat_map (function
           | _id, Sem.Unbounded model -> [model]
           | _id, Bounded (_p, models) -> models) sem.proc_groups
   | None, _ | _, false -> ());
  let spthy = Spthy.compile_sem sem in
  (match !ofile with
   | None -> ()
   | Some ofile ->
       Out_channel.with_open_text (ofile ^ ext) @@ fun oc ->
       let ppf = Format.formatter_of_out_channel oc in
       Format.fprintf ppf "%a@." Spthy.print spthy)

let wrap_exn f = try Ok (f ()) with exn -> Error exn

let run files =
  match !new_compiler with
  | None ->
      (* Only the original compiler *)
      let Loader.{ system= sys; used_idents; used_strings; _ } =
        List.fold_left (fun env fn ->
            match load_file env fn with
            | Ok res -> res
            | Error exn -> raise exn) Loader.process_init !files
      in
      print_string "Loading complete..\n";
      (* XXX Bug: this cannot handle multiple systems properly *)
      List.iter (translate_system (used_idents, used_strings)) sys
  | Some `Main ->
      (* Only the new compiler *)
      let decls = List.concat_map (fun fn ->
          match new_load_file fn with
          | Ok decls -> decls
          | Error exn -> raise exn
        ) !files
      in
      new_translate_system "" decls
  | Some `Test ->
      (* Run the new compiler along with the original one *)
      let Loader.{ system= sys; used_idents; used_strings; _ }, (decls : (Typed.decl list, exn) result) =
        List.fold_left (fun ((env : Loader.env), decls) fn ->
            let res = load_file env fn in
            let new_res = new_load_file fn in
            let may_raise = function
              | Ok x -> x
              | Error exn -> raise exn
            in
            compare_load_results res new_res;
            may_raise res,
            match decls, new_res with
            | Error exn, _ | _, Error exn -> Error exn
            | Ok decls, Ok decls' -> Ok (decls @ decls'))
          (Loader.process_init, Ok []) !files
      in
      print_string "Loading complete..\n";
      (* XXX Bug: this cannot handle multiple systems properly *)
      let res =
        wrap_exn @@ fun () -> List.iter (translate_system (used_idents, used_strings)) sys
      in
      let new_res =
        match decls with
        | Error exn -> Error exn
        | Ok decls -> wrap_exn @@ fun () -> new_translate_system ".2" decls
      in
      match res, new_res with
      | Ok _, Ok _ -> ()
      | Error exn, _ -> raise exn
      | Ok _, Error (Typer.Error _ | Sem.Error _) -> () (* Well-defined errors are ignored for test/test.exe *)
      | Ok _, Error exn -> raise exn

(** Main program *)
let () =
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

  try
    run files
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
  | Typer.Error err ->
      Print.message ~loc:err.loc "Typer error" "%t" (Typer.print_error err.data);
      exit 1
