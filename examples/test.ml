let failwithf fmt = Printf.ksprintf failwith fmt

let (!!) s = Re.compile @@ Re.Pcre.re s

type spec = Verified | Falsified

let string_of_spec = function
  | Verified -> "verified"
  | Falsified -> "falsified"

let spec_of_string = function
  | "verified" -> Verified
  | "falsified" -> Falsified
  | s -> failwithf "invalid spec: %S" s

let run (com : string) : int * string list =
  Format.eprintf "execute %s@." com;
  let ic = Unix.open_process_in com in
  let outputs = In_channel.input_lines ic in
  let exit =
    match Unix.close_process_in ic with
    | WEXITED n -> n
    | _ -> assert false
  in
  exit, outputs

let runf fmt = Printf.ksprintf run fmt

let test_file rab =

  let re = Re.compile @@ Re.Pcre.re {|lemma\s*(\w+)\s*:\s*\(\*\s*(\w*)\s*\*\)|} in
  In_channel.with_open_text rab @@ fun ic ->
  let lines = In_channel.input_lines ic in
  let specs = List.filter_map (fun line ->
      match Re.exec_opt re line with
      | None -> None
      | Some g ->
          let lemma_name = Re.Group.get g 1 in
          let result = Re.Group.get g 2 in
          Format.eprintf "spec: %s: %s@." lemma_name result;
          let result = spec_of_string result in
          Some (lemma_name, result)) lines
  in

  let module_ = Re.replace !!{|\.rab$|} ~f:(fun _ -> "") rab in
  Format.eprintf "module: %s@." module_;
  let spthy = module_ ^ ".spthy" in
  let out_spthy = "_" ^ spthy in
  let log = "_" ^ module_ ^ ".log" in
  let write_log lines =
    let log_oc = open_out log in
    List.iter (fun s -> output_string log_oc s; output_char log_oc '\n') lines;
    close_out log_oc
  in
  if Sys.file_exists out_spthy then Unix.unlink out_spthy;
  let res, output =
    (* [cd ..] is required *)
    runf "cd ..; opam exec -- dune exec src/rabbit.exe -- examples/%s -o examples/%s --post-process --tag-transition 2>&1" rab out_spthy
  in
  write_log output;
  (match res with
   | 0 ->
       Format.eprintf "%s: compiled@." rab
   | _ ->
       Format.eprintf "%s: %d compilation failed@." rab res;
       List.iter prerr_endline output;
       exit 2);

  (* Compare the spthys *)
  if Sys.file_exists spthy then
    let res, output = runf "diff %s %s" spthy out_spthy in
    (match res with
     | 0 -> ()
     | _ ->
         Format.eprintf "%s: different from %s@." out_spthy spthy;
         List.iter prerr_endline output;
         exit 2);
  else
    ignore @@ runf "cp %s %s" out_spthy spthy;

  (* Verification *)
  let _res, output = runf "tamarin-prover %s --prove= 2>&1" spthy in
  (* Tamarin does not return meaningful exit code. *)

  let rec skip = function
    | "summary of summaries:" :: ls -> String.make 78 '=' :: ls
    | _ :: ls -> skip ls
    | [] -> []
  in
  let summary = skip output in

  List.iter prerr_endline summary;

  let re = Re.compile @@ Re.Pcre.re {|(\w+) \([^)]*\): (\w+)|} in
  let results = List.filter_map (fun line ->
      match Re.exec_opt re line with
      | None -> None
      | Some g ->
          let lemma_name = Re.Group.get g 1 in
          let result = Re.Group.get g 2 in
          Format.eprintf "result: %s: %s@." lemma_name result;
          let result = spec_of_string result in
          Some (lemma_name, result)) summary
  in

  let fail = ref false in
  List.iter (fun (lemma_name, expected) ->
      match List.assoc_opt lemma_name results with
      | None ->
          Format.eprintf "%s: no result - Oops@." lemma_name;
          fail := true
      | Some result ->
        if result = expected then
          Format.eprintf "%s: %s - Ok@." lemma_name (string_of_spec result)
        else (
          Format.eprintf "%s: %s - Oops@." lemma_name (string_of_spec result);
          fail := true
        )
    ) specs;

  if !fail then (
    Format.eprintf "Oops, something went wrong@.";
    exit 1
  ) else (
    Format.eprintf "Ok, everything went fine@.";
    exit 0
  )


let () =
  let rev_files = ref [] in
  let () = Arg.parse [] (fun fn -> rev_files := fn :: !rev_files) "test files" in
  let files = List.rev !rev_files in
  List.iter test_file files
