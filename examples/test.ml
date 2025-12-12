let (!!) s = Re.compile @@ Re.Pcre.re s

type spec = Verified | Falsified | Other of string

let string_of_spec = function
  | Verified -> "verified"
  | Falsified -> "falsified"
  | Other s -> s

let spec_of_string = function
  | "verified" -> Verified
  | "falsified" -> Falsified
  | s -> Other s

let run (com : string) : int * string list =
  Format.printf "execute %s@." com;
  let ic = Unix.open_process_in com in
  let outputs = In_channel.input_lines ic in
  let exit =
    match Unix.close_process_in ic with
    | WEXITED n -> n
    | _ -> assert false
  in
  exit, outputs

let with_time f =
  let start = Unix.gettimeofday () in
  let res = f () in
  let end_ = Unix.gettimeofday () in
  res, end_ -. start

let runf fmt = Printf.ksprintf run fmt

let verify ~no_auto specs spthy =

  let proves =
    if no_auto then
      (* Only specified in [spec] *)
      String.concat " " @@ List.map (fun (s, _) -> Printf.sprintf "--prove=%s" s) specs
    else "--prove=" (* prove all *)
  in

  (* Verification *)
  let res, output = runf "tamarin-prover %s %s 2>&1" spthy proves in

  if res <> 0 then
    ( Format.printf "tamarin-prover failed with return code %d!@." res;
      print_endline @@ String.make 78 '=';
      print_endline @@ String.concat "\n" output;
      print_endline @@ String.make 78 '=';
      true
    )
  else (
    let rec skip = function
      | "summary of summaries:" :: ls -> String.make 78 '=' :: ls
      | _ :: ls -> skip ls
      | [] -> []
    in
    let summary = skip output in

    List.iter print_endline summary;

    let re = Re.compile @@ Re.Pcre.re {|(\w+) \([^)]*\): (\w+)|} in
    let results = List.filter_map (fun line ->
        match Re.exec_opt re line with
        | None -> None
        | Some g ->
            let lemma_name = Re.Group.get g 1 in
            let result = Re.Group.get g 2 in
            (* Format.printf "result: %s: %s@." lemma_name result; *)
            let result = spec_of_string result in
            Some (lemma_name, result)) summary
    in

    let fail = ref false in
    List.iter (fun (lemma_name, result) ->
        let expected =
          match List.assoc_opt lemma_name specs with
          | None when no_auto -> None
          | None -> Some Verified
          | Some spec -> Some spec
        in
        match expected with
        | None ->
            Format.printf "%s: %s - Ignored@." lemma_name (string_of_spec result)
        | Some expected ->
            if result = expected then
              Format.printf "%s: %s - Ok@." lemma_name (string_of_spec result)
            else (
              Format.printf "%s: %s - Oops@." lemma_name (string_of_spec result);
              fail := true
            )
      ) results;

    List.iter (fun (lemma_name, _spec) ->
        if not @@ List.mem_assoc lemma_name results then (
          Format.printf "%s: no result - Oops@." lemma_name;
          fail := true
        )
      ) specs;

    if !fail then (
      Format.printf "%s: Oops, something went wrong@.@." spthy;
    ) else (
      Format.printf "%s: Ok, everything went fine@.@." spthy;
    );
    !fail
  )

let test_file ~no_auto rab =
  let module_ = Re.replace !!{|\.rab$|} ~f:(fun _ -> "") rab in
  Format.printf "Testing module: %s@." module_;

  let re = Re.compile @@ Re.Pcre.re {|lemma\s*(\w+)\s*:\s*\(\*\s*(\w*)\s*\*\)|} in
  In_channel.with_open_text rab @@ fun ic ->
  let lines = In_channel.input_lines ic in
  let specs = List.filter_map (fun line ->
      match Re.exec_opt re line with
      | None -> None
      | Some g ->
          let lemma_name = Re.Group.get g 1 in
          let result = Re.Group.get g 2 in
          Format.printf "spec: %s: %s@." lemma_name result;
          let result = spec_of_string result in
          Some (lemma_name, result)) lines
  in

  let spthy = module_ ^ ".spthy" in
  let out_spthy = "_" ^ spthy in
  let out_spthy_2 = "_" ^ spthy ^ ".2" in
  let log = "_" ^ module_ ^ ".log" in
  let write_log lines =
    let log_oc = open_out log in
    List.iter (fun s -> output_string log_oc s; output_char log_oc '\n') lines;
    close_out log_oc
  in
  if Sys.file_exists out_spthy then Unix.unlink out_spthy;
  let res, output =
    (* [cd ..] is required *)
    runf "cd ..; opam exec -- dune exec src/rabbit.exe -- --test-new examples/%s -o examples/%s --svg 2>&1" rab out_spthy
  in
  write_log output;
  (match res with
   | 0 ->
       Format.printf "%s: compiled@." rab
   | _ ->
       Format.printf "%s: %d compilation failed@." rab res;
       List.iter print_endline output;
       exit 2);

  (* Compare the spthys *)
  if Sys.file_exists spthy then
    let res, output = runf "diff -c %s %s" spthy out_spthy in
    (match res with
     | 0 -> ()
     | _ ->
         Format.printf "%s: different from the expected output %s@." out_spthy spthy;
         List.iter print_endline output;
         exit 2);
  else
    ignore @@ runf "cp %s %s" out_spthy spthy;

  let res, time = with_time @@ fun () -> verify ~no_auto specs out_spthy in
  let res2, time2 = with_time @@ fun () -> verify ~no_auto specs out_spthy_2 in
  res || res2, time, time2


let () =
  let rev_files = ref [] in
  let no_auto = ref false in
  let () = Arg.parse [
      "--no-auto-lemmas", Arg.Set no_auto, " Do not prove auto-generated lemmas such as TransitionOnce"
    ] (fun fn -> rev_files := fn :: !rev_files) "test files" in
  let files = List.rev !rev_files in
  let results =
    List.map (fun fn ->
        fn, with_time @@ fun () -> test_file ~no_auto:!no_auto fn) files
  in
  Format.printf "Test summary:@.";
  List.iter (fun (fn, ((res, secs1, secs2), secs)) ->
      Format.printf "- %s: %s (%.2f secs, verification: [original %.2f; new %.2f]) %s@."
        fn (if res then "Failure" else "Ok") secs secs1 secs2
        (* If the times are very different worth warning them *)
        (if secs1 /. secs2 > 2.0 || secs2 /. secs1 > 1.5 then "!!!" else "")
    ) results;
  let has_failure = List.exists (function (_,((true, _, _),_)) -> true | _ -> false) results in
  exit (if has_failure then 1 else 0)
