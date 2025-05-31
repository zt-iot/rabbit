let failwithf fmt = Printf.ksprintf failwith fmt

let re_boundary = Re.compile @@ Re.Pcre.re {|^\(\*\*\*|}

module Camlon = struct
  let parse str =
    Lexer.init ();
    Parser.parse_expression Lexer.token (Lexing.from_string str)
end

module Test = struct
  type t =
    | Success (* [Success] *)
    | Fail of Re.re (* [Fail: expected output regexp] *)

  let parse s =
    let re_head = Re.compile @@ Re.Pcre.re {|^\(\*\*\*(.*)\*\)|} in
    match Re.exec_opt re_head s with
    | None -> failwithf "Invalid test: %s" s
    | Some g ->
        let spec = Re.Group.get g 1 in
        let e = Camlon.parse spec in
        match e.pexp_desc with
        | Pexp_construct ({txt= Lident "Success"; _}, None) -> Success
        | Pexp_construct ({txt= Lident "Fail"; _},
                          Some {pexp_desc= Pexp_constant (Pconst_string (s, _, _)); _}
                         ) -> Fail (Re.compile @@ Re.Pcre.re s)
        | _ -> failwithf "Bad spec: %s" spec
end

let test_block lines =
  assert (lines <> []);
  let fn = Filename.temp_file "test" ".rab" in
  prerr_endline ("---------------------- " ^ fn);
  Out_channel.with_open_text fn (fun oc ->
      List.iter (fun line ->
          output_string oc line;
          output_char oc '\n') lines);
  let test = Test.parse @@ List.hd lines in
  (* [cd ..] is required *)
  let ic = Unix.open_process_in (Printf.sprintf "cd ..; opam exec dune exec src/rabbit.exe %s 2>&1" fn) in
  let outputs = In_channel.input_lines ic in
  match test, Unix.close_process_in ic with
  | Success, WEXITED 0 ->
      prerr_endline "Successful"
  | Success, WEXITED _ ->
      prerr_endline "Unexpected failure:";
      List.iter prerr_endline lines;
      List.iter prerr_endline outputs;
      exit 2
  | Fail _rex, WEXITED 0 ->
      Format.eprintf "Unexpected success. Must fail with %s@." (List.hd lines);
      List.iter prerr_endline lines;
      List.iter prerr_endline outputs;
      exit 2
  | Fail rex, WEXITED (1 | 2) ->
      if List.exists (Re.execp rex) outputs then
        prerr_endline "Failed as expected"
      else begin
        List.iter prerr_endline lines;
        List.iter prerr_endline outputs;
        prerr_endline "Unexpected error message";
        exit 2
      end
  | _ -> assert false

let split_file fn =
  let lines =
    In_channel.with_open_text fn @@ fun ic ->
    In_channel.input_lines ic
  in
  let rec split_lines rev_lines rev_groups = function
    | [] ->
        let rev_groups =
          if rev_lines = [] then rev_groups
          else List.rev rev_lines :: rev_groups
        in
        List.rev rev_groups
    | l::ls when Re.execp re_boundary l ->
        let rev_groups =
          if rev_lines = [] then rev_groups
          else (List.rev rev_lines)::rev_groups
        in
        split_lines [l] rev_groups ls
    | l::ls ->
        split_lines (l::rev_lines) rev_groups ls
  in
  split_lines [] [] lines

let test_file fn =
  let blocks = split_file fn in
  List.iter test_block blocks

let () =
  let rev_files = ref [] in
  let () = Arg.parse [] (fun fn -> rev_files := fn :: !rev_files) "test files" in
  let files = List.rev !rev_files in
  List.iter test_file files
