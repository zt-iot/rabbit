open Ppxlib

let failwithf fmt = Printf.ksprintf failwith fmt

let re_boundary = Re.compile @@ Re.Pcre.re {|^\(\*\*\*|}

let re_falsified = Re.compile @@ Re.Pcre.re {|falsified|}

let re_typerfail = Re.compile @@ Re.Pcre.re {|TyperFail|}

let re_typersuccess = Re.compile @@ Re.Pcre.re {|TyperSuccess|}

module Camlon = struct
  let parse str =
    Lexer.init ();
    Parse.expression (Lexing.from_string str)
end

module Test = struct
  type t =
    | Success (** Syntax check passes *)
    | Fail of Re.re (** Syntax check fails and the output matches with rex *)
    | Verified (** Verified *)
    | Falsified (** Falsified *)
    | TyperSuccess (** Typer success *)
    | TyperFail of Re.re (** Typer fails and the output matches with rex *)

  let verification_required = function
    | Verified | Falsified -> true
    | _ -> false

  let parse s =
    (* let re_head = Re.compile @@ Re.Pcre.re {|^\(\*\*\*(.*)      (*               \*\)|} in *)
    match Re.exec_opt re_head s with
    | None -> failwithf "Invalid test: %s" s
    | Some g ->
        let spec = Re.Group.get g 1 in
        let e = Camlon.parse spec in
        let rex s = Re.compile @@ Re.Pcre.re s in
        let rec parse_expr (e : Parsetree.expression) =
          match e.pexp_desc with
          | Pexp_construct ({txt= Lident "Success"; _}, None) -> [Success]
          | Pexp_construct ({txt= Lident "TyperSuccess"; _}, None) -> [TyperSuccess]
          | Pexp_construct ({txt= Lident "Verified"; _}, None) -> [Verified]
          | Pexp_construct ({txt= Lident "Falsified"; _}, None) -> [Falsified]
          | Pexp_construct ({txt= Lident "Fail"; _},
                            Some {pexp_desc= Pexp_constant (Pconst_string (s, _, _)); _}
                           ) -> [Fail (rex s)]
          | Pexp_construct ({txt= Lident "TyperFail"; _},
                            Some {pexp_desc= Pexp_constant (Pconst_string (s, _, _)); _}
                           ) -> [TyperFail (rex s)]
          | Pexp_tuple exps -> List.concat_map parse_expr exps
          | _ -> failwithf "Bad spec: %s" spec
        in
        parse_expr e
end

let run_check_syntax fn =
  (* [cd ..] is required *)
  let com = Printf.sprintf "cd ..; opam exec -- dune exec -- src/rabbit.exe %s -o %s.spthy 2>&1" fn fn in
  let ic = Unix.open_process_in com in
  let outputs = In_channel.input_lines ic in
  let res =
    match Unix.close_process_in ic with
    | WEXITED 0 -> true
    | _ -> false
  in
  res, outputs

let run_verify fn =
  let ic = Unix.open_process_in (Printf.sprintf "tamarin-prover %s.spthy --prove=" fn) in
  let outputs = In_channel.input_lines ic in
  let res =
    match Unix.close_process_in ic with
    | WEXITED 0 ->
        if List.exists (Re.execp re_falsified) outputs then `Falsified
        else `Verified
    | _ -> `Crashed
  in
  res, outputs

let test specs fn =
  let success_syntax, outputs_syntax = run_check_syntax fn in
  let res_verify, outputs_verify =
    if List.exists Test.verification_required specs then
      run_verify fn
    else
      `None, []
  in
  let typerfail = List.exists (Re.execp re_typerfail) outputs_syntax in
  let typersuccess = List.exists (Re.execp re_typersuccess) outputs_syntax in
  let specs : Test.t list =
    (* mend specs *)
    if
      (* Verified and Falsified imply Success *)
      (List.mem Test.Verified specs
       || List.mem Test.Falsified specs)
      && (not @@ List.mem Test.Success specs)
    then
      Success :: specs
    else specs
  in
  List.iter (function
      | Test.Success ->
          if success_syntax then
            prerr_endline "Syntax check succeeded"
          else (
            prerr_endline "Syntax check failed";
            List.iter prerr_endline outputs_syntax;
            exit 2
          )
      | Fail rex ->
          if success_syntax then (
            prerr_endline "Syntax check successed unexpectedly";
            List.iter prerr_endline outputs_syntax;
            exit 2
          ) else
          if List.exists (Re.execp rex) outputs_syntax then
            prerr_endline "Syntax check failed as expected"
          else (
            prerr_endline "Syntax check failed unexpectedly";
            List.iter prerr_endline outputs_syntax;
            exit 2
          )
      | Verified ->
          (match res_verify with
           | `Verified -> prerr_endline "Verified"
           | `Falsified ->
               prerr_endline "Unexpectedly falsified";
               List.iter prerr_endline outputs_verify;
               exit 2
           | `Crashed ->
               prerr_endline "Verification crashed";
               List.iter prerr_endline outputs_verify;
               exit 2
           | `None -> assert false)
      | Falsified ->
          (match res_verify with
           | `Falsified -> prerr_endline "Falsified as expected"
           | `Verified ->
               prerr_endline "Unexpectedly verified";
               List.iter prerr_endline outputs_verify;
               exit 2
           | `Crashed ->
               prerr_endline "Verification crashed";
               List.iter prerr_endline outputs_verify;
               exit 2
           | `None -> assert false)
      | TyperFail rex ->
          if typerfail then
            if List.exists (Re.execp rex) outputs_syntax then
              prerr_endline "Typerfail as expected"
            else (
              prerr_endline "Typerfail unexpectedly";
              List.iter prerr_endline outputs_syntax;
              exit 2
            )
          else (
            prerr_endline "Typer succeeded unexpectedly";
            List.iter prerr_endline outputs_syntax;
            exit 2
          )
      | TyperSuccess ->
          if typersuccess then (
            prerr_endline "Typer succeeeded as expected"
          ) else (
            prerr_endline "Typer failed unexpectedly";
            List.iter prerr_endline outputs_syntax;
            exit 2
          )
    ) specs

let test_block lines =
  assert (lines <> []);
  let fn = Filename.temp_file "test" ".rab" in
  prerr_endline ("---------------------- " ^ fn);
  Out_channel.with_open_text fn (fun oc ->
      List.iter (fun line ->
          output_string oc line;
          output_char oc '\n') lines);
  let specs = Test.parse @@ List.hd lines in
  test specs fn

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
  List.iter test_file files *)
