open Graph

exception Graph_Parse_error of int * int
exception Record_parse_error of string

let unquote str =
  let len = String.length str in
  if len >= 2 && str.[0] == '"' && str.[len - 1] = '"'
  then String.sub str 1 (len - 2)
  else str
;;

let parse_record_label attr_list =
  if List.mem (Id "shape", Some (Id_quoted "record")) attr_list
  then
    List.map
      (fun (id, id_opt) ->
         if id = Id "label"
         then (
           let element =
             match id_opt with
             | Some v ->
                 let label_str = unquote (string_of_id v) in
                 Lexer.read_string Lexer.token_rc Parser.record label_str
             | None -> Lexer.read_string Lexer.token_rc Parser.record ""
           in
           id, Some (Id_record element))
         else id, id_opt)
      attr_list
  else attr_list
;;

let parse_substitutions attr_list =
  let subst_l =
    if List.mem (Id "shape", Some (Id_quoted "plain")) attr_list
    then
      List.filter_map
        (fun (id, id_opt) ->
           if id = Id "label"
           then (
             match id_opt with
             | Some v ->
                 let label_str = string_of_id v in
                 let len = String.length label_str in
                 if len >= 2 && label_str.[0] == '<' && label_str.[len - 1] == '>'
                 then (
                   let content = String.sub label_str 1 (len - 2) in
                   let raw_substs =
                     Lexer.read_string Lexer.token_st Parser.subst_label content
                   in
                   let substs =
                     List.map
                       (fun (tar, raw_repl) ->
                          let arg =
                            match (raw_repl : arg) with
                            | Raw_text str ->
                                Lexer.read_string Lexer.token_rc Parser.parse_arg str
                            | _ -> raw_repl
                          in
                          tar, arg)
                       raw_substs
                   in
                   Some substs)
                 else None
             | None -> None)
           else None)
        attr_list
    else []
  in
  match subst_l with
  | [ l ] -> Some l
  | _ -> None
;;

let preprocess gr =
  let deleted_nodes = ref [] in
  let rec process_stmts stmt_list = List.filter_map process_stmt stmt_list
  and process_stmt stmt =
    match stmt with
    | Stmt_node (((node_id, _) as id), attr_list) ->
        let subst_l = parse_substitutions attr_list in
        (match subst_l with
         | Some l ->
             gr.subst_list <- l;
             deleted_nodes := node_id :: !deleted_nodes;
             None
         | None -> Some (Stmt_node (id, parse_record_label attr_list)))
    | Stmt_subgraph subgr ->
        Some (Stmt_subgraph { subgr with stmt_list = process_stmts subgr.stmt_list })
    | stmt -> Some stmt
  in
  gr.stmt_list <- process_stmts gr.stmt_list;
  gr.stmt_list <- Translate.remove_nodes_from_edges gr.stmt_list !deleted_nodes;
  gr
;;

let load fn =
  let raw_graph = Lexer.read_file Lexer.token_gr Parser.main fn in
  let out = List.map preprocess raw_graph in
  out
;;
