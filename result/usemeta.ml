open Graph
open Metadata

let optimize_filename rule_info_list =
  let filename = ref "" in
  let is_single_file = ref false in
  let is_multiple_files = ref false in
  let compare_info fact_info =
    match fact_info.loc with
    | Some { filename = Some fn; begin_line = _ } ->
        if !filename <> fn
        then
          if !is_single_file
          then is_multiple_files := true
          else (
            filename := fn;
            is_single_file := true)
        else ()
    | _ -> ()
  in
  List.iter
    (fun rule_info ->
       List.iter compare_info rule_info.pre;
       List.iter compare_info rule_info.label;
       List.iter compare_info rule_info.post)
    rule_info_list;
  let delete_filename' fact_info : fact_info =
    match fact_info.loc with
    | Some { filename = _; begin_line } ->
        { fact_info with loc = Some { filename = None; begin_line } }
    | None -> fact_info
  in
  let delete_filename rule_info =
    let new_pre = List.map delete_filename' rule_info.pre in
    let new_label = List.map delete_filename' rule_info.label in
    let new_post = List.map delete_filename' rule_info.post in
    { rule_info with pre = new_pre; label = new_label; post = new_post }
  in
  if !is_multiple_files then rule_info_list else List.map delete_filename rule_info_list
;;

let load_file filename =
  let sexp = Sexplib.Sexp.load_sexp filename in
  let rules = t_of_sexp sexp in
  optimize_filename rules
;;

let trans_fact_type (ty_opt : Metadata.fact_type option) : Graph.fact_type =
  match ty_opt with
  | Some ty ->
      (match ty with
       | Channel -> Channel
       | Global -> Global
       | Eq -> Eq
       | Neq -> Neq
       | File -> File
       | Fresh -> Fresh
       | ConstFresh -> ConstFresh)
  | None -> Plain
;;

let modify infos gr =
  let rename_fresh_var var_name comp =
    match comp with
    | { data = Fact (name, [ Var str ], ty); loc } when name = "Fr" ->
        let var_serial =
          if List.mem_assoc var_name gr.var_serial_list
          then (
            let _, num =
              List.find
                (fun (name, num) ->
                   if name = var_name then num := !num + 1;
                   true)
                gr.var_serial_list
            in
            !num)
          else (
            gr.var_serial_list <- (var_name, ref 0) :: gr.var_serial_list;
            0)
        in
        let new_var_name = Printf.sprintf "%s[%i]" var_name var_serial in
        gr.subst_list <- (str, Var new_var_name) :: gr.subst_list;
        { data = Fact (name, [ Var new_var_name ], ty); loc }
    | _ -> comp
  in
  let modify_on_fact fact_info comp =
    let new_comp =
      match fact_info.fresh with
      | Some str -> rename_fresh_var str comp
      | None -> comp
    in
    let new_comp =
      match fact_info.loc with
      | Some loc ->
          (match comp with
           | { data = Fact (name, args, Plain); loc = _ } when name = fact_info.name ->
               { data = Fact (name, args, trans_fact_type fact_info.ty)
               ; loc = Some { filename = loc.filename; begin_line = loc.begin_line }
               }
           | _ -> comp)
      | None -> new_comp
    in
    new_comp
  in
  let rec modify_on_elem fact_info elem =
    match elem with
    | Field (port, comp) -> Field (port, modify_on_fact fact_info comp)
    | Nested l -> Nested (List.map (modify_on_elem fact_info) l)
  in
  let modify_on_attr (info : rule_info) attr =
    match attr with
    | ( id
      , Some
          (Id_record
             (Nested
                [ Nested
                    [ pre
                    ; Nested [ Field (port, { data = Transition (name, facts); loc }) ]
                    ; post
                    ]
                ])) )
      when name = info.name ->
        let new_pre =
          List.fold_left (fun elem info -> modify_on_elem info elem) pre info.pre
        in
        let new_label_facts =
          List.fold_left
            (fun facts info -> List.map (modify_on_fact info) facts)
            facts
            info.label
        in
        let new_label_facts =
          if info.attack
          then { data = Raw_text "ATTACK"; loc = None } :: new_label_facts
          else new_label_facts
        in
        let new_label =
          Nested [ Field (port, { data = Transition (name, new_label_facts); loc }) ]
        in
        let new_post =
          List.fold_left (fun elem info -> modify_on_elem info elem) post info.post
        in
        id, Some (Id_record (Nested [ Nested [ new_pre; new_label; new_post ] ]))
    | _ -> attr
  in
  let rec modify_on_stmt info stmt =
    match stmt with
    | Stmt_node (id, attr_l) -> Stmt_node (id, List.map (modify_on_attr info) attr_l)
    | Stmt_subgraph subgr ->
        Stmt_subgraph
          { subgr with stmt_list = List.map (modify_on_stmt info) subgr.stmt_list }
    | _ -> stmt
  in
  gr.stmt_list
  <- List.fold_left
       (fun stmt_l info -> List.map (modify_on_stmt info) stmt_l)
       gr.stmt_list
       infos;
  gr
;;

module StringSet = Set.Make (String)

let collect_var_with_param infos =
  let s = ref StringSet.empty in
  let collect_on_fact_infos fact_infos =
    List.iter
      (fun fact_info ->
         List.iter (fun var -> s := StringSet.add var !s) fact_info.paramvars)
      fact_infos
  in
  List.iter
    (fun rule_info ->
       collect_on_fact_infos rule_info.pre;
       collect_on_fact_infos rule_info.label;
       collect_on_fact_infos rule_info.post)
    infos;
  StringSet.elements !s
;;

let transform_var_with_param var_name comp =
  let rec transform_on_args args = List.map transform_on_arg args
  and transform_on_arg arg =
    match arg with
    | Tuple (Var str :: rest) when str = var_name ->
        if List.length rest > 1
        then Var_with_param (str, Tuple rest)
        else if List.length rest = 1
        then Var_with_param (str, List.hd rest)
        else arg
    | Func (name, args) -> Func (name, transform_on_args args)
    | _ -> arg
  in
  match comp with
  | { data = Fact (name, args, ty); loc } ->
      { data = Fact (name, transform_on_args args, ty); loc }
  | _ -> comp
;;

let use_metadata meta graph =
  let graph = modify meta graph in
  graph.paramvars <- collect_var_with_param meta;
  graph
;;
