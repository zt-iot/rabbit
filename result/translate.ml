open Graph

(* config *)
let color_of_not_communication_edge = "gray50"

let def_edge_attrs =
  [ Id "color", Some (Id_quoted color_of_not_communication_edge)
  ; Id "style", Some (Id_quoted "bold")
  ; Id "weight", Some (Id_quoted "10.0")
  ]
;;

let def_global_node_attrs =
  [ Id "shape", Some (Id_quoted "record")
  ; Id "fillcolor", Some (Id_quoted "#b5db99")
  ; Id "style", Some (Id_quoted "filled")
  ; Id "fontcolor", Some (Id_quoted "black")
  ; Id "role", Some (Id_quoted "Undefined")
  ]
;;

let deletable_facts_prefix =
  [ "Init"; "ACP"; "Const"; "State"; "Transition"; "Structure" ]
;;

let loop_in_fact = "Loop_In"
let loop_back_fact = "Loop_Back"
let loop_out_fact = "Loop_Out"
let loop_marker_facts = [ loop_in_fact; loop_back_fact; loop_out_fact ]
let var_channel_prefix = "chan:"
let var_string_prefix = "str:"
let deletable_var_prefixs = [ var_channel_prefix; var_string_prefix ]
let deletable_subgr_prefixs = [ "PG" ]
let subgraph_name_pattern = Str.regexp "\\(.*\\)__.*_\\([0-9]*\\)$"

(* generate node/port names *)
let name_counter = ref 0

let fresh_name () =
  name_counter := !name_counter + 1;
  Printf.sprintf "m%i" !name_counter
;;

(* split middle layer into facts *)
let split_transition attr =
  let rec split_elem elem =
    match elem with
    | Nested [ Field (_, { data = Transition (name, facts) }) ] ->
        Nested (List.map (fun fact -> Field (None, fact)) facts)
    | Nested el -> Nested (List.map split_elem el)
    | Field (p, f) -> Field (p, f)
  in
  match attr with
  | id, Some (Id_record elem) ->
      let new_elem = split_elem elem in
      id, Some (Id_record new_elem)
  | other -> other
;;

(* whether "s" begins with "prefix" *)
let check_prefix prefix s =
  let len_p = String.length prefix in
  let len_s = String.length s in
  len_s >= len_p && String.sub s 0 len_p = prefix
;;

(* search component of the specific port *)
let search_port node_id stmt_l =
  match node_id with
  | node_id_target, Some (port_id_target, _) ->
      let rec find_node stmt_l =
        List.find_map
          (fun stmt ->
             match stmt with
             | Stmt_node ((node_id, _), attr_l) when node_id = node_id_target -> Some stmt
             | Stmt_subgraph subgr -> find_node subgr.stmt_list
             | _ -> None)
          stmt_l
      in
      let rec match_elem elem_l =
        List.find_map
          (fun elem ->
             match elem with
             | Field (Some port_id, comp) when port_id = port_id_target -> Some comp
             | Nested l -> match_elem l
             | _ -> None)
          elem_l
      in
      let rec find_port attr_l =
        List.find_map
          (fun attr ->
             match attr with
             | _, Some (Id_record elem) -> match_elem [ elem ]
             | _ -> None)
          attr_l
      in
      (match find_node stmt_l with
       | Some (Stmt_node (_, attr_l)) -> find_port attr_l
       | Some _ | None -> None)
  | _, None -> None
;;

(* change edge color *)
let change_edge_color stmt_l =
  let rec change_color stmt =
    match stmt with
    | Stmt_edge (Point_node from, [ Point_node into ], attr_l) ->
        let from_component = search_port from stmt_l in
        let into_component = search_port into stmt_l in
        (match from_component, into_component with
         | ( Some { data = Fact (from_fact, _, from_typ) }
           , Some { data = Fact (into_fact, _, into_typ) } ) ->
             if
               ((from_typ = File && into_typ = File)
                || (from_typ = Plain
                    && into_typ = Plain
                    && List.exists
                         (fun prefix ->
                            check_prefix prefix from_fact && check_prefix prefix into_fact)
                         deletable_facts_prefix))
               && (from_fact <> "Out" || into_fact <> "In")
             then (
               let color_changed =
                 (Id "color", Some (Id_quoted color_of_not_communication_edge))
                 :: List.remove_assoc (Id "color") attr_l
               in
               Stmt_edge (Point_node from, [ Point_node into ], color_changed))
             else stmt
         | Some { data = Fact (from_fact, _, _) }, _ when from_fact = "Out" ->
             let color_changed = List.remove_assoc (Id "color") attr_l in
             Stmt_edge (Point_node from, [ Point_node into ], color_changed)
         | _, Some { data = Fact (into_fact, _, _) } when into_fact = "In" ->
             let color_changed = List.remove_assoc (Id "color") attr_l in
             Stmt_edge (Point_node from, [ Point_node into ], color_changed)
         | _ -> stmt)
    | Stmt_subgraph subgr ->
        Stmt_subgraph { subgr with stmt_list = List.map change_color subgr.stmt_list }
    | _ -> stmt
  in
  List.map change_color stmt_l
;;

(* delete specific prefixes from Rabbit variables *)
let delete_prefixs_of_vars prefix attr =
  let delete_prefix str =
    if check_prefix prefix str
    then (
      let len_prefix = String.length prefix in
      let len_str = String.length str in
      let new_str = String.sub str len_prefix (len_str - len_prefix) in
      let new_str =
        if prefix = var_string_prefix then "\\\"" ^ new_str ^ "\\\"" else new_str
      in
      new_str)
    else str
  in
  let rec delete_on_args args = List.map delete_on_arg args
  and delete_on_arg arg =
    match arg with
    | Var var -> Var (delete_prefix var)
    | Tuple args -> Tuple (delete_on_args args)
    | Func (name, args) -> Func (delete_prefix name, delete_on_args args)
    | _ -> arg
  in
  let rec delete_on_elem elem =
    match elem with
    | Field (p, { data = Fact (name, args, ty); loc = lc }) ->
        Field (p, { data = Fact (name, delete_on_args args, ty); loc = lc })
    | Nested l -> Nested (List.map delete_on_elem l)
    | _ -> elem
  in
  match attr with
  | id, Some (Id_record elem) -> id, Some (Id_record (delete_on_elem elem))
  | _ -> attr
;;

(* delete facts begining with specific prefixes *)
let delete_fact_starts_with str attr =
  let rec delete_on_elem elem =
    match elem with
    | Field (p, { data = Fact (name, _, _) })
      when check_prefix str name || check_prefix ("!" ^ str) name -> None
    | Field (p, other) -> Some (Field (p, other))
    | Nested l -> Some (Nested (List.filter_map delete_on_elem l))
  in
  match attr with
  | id, Some (Id_record elem) ->
      let new_elem_opt = delete_on_elem elem in
      let new_elem =
        match new_elem_opt with
        | Some e -> e
        | None -> Nested []
      in
      id, Some (Id_record new_elem)
  | _ -> attr
;;

(* substitute Rabbit terms for abbreviations by Tamarin *)
let substitute subst_l attr =
  let rec substitute_arg_list arg_l = List.map substitute_arg arg_l
  and substitute_arg arg =
    match arg with
    | Var str ->
        (try
           let new_arg = List.assoc str subst_l in
           substitute_arg new_arg
         with
         | Not_found -> arg)
    | Tuple arg_l -> Tuple (substitute_arg_list arg_l)
    | Func (name, arg_l) -> Func (name, substitute_arg_list arg_l)
    | _ -> arg
  in
  let rec substitute_elem elem =
    match elem with
    | Field (port, { data = Fact (name, args, ty); loc = lc }) ->
        Field (port, { data = Fact (name, substitute_arg_list args, ty); loc = lc })
    | Field (port, other) -> Field (port, other)
    | Nested l -> Nested (List.map substitute_elem l)
  in
  match attr with
  | id, Some (Id_record elem) ->
      let new_elem = substitute_elem elem in
      id, Some (Id_record new_elem)
  | _ -> attr
;;

(* delete unnecessary file facts *)
let optimize_file_fact attr =
  let optimize_elem elem =
    match elem with
    | Nested [ Nested [ Nested pre; Nested label; Nested post ] ] ->
        let pre_file, pre_others =
          List.partition
            (fun el ->
               match el with
               | Field (_, { data = Fact (_, _, File); _ }) -> true
               | _ -> false)
            pre
        in
        let pre_file_facts =
          List.filter_map
            (fun el ->
               match el with
               | Field (_, { data = Fact _ as fact; _ }) -> Some fact
               | _ -> None)
            pre_file
        in
        let new_post =
          List.filter
            (fun el ->
               match el with
               | Field (_, { data = fact; _ }) when List.mem fact pre_file_facts -> false
               | _ -> true)
            post
        in
        Nested [ Nested [ Nested pre_others; Nested label; Nested new_post ] ]
    | _ -> elem
  in
  match attr with
  | id, Some (Id_record elem) ->
      let new_elem = optimize_elem elem in
      id, Some (Id_record new_elem)
  | _ -> attr
;;

(* transform the style of variables with parameters *)
(* using metadata *)
let transform_var_with_param paramvars attr =
  let rec transform_on_facts elems = List.map transform_on_fact elems
  and transform_on_fact elem =
    match elem with
    | Field (port, ({ data = Fact (name, _, _); _ } as comp)) ->
        let new_comp =
          List.fold_left
            (fun comp var_name -> Usemeta.transform_var_with_param var_name comp)
            comp
            paramvars
        in
        Field (port, new_comp)
    | _ -> elem
  in
  let transform_on_elem elem =
    match elem with
    | Nested [ Nested [ Nested pre; Nested label; Nested post ] ] ->
        let new_pre = transform_on_facts pre in
        let new_label = transform_on_facts label in
        let new_post = transform_on_facts post in
        Nested [ Nested [ Nested new_pre; Nested new_label; Nested new_post ] ]
    | _ -> elem
  in
  if List.length paramvars > 0
  then (
    match attr with
    | id, Some (Id_record elem) ->
        let new_elem = transform_on_elem elem in
        id, Some (Id_record new_elem)
    | _ -> attr)
  else attr
;;

(* move specific facts to other layers *)
let move_fr_and_file attr =
  let move_elem elem =
    match elem with
    | Nested [ Nested [ Nested pre; Nested label; Nested post ] ] ->
        (* Fr fact: pre -> label *)
        let pre_fr, pre_others =
          List.partition
            (fun el ->
               match el with
               | Field (_, { data = Fact (_, _, (Fresh | ConstFresh)); _ }) -> true
               | _ -> false)
            pre
        in
        (* Eq/Neq fact: label -> pre *)
        let eq_and_neq, label_others =
          List.partition
            (fun el ->
               match el with
               | Field (_, { data = Fact (_, _, (Eq | Neq)); _ }) -> true
               | _ -> false)
            label
        in
        (* File fact: post -> label *)
        let post_file, post_others =
          List.partition
            (fun el ->
               match el with
               | Field (_, { data = Fact (_, _, File); _ }) -> true
               | _ -> false)
            post
        in
        let new_pre = pre_others @ eq_and_neq in
        let new_label = pre_fr @ post_file @ label_others in
        let new_label =
          List.map
            (fun el ->
               match el with
               | Field (Some port, comp) -> Field (None, comp)
               | _ -> el)
            new_label
        in
        let new_post = post_others in
        Nested [ Nested [ Nested new_pre; Nested new_label; Nested new_post ] ]
    | _ -> elem
  in
  match attr with
  | id, Some (Id_record elem) ->
      let new_elem = move_elem elem in
      id, Some (Id_record new_elem)
  | _ -> attr
;;

let change_edge_attrs attr_l =
  let change_color attr_l =
    List.map
      (fun attr ->
         match attr with
         | Id "color", Some content
           when content != Id_quoted color_of_not_communication_edge ->
             Id "color", Some (Id_quoted color_of_not_communication_edge)
         | _ -> attr)
      attr_l
  in
  let unify_style_to_bold attr_l =
    List.map
      (fun attr ->
         match attr with
         | Id "style", Some content when content != Id_quoted "bold" ->
             Id "style", Some (Id_quoted "bold")
         | _ -> attr)
      attr_l
  in
  let new_attr_l = ref attr_l in
  new_attr_l := change_color !new_attr_l;
  new_attr_l := unify_style_to_bold !new_attr_l;
  !new_attr_l
;;

(* replace names of subgraphs *)
let replace_subgraph_name stmt_l =
  let replace stmt =
    match stmt with
    | Stmt_eq (id1, id2) ->
        let new_id1, new_id2 =
          if id1 = Id "label"
          then (
            match id2 with
            | Id_quoted name ->
                if Str.string_match subgraph_name_pattern name 0
                then (
                  let proc_name = Str.matched_group 1 name in
                  let proc_idx = Str.matched_group 2 name in
                  let proc_idx = string_of_int (int_of_string proc_idx - 1) in
                  id1, Id_quoted (proc_name ^ "\\[" ^ proc_idx ^ "\\]"))
                else id1, id2
            | _ -> id1, id2)
          else id1, id2
        in
        Stmt_eq (new_id1, new_id2)
    | _ -> stmt
  in
  List.map replace stmt_l
;;

(* remove specific nodes from edge statements *)
let remove_nodes_from_edges stmt_l nodes =
  let remove_node stmt_l node_id =
    let edges_from_node = ref [] in
    let edges_into_node = ref [] in
    let rec check_edges_on_stmts stmt_l = List.filter_map check_edges_on_stmt stmt_l
    and check_edges_on_stmt stmt =
      match stmt with
      | Stmt_edge (Point_node (from, _), [ Point_node (into, _) ], _) as edge
        when from = node_id ->
          if not (List.mem into nodes)
          then edges_from_node := edge :: !edges_from_node
          else ();
          None
      | Stmt_edge (Point_node (from, _), [ Point_node (into, _) ], _) as edge
        when into = node_id ->
          if not (List.mem from nodes)
          then edges_into_node := edge :: !edges_into_node
          else ();
          None
      | Stmt_subgraph subgr ->
          Some
            (Stmt_subgraph { subgr with stmt_list = check_edges_on_stmts subgr.stmt_list })
      | _ -> Some stmt
    in
    let new_stmt_l = check_edges_on_stmts stmt_l in
    let new_edges =
      if List.length !edges_from_node > 0 && List.length !edges_into_node > 0
      then (
        let merge_edge edge1 edge2 =
          let from, attr_l =
            match edge1 with
            | Stmt_edge (Point_node id, _, l) -> id, l
            | _ -> assert false
          in
          let into =
            match edge2 with
            | Stmt_edge (_, [ Point_node id ], _) -> id
            | _ -> assert false
          in
          Stmt_edge (Point_node from, [ Point_node into ], attr_l)
        in
        List.concat_map
          (fun out_edge ->
             List.map (fun in_edge -> merge_edge in_edge out_edge) !edges_into_node)
          !edges_from_node)
      else []
    in
    new_stmt_l @ new_edges
  in
  List.fold_left remove_node stmt_l nodes
;;

(* separate loop markers from nodes containing other elements *)
let split_loop_marker stmt_l =
  let is_loop_elem elem =
    let marker_name = ref "" in
    match elem with
    | Nested [ Nested [ Nested pre; Nested label; Nested post ] ] ->
        let loop_marker, other_label =
          List.partition
            (fun elem ->
               match elem with
               | Field (_, { data = Fact (fact, _, Plain); _ })
                 when List.mem fact loop_marker_facts ->
                   marker_name := fact;
                   true
               | _ -> false)
            label
        in
        if
          List.length loop_marker > 0
          && (List.length pre != 0
              || List.length post != 0
              || List.length other_label != 0)
        then
          ( true
          , Nested [ Nested [ Nested pre; Nested other_label; Nested post ] ]
          , Some (Nested [ Nested [ Nested []; Nested loop_marker; Nested [] ] ])
          , !marker_name )
        else false, elem, None, !marker_name
    | _ -> false, elem, None, !marker_name
  in
  let is_loop_attr attr_l =
    let replacement_attrs = ref attr_l in
    let loop_marker_attrs = ref None in
    let marker_name = ref "" in
    let result =
      List.exists
        (fun attr ->
           match attr with
           | attr_id, Some (Id_record elem) ->
               let res, repl, loop, name = is_loop_elem elem in
               if res
               then (
                 replacement_attrs
                 := List.map
                      (fun attr ->
                         match attr with
                         | id, Some (Id_record _) when id = attr_id ->
                             attr_id, Some (Id_record repl)
                         | _ -> attr)
                      attr_l;
                 let loop_elem =
                   match loop with
                   | Some elem -> elem
                   | _ -> assert false
                 in
                 loop_marker_attrs
                 := Some
                      (List.map
                         (fun attr ->
                            match attr with
                            | id, Some (Id_record _) when id = attr_id ->
                                attr_id, Some (Id_record loop_elem)
                            | _ -> attr)
                         attr_l);
                 marker_name := name)
               else ();
               res
           | _ -> false)
        attr_l
    in
    result, !replacement_attrs, !loop_marker_attrs, !marker_name
  in
  let new_nodes = ref [] in
  let rec split_stmts stmt_l = List.concat_map split_stmt stmt_l
  and split_stmt stmt =
    match stmt with
    | Stmt_node (id, attr_l) ->
        let result, repl, loop_marker, name = is_loop_attr attr_l in
        if result
        then (
          let new_node_id = Id (fresh_name ()), None in
          let new_attrs =
            match loop_marker with
            | Some attrs -> attrs
            | None -> assert false
          in
          new_nodes := (Point_node id, Point_node new_node_id, name) :: !new_nodes;
          [ Stmt_node (id, repl); Stmt_node (new_node_id, new_attrs) ])
        else [ stmt ]
    | Stmt_subgraph subgr ->
        [ Stmt_subgraph { subgr with stmt_list = split_stmts subgr.stmt_list } ]
    | _ -> [ stmt ]
  in
  let new_edges stmt_l origin_id new_id marker =
    let is_new_to_origin = marker = loop_in_fact in
    let new_edge =
      if is_new_to_origin
      then Stmt_edge (new_id, [ origin_id ], def_edge_attrs)
      else Stmt_edge (origin_id, [ new_id ], def_edge_attrs)
    in
    let rec exec_on_edges stmt_l = List.map exec_on_edge stmt_l
    and exec_on_edge stmt =
      match stmt with
      | Stmt_edge (from, [ into ], attrs) when is_new_to_origin && into = origin_id ->
          Stmt_edge (from, [ new_id ], attrs)
      | Stmt_edge (from, [ into ], attrs) when (not is_new_to_origin) && from = origin_id
        -> Stmt_edge (new_id, [ into ], attrs)
      | Stmt_subgraph subgr ->
          Stmt_subgraph { subgr with stmt_list = exec_on_edges subgr.stmt_list }
      | _ -> stmt
    in
    exec_on_edges stmt_l @ [ new_edge ]
  in
  let new_stmt_l = split_stmts stmt_l in
  List.fold_left
    (fun stmts (origin_id, new_id, marker) -> new_edges stmts origin_id new_id marker)
    new_stmt_l
    !new_nodes
;;

(* change shapes of loop markers *)
let reshape_loop_marker stmt_l =
  let is_loop_elem elem =
    match elem with
    | Nested
        [ Nested
            [ Nested []
            ; Nested [ Field (_, { data = Fact (fact, _, Plain); _ }) ]
            ; Nested []
            ]
        ]
      when List.mem fact loop_marker_facts -> true, fact
    | _ -> false, ""
  in
  let is_loop_attr attr_l =
    let loop_marker = ref "" in
    let result =
      List.exists
        (fun attr ->
           match attr with
           | _, Some (Id_record elem) ->
               let res, name = is_loop_elem elem in
               if res then loop_marker := name else ();
               res
           | _ -> false)
        attr_l
    in
    result, !loop_marker
  in
  let reshape_attr loop_marker attr =
    let marker_shape =
      if loop_marker = loop_in_fact
      then "trapezium"
      else if loop_marker = loop_back_fact
      then "rect"
      else if loop_marker = loop_out_fact
      then "invtrapezium"
      else "box"
    in
    match attr with
    | Id "shape", Some (Id_quoted _) -> Id "shape", Some (Id_quoted marker_shape)
    | Id "label", Some (Id_record _) -> Id "label", Some (Id_quoted loop_marker)
    | _ -> attr
  in
  let rec reshape_stmts stmt_l = List.map reshape_stmt stmt_l
  and reshape_stmt stmt =
    match stmt with
    | Stmt_node (id, attr_l) ->
        let result, loop_marker = is_loop_attr attr_l in
        if result
        then (
          let new_attr_l = List.map (reshape_attr loop_marker) attr_l in
          Stmt_node (id, new_attr_l))
        else stmt
    | Stmt_subgraph subgr ->
        Stmt_subgraph { subgr with stmt_list = reshape_stmts subgr.stmt_list }
    | _ -> stmt
  in
  reshape_stmts stmt_l
;;

(* change the style of attacker's nodes generated by Tamarin *)
let reshape_attack_marker stmt_l =
  let is_attack_attr attr_l =
    List.exists
      (fun attr ->
         match attr with
         | Id "shape", Some (Id_quoted "ellipse") -> true
         | _ -> false)
      attr_l
  in
  let from_attack_node (node_id, _) =
    let rec search_id stmt =
      match stmt with
      | Stmt_edge (Point_node (from, _), [ Point_node (into, _) ], _) when from = node_id
        -> [ into ]
      | Stmt_subgraph subgr -> List.concat_map search_id subgr.stmt_list
      | _ -> []
    in
    let target_ids = List.concat_map search_id stmt_l in
    let rec search_stmt node_id stmt =
      match stmt with
      | Stmt_node ((id, _), _) when id = node_id -> Some stmt
      | Stmt_subgraph subgr -> List.find_map (search_stmt node_id) subgr.stmt_list
      | _ -> None
    in
    List.concat_map (fun id -> List.filter_map (search_stmt id) stmt_l) target_ids
  in
  let rec reshape_stmt stmt =
    match stmt with
    | Stmt_node (id, attr_l) ->
        if is_attack_attr attr_l
        then (
          let targets = from_attack_node id in
          let new_label =
            if
              List.for_all
                (fun stmt ->
                   match stmt with
                   | Stmt_node (_, attr_l) -> is_attack_attr attr_l
                   | _ -> assert false)
                targets
            then
              ( Id "label"
              , Some (Id_record (Nested [ Nested [ Nested []; Nested []; Nested [] ] ])) )
            else
              ( Id "label"
              , Some
                  (Id_record
                     (Nested
                        [ Nested
                            [ Nested []
                            ; Nested
                                [ Field (None, { data = Raw_text "ATTACK"; loc = None }) ]
                            ; Nested []
                            ]
                        ])) )
          in
          Stmt_node (id, new_label :: def_global_node_attrs))
        else stmt
    | Stmt_subgraph subgr ->
        Stmt_subgraph { subgr with stmt_list = List.map reshape_stmt subgr.stmt_list }
    | _ -> stmt
  in
  List.map reshape_stmt stmt_l
;;

(* delete nodes with no elements *)
let delete_blank_node stmt_l =
  let rec is_blank_elem elem =
    match elem with
    | Field _ -> false
    | Nested l -> List.for_all is_blank_elem l
  in
  let is_blank_attr attr_l =
    List.exists
      (fun attr ->
         match attr with
         | _, Some (Id_record elem) -> is_blank_elem elem
         | _ -> false)
      attr_l
  in
  let deleted_nodes = ref [] in
  let rec delete stmt_l = List.filter_map keep_stmt stmt_l
  and keep_stmt stmt =
    match stmt with
    | Stmt_node ((node_id, _), attr_l) ->
        if is_blank_attr attr_l
        then (
          deleted_nodes := node_id :: !deleted_nodes;
          None)
        else Some stmt
    | Stmt_subgraph subgr ->
        let new_stmt_l = delete subgr.stmt_list in
        Some (Stmt_subgraph { subgr with stmt_list = new_stmt_l })
    | _ -> Some stmt
  in
  let new_stmt_l = delete stmt_l in
  remove_nodes_from_edges new_stmt_l !deleted_nodes
;;

(* delete subgraphs with no nodes *)
let delete_empty_subgraph stmt_l =
  let rec has_node stmt =
    match stmt with
    | Stmt_node _ -> false
    | Stmt_subgraph subgr -> List.for_all has_node subgr.stmt_list
    | _ -> true
  in
  let filter stmt =
    match stmt with
    | Stmt_subgraph _ -> not (has_node stmt)
    | _ -> true
  in
  List.filter filter stmt_l
;;

(* delete subgraphs begining with specific prefixes *)
let delete_subgr_starts_with str stmt_l =
  let check (subgr : subgraph) =
    List.exists
      (fun stmt ->
         match stmt with
         | Stmt_eq (Id "label", Id_quoted name) when check_prefix str name -> true
         | _ -> false)
      subgr.stmt_list
  in
  let filter stmt =
    match stmt with
    | Stmt_node _ | Stmt_edge _ -> true
    | _ -> false
  in
  List.concat_map
    (fun stmt ->
       match stmt with
       | Stmt_subgraph subgr ->
           if check subgr then List.filter filter subgr.stmt_list else [ stmt ]
       | _ -> [ stmt ])
    stmt_l
;;

(* delete specification of ports that no longer exists from edge statements *)
let delete_nonexist_port stmt_l =
  let exist_ports = ref [] in
  let rec filter_list stmt_l = List.iter filter_stmt stmt_l
  and filter_stmt stmt =
    match stmt with
    | Stmt_node ((_, port), attr_l) ->
        (match port with
         | Some port_id -> exist_ports := port_id :: !exist_ports
         | None -> ());
        (try
           let label = List.assoc (Id "label") attr_l in
           match label with
           | Some (Id_record elem) -> filter_elem elem
           | _ -> ()
         with
         | Not_found -> ())
    | Stmt_subgraph subgr -> filter_list subgr.stmt_list
    | _ -> ()
  and filter_elem elem =
    match elem with
    | Field (Some port_id, _) -> exist_ports := (port_id, None) :: !exist_ports
    | Nested elem_l -> List.iter filter_elem elem_l
    | _ -> ()
  in
  filter_list stmt_l;
  let rec delete stmt =
    match stmt with
    | Stmt_edge (Point_node (id1, Some port1), [ Point_node (id2, Some port2) ], attr_l)
      ->
        if List.mem port1 !exist_ports
        then
          if List.mem port2 !exist_ports
          then stmt
          else Stmt_edge (Point_node (id1, Some port1), [ Point_node (id2, None) ], attr_l)
        else if List.mem port2 !exist_ports
        then Stmt_edge (Point_node (id1, None), [ Point_node (id2, Some port2) ], attr_l)
        else Stmt_edge (Point_node (id1, None), [ Point_node (id2, None) ], attr_l)
    | Stmt_edge (Point_node (id1, Some port1), [ Point_node (id2, None) ], attr_l) ->
        if List.mem port1 !exist_ports
        then stmt
        else Stmt_edge (Point_node (id1, None), [ Point_node (id2, None) ], attr_l)
    | Stmt_edge (Point_node (id1, None), [ Point_node (id2, Some port2) ], attr_l) ->
        if List.mem port2 !exist_ports
        then stmt
        else Stmt_edge (Point_node (id1, None), [ Point_node (id2, None) ], attr_l)
    | Stmt_subgraph subgr ->
        Stmt_subgraph { subgr with stmt_list = List.map delete subgr.stmt_list }
    | _ -> stmt
  in
  List.map delete stmt_l
;;

(* when multiple edges have the same starting and ending points, one will remain and others will be deleted *)
let delete_duplicated_edges stmt_l =
  let delete_edges_with stmt_l edge =
    let from, into =
      match edge with
      | Stmt_edge (Point_node from, [ Point_node into ], _) -> from, into
      | _ -> assert false
    in
    let new_stmt_l =
      List.filter
        (fun stmt ->
           match stmt with
           | Stmt_edge (Point_node id1, [ Point_node id2 ], _)
             when id1 = from && id2 = into -> false
           | _ -> true)
        stmt_l
    in
    new_stmt_l @ [ edge ]
  in
  let edges =
    List.filter
      (fun stmt ->
         match stmt with
         | Stmt_edge _ -> true
         | _ -> false)
      stmt_l
  in
  List.fold_left delete_edges_with stmt_l edges
;;

(* change the number of layers in each node from 3 to 2 *)
let convert_to_two_stages stmt_l =
  let new_nodes = ref [] in
  let rec convert_on_stmt stmt =
    match stmt with
    | Stmt_node (id, attrs) ->
        let label = List.assoc (Id "label") attrs in
        let other_attrs = List.remove_assoc (Id "label") attrs in
        (match label with
         | Some (Id_record (Nested [ Nested [ Nested pre; Nested label; Nested post ] ]))
           ->
             if List.length label > 0 && List.length post > 0
             then (
               let label_attr =
                 ( Id "label"
                 , Some (Id_record (Nested [ Nested [ Nested pre; Nested label ] ])) )
               in
               let post_attr =
                 ( Id "label"
                 , Some (Id_record (Nested [ Nested [ Nested []; Nested post ] ])) )
               in
               let new_node_id = Id (fresh_name ()), None in
               new_nodes := (id, new_node_id) :: !new_nodes;
               [ Stmt_node (id, label_attr :: other_attrs)
               ; Stmt_node (new_node_id, post_attr :: other_attrs)
               ])
             else (
               let new_attr =
                 ( Id "label"
                 , Some
                     (Id_record (Nested [ Nested [ Nested pre; Nested (label @ post) ] ]))
                 )
               in
               [ Stmt_node (id, new_attr :: other_attrs) ])
         | _ -> [ stmt ])
    | Stmt_subgraph subgr ->
        [ Stmt_subgraph
            { subgr with stmt_list = List.concat_map convert_on_stmt subgr.stmt_list }
        ]
    | _ -> [ stmt ]
  in
  let new_edges stmt_l (origin_id, _) (new_id, _) =
    let new_edge =
      Stmt_edge
        (Point_node (origin_id, None), [ Point_node (new_id, None) ], def_edge_attrs)
    in
    let rec exec_on_edges stmt_l = List.map exec_on_edge stmt_l
    and exec_on_edge stmt =
      match stmt with
      | Stmt_edge (Point_node (from, port), [ into ], attrs) when from = origin_id ->
          Stmt_edge (Point_node (new_id, port), [ into ], attrs)
      | Stmt_subgraph subgr ->
          Stmt_subgraph { subgr with stmt_list = exec_on_edges subgr.stmt_list }
      | _ -> stmt
    in
    exec_on_edges stmt_l @ [ new_edge ]
  in
  let new_stmt_l = List.concat_map convert_on_stmt stmt_l in
  List.fold_left
    (fun stmts (origin_id, new_id) -> new_edges stmts origin_id new_id)
    new_stmt_l
    !new_nodes
;;

(* for operation check *)
(* unused *)
let delete_all_edges gr =
  let rec body stmt_l =
    match stmt_l with
    | [] -> []
    | Stmt_edge _ :: rest -> body rest
    | Stmt_subgraph sgr :: rest ->
        Stmt_subgraph { sgr with stmt_list = body sgr.stmt_list } :: body rest
    | stmt :: rest -> stmt :: body rest
  in
  gr.stmt_list <- body gr.stmt_list;
  gr
;;

(* execute conversion *)
let translate gr metadata =
  let pre_trans stmts =
    let new_stmts = ref stmts in
    new_stmts := change_edge_color stmts;
    !new_stmts
  in
  let rec main_trans stmts =
    List.map
      (fun stmt ->
         match stmt with
         | Stmt_node (id, attr_l) ->
             let new_attr_l = ref attr_l in
             new_attr_l := List.map split_transition !new_attr_l;
             new_attr_l
             := List.fold_left
                  (fun attr_l prefix -> List.map (delete_fact_starts_with prefix) attr_l)
                  !new_attr_l
                  deletable_facts_prefix;
             new_attr_l := List.map (substitute gr.subst_list) !new_attr_l;
             new_attr_l
             := List.fold_left
                  (fun attr_l prefix -> List.map (delete_prefixs_of_vars prefix) attr_l)
                  !new_attr_l
                  deletable_var_prefixs;
             new_attr_l := List.map optimize_file_fact !new_attr_l;
             new_attr_l := List.map (transform_var_with_param gr.paramvars) !new_attr_l;
             new_attr_l := List.map move_fr_and_file !new_attr_l;
             Stmt_node (id, !new_attr_l)
         | Stmt_edge (node_id, node_id_list, attr_l) ->
             let new_attr_l = ref attr_l in
             new_attr_l := change_edge_attrs !new_attr_l;
             Stmt_edge (node_id, node_id_list, !new_attr_l)
         | Stmt_subgraph subgr ->
             let new_stmt_l = replace_subgraph_name subgr.stmt_list in
             Stmt_subgraph { subgr with stmt_list = main_trans new_stmt_l }
         | _ -> stmt)
      stmts
  in
  let post_trans stmts =
    let new_stmts = ref stmts in
    new_stmts := reshape_attack_marker !new_stmts;
    new_stmts := delete_blank_node !new_stmts;
    new_stmts := delete_empty_subgraph !new_stmts;
    new_stmts
    := List.fold_left
         (fun stmt_l prefix -> delete_subgr_starts_with prefix stmt_l)
         !new_stmts
         deletable_subgr_prefixs;
    new_stmts := delete_nonexist_port !new_stmts;
    new_stmts := split_loop_marker !new_stmts;
    new_stmts := reshape_loop_marker !new_stmts;
    new_stmts := delete_duplicated_edges !new_stmts;
    new_stmts := convert_to_two_stages !new_stmts;
    !new_stmts
  in
  gr.stmt_list <- pre_trans gr.stmt_list;
  gr.stmt_list <- main_trans gr.stmt_list;
  gr.stmt_list <- post_trans gr.stmt_list;
  gr
;;

(* output *)
let print_graph fn output =
  let oc = open_out fn in
  print oc output;
  close_out oc
;;
