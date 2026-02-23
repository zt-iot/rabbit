type graph_type =
  | Graph
  | Digraph

type arg =
  | Var of string
  | Var_with_param of string * arg
  | Tuple of arg list
  | Func of string * arg list
  | Raw_text of string

type fact_type =
  | Channel
  | Global
  | Eq
  | Neq
  | File
  | Fresh
  | ConstFresh
  | Plain

type location =
  { filename : string option
  ; begin_line : int option
  }

type component =
  | Fact of string * arg list * fact_type
  | Transition of string * component' list
  | Raw_text of string

and component' =
  { data : component
  ; loc : location option
  }

type id =
  | Id of string
  | Id_quoted of string
  | Id_html of string
  | Id_record of record_element

and compass_pt =
  | N
  | NE
  | E
  | SE
  | S
  | SW
  | W
  | NW
  | C

and port = id * compass_pt option

and record_element =
  | Field of id option * component'
  | Nested of record_element list

type subst = string * arg
type attr = id * id option

type attr_stmt =
  | Attr_graph of attr list
  | Attr_node of attr list
  | Attr_edge of attr list

type point_of_stmt_edge =
  | Point_node of (id * port option)
  | Point_subgraph of subgraph

and stmt =
  | Stmt_node of (id * port option) * attr list
  | Stmt_edge of point_of_stmt_edge * point_of_stmt_edge list * attr list
  | Stmt_attr of attr_stmt
  | Stmt_eq of id * id
  | Stmt_subgraph of subgraph

and subgraph =
  { mutable name : id option
  ; mutable stmt_list : stmt list
  }

type graph =
  { mutable strict : bool
  ; mutable graph_type : graph_type
  ; mutable name : id option
  ; mutable stmt_list : stmt list
  ; mutable subst_list : subst list
  ; mutable var_serial_list : (string * int ref) list
  ; mutable paramvars : string list
  }

let string_of_graph_type graph_ty =
  match graph_ty with
  | Graph -> "graph"
  | Digraph -> "digraph"
;;

let rec string_of_arg arg =
  match arg with
  | Var s -> s
  | Var_with_param (s, param) -> Printf.sprintf "%s\\<%s\\>" s (string_of_arg param)
  | Tuple args -> Printf.sprintf "(%s)" (String.concat "," (List.map string_of_arg args))
  | Func (s, args) ->
      Printf.sprintf "%s(%s)" s (String.concat "," (List.map string_of_arg args))
  | Raw_text s -> s
;;

let string_of_location loc =
  (match loc.filename with
   | Some fn -> Printf.sprintf "file \\\"%s\\\", \\l" fn
   | None -> "")
  ^ (match loc.filename, loc.begin_line with
     | Some _, Some _ -> Printf.sprintf "&nbsp;&nbsp;"
     | _ -> "")
  ^
  match loc.begin_line with
  | Some n -> Printf.sprintf "line%i:\\l" n
  | None -> ""
;;

let rec string_of_component comp =
  match comp with
  | Fact (s, args, ty) ->
      (match ty with
       | Channel ->
           Printf.sprintf
             "%s::%s(%s)"
             (string_of_arg (List.hd args))
             s
             (String.concat "," (List.map string_of_arg (List.tl args)))
       | Global ->
           Printf.sprintf "::%s(%s)" s (String.concat "," (List.map string_of_arg args))
       | Eq ->
           Printf.sprintf
             "%s=%s"
             (string_of_arg (List.nth args 0))
             (string_of_arg (List.nth args 1))
       | Neq ->
           Printf.sprintf
             "%s!=%s"
             (string_of_arg (List.nth args 0))
             (string_of_arg (List.nth args 1))
       | File ->
           Printf.sprintf
             "%s.%s"
             (string_of_arg (List.nth args 1))
             (string_of_arg (List.nth args 2))
       | Fresh -> Printf.sprintf "new %s" (string_of_arg (List.hd args))
       | ConstFresh -> Printf.sprintf "const fresh %s" (string_of_arg (List.hd args))
       | Plain ->
           Printf.sprintf "%s(%s)" s (String.concat "," (List.map string_of_arg args)))
  | Transition (s, comps) ->
      Printf.sprintf "%s[%s]" s (String.concat "," (List.map string_of_component' comps))
  | Raw_text s -> s

and string_of_component' comp =
  (match comp.loc with
   | Some location -> string_of_location location
   | None -> "")
  ^ string_of_component comp.data
;;

let string_of_compass_pt pt =
  match pt with
  | N -> "n"
  | NE -> "ne"
  | E -> "e"
  | SE -> "se"
  | S -> "s"
  | SW -> "sw"
  | W -> "w"
  | NW -> "nw"
  | C -> "c"
;;

let rec string_of_id id =
  match id with
  | Id s -> s
  | Id_quoted s ->
      let out = ref "" in
      String.iter
        (fun c ->
           match c with
           | '"' -> out := !out ^ "\\\""
           | _ -> out := Printf.sprintf "%s%c" !out c)
        s;
      Printf.sprintf "\"%s\"" !out
  | Id_html s -> s
  | Id_record elem -> string_of_record_element elem

and string_of_record_element_inner elem =
  match elem with
  | Field (Some id, c) ->
      Printf.sprintf "<%s> %s" (string_of_id id) (string_of_component' c)
  | Field (None, c) -> string_of_component' c
  | Nested l ->
      Printf.sprintf
        "{%s}"
        (String.concat "|" (List.map string_of_record_element_inner l))

and string_of_record_element elem =
  Printf.sprintf
    "\"%s\""
    (match elem with
     | Nested l -> String.concat "|" (List.map string_of_record_element_inner l)
     | Field _ -> string_of_record_element_inner elem)
;;

let string_of_port port =
  match port with
  | id, None -> string_of_id id
  | id, Some compass_pt ->
      Printf.sprintf "%s:%s" (string_of_id id) (string_of_compass_pt compass_pt)
;;

let string_of_attr attr =
  match attr with
  | id, None -> string_of_id id
  | id, Some v -> Printf.sprintf "%s=%s" (string_of_id id) (string_of_id v)
;;

let string_of_attr_list attrs =
  if List.length attrs > 0
  then Printf.sprintf "[%s]" (String.concat ", " (List.map string_of_attr attrs))
  else ""
;;

let string_of_attr_stmt attr_stmt =
  let s, attrs =
    match attr_stmt with
    | Attr_graph l -> "graph", l
    | Attr_node l -> "node", l
    | Attr_edge l -> "edge", l
  in
  Printf.sprintf "%s %s" s (string_of_attr_list attrs)
;;

let rec string_of_point_of_stmt_edge gr_typ pt =
  match pt with
  | Point_node (id, None) -> string_of_id id
  | Point_node (id, Some port) ->
      Printf.sprintf "%s:%s" (string_of_id id) (string_of_port port)
  | Point_subgraph subgr -> string_of_subgraph gr_typ subgr

and string_of_stmt gr_typ stmt =
  match stmt with
  | Stmt_node ((id, port_opt), attrs) ->
      Printf.sprintf
        "%s%s %s"
        (string_of_id id)
        (match port_opt with
         | Some port -> Printf.sprintf ":%s" (string_of_port port)
         | None -> "")
        (string_of_attr_list attrs)
  | Stmt_edge (pt, pts, attrs) ->
      let arrow =
        match gr_typ with
        | Graph -> "--"
        | Digraph -> "->"
      in
      Printf.sprintf
        "%s %s %s%s"
        (string_of_point_of_stmt_edge gr_typ pt)
        arrow
        (String.concat
           (Printf.sprintf " %s " arrow)
           (List.map (string_of_point_of_stmt_edge gr_typ) pts))
        (string_of_attr_list attrs)
  | Stmt_attr attr -> string_of_attr_stmt attr
  | Stmt_eq (id, v) -> Printf.sprintf "%s=%s" (string_of_id id) (string_of_id v)
  | Stmt_subgraph subgr -> string_of_subgraph gr_typ subgr

and string_of_stmt_list gr_typ sepa stmts =
  String.concat
    sepa
    (List.map (fun stmt -> Printf.sprintf "%s;" (string_of_stmt gr_typ stmt)) stmts)

and string_of_subgraph gr_typ subgr =
  Printf.sprintf
    "subgraph %s{\n  %s\n}"
    (match subgr.name with
     | Some id -> Printf.sprintf "%s " (string_of_id id)
     | None -> "")
    (string_of_stmt_list gr_typ "\n  " subgr.stmt_list)
;;

let string_of_graph gr =
  Printf.sprintf
    "%s%s %s {\n%s\n}"
    (if gr.strict then "strict " else "")
    (string_of_graph_type gr.graph_type)
    (match gr.name with
     | Some id -> Printf.sprintf "%s " (string_of_id id)
     | None -> "")
    (string_of_stmt_list gr.graph_type "\n" gr.stmt_list)
;;

let print oc gr = output_string oc (string_of_graph gr)
