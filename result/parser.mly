%{
  open Graph

  exception Compass_error of string

  let compass_pt_of_id id =
    let str =
      match id with
      | Id s | Id_quoted s | Id_html s -> s
      | Id_record _ -> ""
    in
    match str with
    | "n" -> N
    | "ne" -> NE
    | "e" -> E
    | "se" -> SE
    | "s" -> S
    | "sw" -> SW
    | "w" -> W
    | "nw" -> NW
    | "c" -> C
    | _ -> raise (Compass_error (str ^ " <- invalid for compass point"))

  let concat_texts s_list = String.concat " " s_list
%}

%token LBRA RBRA
%token EOF
%token COMMA
%token LSBRA RSBRA
%token COLON
%token SEMICOLON
%token EQ
%token PLUS
%token GRAPH DIGRAPH
%token STRICT
%token NODE EDGE SUBGRAPH
%token EDGEOP
%token <string> ID ID_DQUOTE ID_HTML
%token PIPE
%token LPAR RPAR
%token LT GT
%token <string> TEXT PORT_ID TIMESTAMP
%token TABLE_L TABLE_R
%token TR_L TR_R
%token TD_L TD_R
%token FONT_L FONT_R

%start <Graph.graph list> main
%start <Graph.record_element> record
%start <Graph.arg> parse_arg
%start <Graph.subst list> subst_label
%%
/* graph parser */
main:
| l=graph_list EOF { l }

graph_list:
| /* empty */ { [] }
| g=graph l=graph_list { g :: l }

graph:
| STRICT ty=graph_type i=id LBRA l=stmt_list RBRA {
    {
      strict = true;
      graph_type = ty;
      name = Some i;
      stmt_list = l;
      subst_list = [];
      var_serial_list = [];
      paramvars = [];
    }
  }
| STRICT ty=graph_type LBRA l=stmt_list RBRA {
    {
      strict = true;
      graph_type = ty;
      name = None;
      stmt_list = l;
      subst_list = [];
      var_serial_list = [];
      paramvars = [];
    }
  }
| ty=graph_type i=id LBRA l=stmt_list RBRA {
    {
      strict = false;
      graph_type = ty;
      name = Some i;
      stmt_list = l;
      subst_list = [];
      var_serial_list = [];
      paramvars = [];
    }
  }
| ty=graph_type LBRA l=stmt_list RBRA {
    {
      strict = false;
      graph_type = ty;
      name = None;
      stmt_list = l;
      subst_list = [];
      var_serial_list = [];
      paramvars = [];
    }
  }

graph_type:
| GRAPH { Graph }
| DIGRAPH { Digraph }

id:
| i=ID { Id i }
| i=id_dquote { Id_quoted i }
| i=ID_HTML { Id_html i }

id_dquote:
| i=ID_DQUOTE { i }
| i1=ID_DQUOTE PLUS i2=id_dquote { i1 ^ i2 }

stmt_list:
| s=stmt | s=stmt SEMICOLON { [s] }
| s=stmt l=stmt_list | s=stmt SEMICOLON l=stmt_list { s :: l }

stmt:
| i=node_id l=attr_list { Stmt_node (i, l) }
| p=edge_point pl=targets al=attr_list { Stmt_edge (p, pl, al) }
| a=attr_stmt { Stmt_attr a }
| i1=id EQ i2=id { Stmt_eq (i1, i2) }
| sg=subgraph { Stmt_subgraph sg }

node_id:
| i1=id COLON i2=id COLON i3=id {
    try
      let pt = compass_pt_of_id i3 in
      (i1, Some (i2, Some pt))
    with
    | exn -> raise exn
  }
| i1=id COLON i2=id { (i1, Some (i2, None)) }
| i=id { (i, None) }

edge_point:
| i=node_id { Point_node i }
| sg=subgraph { Point_subgraph sg }

targets:
| EDGEOP p=edge_point { [p] }
| EDGEOP p=edge_point l=targets { p :: l }

attr_stmt:
| GRAPH l=attr_list { Attr_graph l }
| NODE l=attr_list { Attr_node l }
| EDGE l=attr_list { Attr_edge l }

attr_list:
| /* empty */ { [] }
| LSBRA l1=a_list RSBRA l2=attr_list { l1 @ l2 }

a_list:
| /* empty */ { [] }
| i=id l=a_list | i=id COMMA l=a_list { (i, None) :: l }
| i1=id EQ i2=id l=a_list | i1=id EQ i2=id COMMA l=a_list { (i1, Some i2) :: l }

subgraph:
| LBRA l=stmt_list RBRA | SUBGRAPH LBRA l=stmt_list RBRA {
    {
      name = None;
      stmt_list = l;
    }
  }
| SUBGRAPH i=id LBRA l=stmt_list RBRA {
    {
      name = Some i;
      stmt_list = l;
    }
  }


/* record node parser */
record:
| c=record_content EOF { Nested c }

parse_arg:
| a=arg EOF { a }

record_content:
| l=separated_nonempty_list(PIPE, element) { l }

element:
| LBRA c=record_content RBRA { Nested c }
| f=field { f }

component:
| t=TEXT f=component_suffix { f t }
| TIMESTAMP COLON t=TEXT LSBRA l=component_list RSBRA { Transition(t, l) }

component_suffix:
| LPAR a=args RPAR { fun id -> Fact(id, a, Plain) }
| /* empty */ { fun id -> Raw_text id }

component_list:
| l=separated_list(COMMA, component) { List.map (fun comp -> {data=comp; loc=None}) l }

args:
| l=separated_list(COMMA, arg) { l }

arg:
| t=TEXT f=arg_suffix | LPAR t=TEXT RPAR f=arg_suffix { f t }
| LT a=args GT { Tuple a }

arg_suffix:
| LPAR a=args RPAR { fun id -> Func(id, a) }
| /* empty */ { fun id -> Var id }

field:
| p=PORT_ID c=component { Field(Some (Id p), {data=c; loc=None}) }
| p=PORT_ID { Field(Some (Id p), {data=Raw_text ""; loc=None}) }
| c=component { Field(None, {data=c; loc=None}) }
| /* empty */ { Field(None, {data=Raw_text ""; loc=None}) }


/* substitution parser */
subst_label:
| TABLE_L l=subst_list TABLE_R EOF { l }

subst_list:
| /* empty */ { [] }
| TR_L c=content TR_R l=subst_list { c :: l }

content:
| TD_L FONT_L t1=texts FONT_R TD_R TD_L EQ TD_R TD_L t2=texts TD_R { (concat_texts t1, Raw_text (concat_texts t2)) }

texts:
| t=TEXT { [t] }
| t=TEXT l=texts { t :: l }
%%