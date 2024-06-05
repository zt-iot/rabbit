type to_xml_error =
  | UnintendedError 

exception Error of to_xml_error Location.located

(** [error ~loc err] raises the given runtime error. *)
let error ~loc err = Stdlib.raise (Error (Location.locate ~loc err))

(** Print error description. *)
let print_error err ppf =
  match err with
  | UnintendedError -> Format.fprintf ppf "unintended behavior. Contact the developer"

let to_xml_instruction i = 
    let (s, _, _) = List.find (fun (_, s, _) -> s = i) Primitives.primitive_ins in
    Xml.Element ("Instruction", [], [Xml.PCData s])

let to_xml_ext_func f = 
  Xml.Element ("ExtFunction", [], [Xml.PCData f])

let to_xml_proc_func f = 
  Xml.Element ("ProcFunction", [], [Xml.PCData f])

let to_xml_indexed_var (s, i, j) =
  Xml.Element ("IndexedVariable", [("frame",string_of_int i) ; ("stack",string_of_int j)], [Xml.PCData s])


let tag_expr = "Expression"
let tag_stmt = "Statement"
let tag_atomic_stmt = "AtomicStatement"
let tag_stmts = "Statements"
let tag_event = "Event"
let tag_process = "Process"

let rec to_xml_expr {Location.data=c; Location.loc=loc} = 
    match c with
    | Syntax.Const s -> Xml.Element (tag_expr, [("constr", "constant")], [Xml.PCData s])
    | Syntax.ExtConst s -> Xml.Element (tag_expr, [("constr", "external constant")], [Xml.PCData s])
    | Syntax.Variable v-> Xml.Element (tag_expr, [("constr", "variable")], [to_xml_indexed_var v])
    | Syntax.Boolean b -> Xml.Element (tag_expr, [("constr", "boolean")], [Xml.PCData (string_of_bool b)])
    | Syntax.String s -> Xml.Element (tag_expr, [("constr", "string")], [Xml.PCData s])
    | Syntax.Integer k -> Xml.Element (tag_expr, [("constr", "integer")], [Xml.PCData (string_of_int k)])
    | Syntax.Float s -> Xml.Element (tag_expr, [("constr", "float")], [Xml.PCData s])
    | Syntax.Apply (o, el) -> 
      Xml.Element (tag_expr, [("constr", "apply")], 
        (to_xml_ext_func o) :: (List.map to_xml_expr el))
    | Syntax.Tuple el -> 
      Xml.Element (tag_expr, [("constr", "tuple")], 
        List.map to_xml_expr el)
    | Syntax.Channel (s,_,_) -> Xml.Element (tag_expr, [("constr", "channel")], [Xml.PCData s])
    | Syntax.FrVariable s -> error ~loc UnintendedError  

let to_xml_event {Location.data=c; Location.loc=loc} = 
  match c with  
  | Syntax.Event (eid, ivl) -> 
    Xml.Element (tag_event, [("name",eid)], List.map to_xml_expr ivl)

let rec to_xml_stmt {Location.data=c; Location.loc=loc}  = 
  match c with
  | Syntax.OpStmt a -> Xml.Element (tag_stmt, [], [to_xml_atomic_stmt a])
  | Syntax.EventStmt (a, el) -> Xml.Element (tag_stmt, [], (to_xml_atomic_stmt a) :: (List.map to_xml_event el))
  
and to_xml_atomic_stmt {Location.data=c; Location.loc=loc}  = 
    match c with
    | Syntax.Skip -> Xml.Element (tag_atomic_stmt, [("constr", "skip")], [Xml.PCData ""])
    | Syntax.Let (v, e) -> Xml.Element (tag_atomic_stmt, [("constr", "let")], (to_xml_indexed_var v) :: [to_xml_expr e])
    | Syntax.Call (v, f, args) -> 
      Xml.Element (tag_atomic_stmt, [("constr", "call")], (to_xml_indexed_var v) :: (to_xml_proc_func f) :: (List.map to_xml_expr args))
    | Syntax.Instruction (v, ins, args) -> 
      Xml.Element (tag_atomic_stmt, [("constr", "instruction")], (to_xml_indexed_var v) :: (to_xml_instruction ins) :: (List.map to_xml_expr args))
    | Syntax.If (e, c1, c2) -> 
      Xml.Element (tag_atomic_stmt, [("constr", "if")], 
        (to_xml_expr e) :: (to_xml_stmts c1) :: [(to_xml_stmts c2)])
    | Syntax.For (v, i, j, c) -> 
      Xml.Element (tag_atomic_stmt, [("constr", "for")], 
        [
          to_xml_indexed_var v ; 
          Xml.Element("From", [], [Xml.PCData (string_of_int i)]) ; 
          Xml.Element("To", [], [Xml.PCData (string_of_int j)]) ; 
          to_xml_stmts c
        ])

and to_xml_stmts cs = Xml.Element (tag_stmts, [], List.map to_xml_stmt cs)

let access_class_list = [Input.CRead ;  Input.CWrite ; Input.CSend ; Input.CRecv] 
let attack_class_list = [Input.CEaves ;  Input.CTamper ; Input.CDrop] 


let attks_to_attr attks = 
  List.map (fun a -> (Printer.print_attack_class a, "true")) attks

let accs_to_attr accs = 
  List.map (fun a -> (Printer.print_access_class a, "true")) accs

let to_xml_proc {
  Context.proc_pid=k;
  Context.proc_name=s;
  Context.proc_attack=attks;
  Context.proc_channel=chs;
  Context.proc_file=fls;
  Context.proc_variable=vars;
  Context.proc_function=fns;
  Context.proc_main=m
} = 
  let vars = List.rev vars in 
  let fns = List.rev fns in 
  let xml_ch (n, cl, acc, attk) =
    Xml.Element("Channel", [("name", n) ; ("class", Printer.print_chan_class cl)] @ (accs_to_attr acc) @ (attks_to_attr attk), []) in
  let xml_file (p, data, accs, attks) = 
    Xml.Element("File", ((accs_to_attr accs) @ (attks_to_attr attks)), 
      [Xml.Element("Path", [], [Xml.PCData p]) ;
      Xml.Element("Data", [], [to_xml_expr data])]) in 
  let xml_variable (id, expr) = 
    Xml.Element("Variable", [], 
      [Xml.Element("Ident", [], [Xml.PCData id]) ; Xml.Element("Data", [], [to_xml_expr expr])]) in 
  let xml_function (id, args, cmds, ret) = 
    Xml.Element("Function", (("name", id) :: fst (List.fold_left (fun (attrs, k) arg -> (attrs @ [("input " ^ (string_of_int k), arg)], k+1)) ([],0) args)), 
      [
        Xml.Element("Commands", [], [to_xml_stmts cmds]);
        Xml.Element("Return", [], [to_xml_indexed_var ret])
      ]) in 
  let xml_main cmds = 
      Xml.Element("Main", [], [to_xml_stmts cmds]) in 

    Xml.Element(tag_process, 
      ("pid", string_of_int k) :: ("pname", s) :: (attks_to_attr attks), 
      List.concat [(List.map xml_ch chs) ;
      (List.map xml_file fls) ;
      (List.map xml_variable vars) ;
      (List.map xml_function fns) ; [xml_main m]])

let to_xml_sys s =
  Xml.Element("System", [], List.map to_xml_proc s.Context.sys_process)

