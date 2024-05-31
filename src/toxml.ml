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
    let (s, _, _) = List.find (fun (_, s, _) -> s = i) Loader.primitive_ins in
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
    | Syntax.Channel s -> Xml.Element (tag_expr, [("constr", "channel")], [Xml.PCData s])
    | Syntax.FrVariable s -> error ~loc UnintendedError  

let to_xml_event {Location.data=c; Location.loc=loc} ppf = 
  match c with  
  | Syntax.Event (eid, ivl) -> 
    Xml.Element (tag_event, [("name",eid)], List.map to_xml_indexed_var ivl)

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

and to_xml_stmts cs = Xml.Element (tag_stmts, [], List.map pprint_stmt cs)
