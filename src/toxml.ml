type to_xml_error =
  | UnintendedError 

exception Error of to_xml_error Location.located

(** [error ~loc err] raises the given runtime error. *)
let error ?(loc=Location.Nowhere) err = Stdlib.raise (Error (Location.locate ~loc err))

(** Print error description. *)
let print_error err ppf =
  match err with
  | UnintendedError -> Format.fprintf ppf "unintended behavior. Contact the developer"

let string_of_ins i = i
(*     let (s, _, _) = List.find (fun (_, s, _) -> s = i) Primitives.primitive_ins in
    s
 *)


let attks_to_attr attks = 
  List.map (fun a -> (a, "true")) attks

let accs_to_attr accs = 
  List.map (fun a -> (a, "true")) accs
  (* List.map (fun a -> (Printer.print_access_class a, "true")) accs *)

let to_xml_attks attks = 
  Xml.Element ("attack", List.map (fun a -> ( a, "true")) attks, [])

let to_xml_accs accs = 
  Xml.Element ("access", List.map (fun a -> (a, "true")) accs, [])
  (* Xml.Element ("access", List.map (fun a -> (Printer.print_access_class a, "true")) accs, []) *)

let mypcdata s = Xml.Element ("value", [], [Xml.PCData s])

type engine = {
  eng_ext_const : (string * int) list ; 
  eng_ext_func : (string * int) list ; 
  eng_const : (string * int) list ; 
  eng_ch : (string * int) list ; 
  eng_event : (string * int) list ; 
  eng_mem_func : (int * (string * int) list) list ; 
  id : int 
}

let eng_init = {
  eng_ext_const = [];
  eng_ext_func = [];
  eng_const = [];
  eng_ch = [];
  eng_event = [];
  eng_mem_func = [];
  id = 0;

}

let eng_inc eng = 
  {eng with id=eng.id+1}

let get_new_proc_id eng = 
  let i = eng.id in let eng = eng_inc eng in 
  ({eng with eng_mem_func=(i, [])::eng.eng_mem_func}, i)



let eng_add_ext_const eng n = 
  let i = eng.id in let eng = eng_inc eng in 
  ({eng with eng_ext_const=(n, i)::eng.eng_ext_const}, i )

let eng_add_mem_func eng n = 
  let i = eng.id in let eng = eng_inc eng in 
   match eng.eng_mem_func with 
   | (pid, nl)::frames -> ({eng with eng_mem_func=(pid,(n, i)::nl)::frames}, i)
   | _ -> error  (UnintendedError)

let eng_get_mem_fun eng n = 
 match eng.eng_mem_func with 
   | (pid, nl)::frames -> snd (List.find (fun (m, _) -> n = m) nl)
   | _ -> error  (UnintendedError)
  
let eng_add_ext_func eng n = 
  let i = eng.id in let eng = eng_inc eng in 
  ({eng with eng_ext_func=(n, i)::eng.eng_ext_func}, i )

let eng_add_const eng n = 
  let i = eng.id in let eng = eng_inc eng in 
  ({eng with eng_const=(n, i)::eng.eng_const}, i )

let eng_add_ch eng n = 
  let i = eng.id in let eng = eng_inc eng in 
  ({eng with eng_ch=(n, i)::eng.eng_ch}, i )

let eng_add_event eng n = 
  let i = eng.id in let eng = eng_inc eng in 
  ({eng with eng_event=(n, i)::eng.eng_event}, i )

let eng_get_ext_const eng n = 
  snd (List.find (fun (m, _) -> n = m) eng.eng_ext_const)

let eng_get_ext_func eng n = 
  snd (List.find (fun (m, _) -> n = m) eng.eng_ext_func)

let eng_get_const eng n = 
  snd (List.find (fun (m, _) -> n = m) eng.eng_const)

let eng_get_ch eng n = 
  snd (List.find (fun (m, _) -> n = m) eng.eng_ch)

let eng_get_event eng n = 
  snd (List.find (fun (m, _) -> n = m) eng.eng_event)

let to_xml_ext_const eng n  = 
  let (eng, k) = eng_add_ext_const eng n in
  (eng, Xml.Element ("ext_const", [("id", string_of_int k) ; ("name", n)], []))

let to_xml_ext_func eng (n, k) = 
  let (eng, i) = eng_add_ext_func eng n in
  (eng, Xml.Element ("ext_func", [("id", string_of_int i); ("name", n) ;("arity", string_of_int k)], []))

let to_xml_indexed_var (s, i, j, k) =
  Xml.Element ("expr_var", [("name", s) ; ("frame",string_of_int i) ; ("de_Bruijn",string_of_int j) ; ("total_de_Bruijn",string_of_int k)], [])


let rec to_xml_expr eng {Location.data=c; Location.loc=loc} = 
   let to_xml_expr' eng = function
    | Syntax.Const s -> Xml.Element ("expr_const", [("const_name", s); "const_ref", string_of_int (eng_get_const eng s)], [])
    | Syntax.ExtConst s -> Xml.Element ("expr_ext_const", [("ext_const_name", s); ("ext_const_ref", string_of_int (eng_get_ext_const eng s))], [])
    | Syntax.Variable (s,i,j, k) -> to_xml_indexed_var(s,i,j, k)
    | Syntax.Boolean b -> Xml.Element ("expr_boolean", [], [mypcdata (string_of_bool b)])
    | Syntax.String s -> Xml.Element ("expr_string", [], [mypcdata s])
    | Syntax.Integer k -> Xml.Element ("expr_integer", [], [mypcdata (string_of_int k)])
    | Syntax.Float s -> Xml.Element ("expr_float", [], [mypcdata s])
    | Syntax.Apply (o, el) -> 
      Xml.Element ("expr_apply", [
          ("ext_func_ref", string_of_int (eng_get_ext_func eng o)) ; 
          ("ext_func_name", o)
        ], 
        (List.map (to_xml_expr eng) el))
    | Syntax.Tuple el -> Xml.Element ("expr_tuple", [], List.map (to_xml_expr eng) el)
    | Syntax.Channel (s,_) -> Xml.Element ("expr_channel", [("ch_name", s) ; ("ch_ref", string_of_int (eng_get_ch eng s))], [])
    | Syntax.FrVariable s -> error ~loc UnintendedError  
  in Xml.Element ("expr", [], [to_xml_expr' eng c])

and to_xml_ext_eq eng (nl, e1, e2)  = 
  (eng, Xml.Element ("ext_eq", [], [to_xml_expr eng e1 ; to_xml_expr eng e2]))

and to_xml_const eng (n, e)  = 
  let (eng, i) = eng_add_const eng n in
  (eng, Xml.Element ("const", [("id", string_of_int i); ("name", n)], [to_xml_expr eng e]))

and to_xml_ch eng (n, attks)  = 
  let (eng, i) = eng_add_ch eng n in
  (eng, Xml.Element ("channel", [("name", n) ; ("id", string_of_int i)], 
                   [Xml.Element ("attack", List.map (fun a -> (a, "true")) attks, [])]))

and to_xml_event eng (n, k) = 
  let (eng, i) = eng_add_event eng n in
  (eng, Xml.Element("event", [("name", n);("id", string_of_int i) ; ("arity", string_of_int k)], []))

let to_xml_event_call eng {Location.data=c; Location.loc=loc} = 
  match c with  
  | Syntax.Event (eid, ivl) -> 
    Xml.Element ("event_call", [("event_ref", string_of_int (eng_get_event eng eid)) ; ("event_name", eid)], List.map (to_xml_expr eng) ivl)

let rec to_xml_stmt eng {Location.data=c; Location.loc=loc}  = 
  match c with
  | Syntax.OpStmt a -> Xml.Element ("stmt", [], [to_xml_atomic_stmt eng a])
  | Syntax.EventStmt (a, el) -> Xml.Element ("stmt", [], (to_xml_atomic_stmt eng a) :: (List.map (to_xml_event_call eng) el))
  
and to_xml_atomic_stmt eng {Location.data=c; Location.loc=loc}  = 
  let to_xml_atomic_stmt' eng = function  
    | Syntax.Skip -> Xml.Element ("a_stmt_skip", [], [])
    | Syntax.Let (v, e) -> Xml.Element ("a_stmt_let", [], (to_xml_indexed_var v) :: [to_xml_expr eng e])
    | Syntax.Call (v, f, args) -> 
      Xml.Element ("a_stmt_call", [("mem_func_ref", string_of_int (eng_get_mem_fun eng f)); ("mem_func_name", f)], (to_xml_indexed_var v) :: (List.map (to_xml_expr eng) args))
    | Syntax.Syscall (v, ins, args) -> 
      Xml.Element ("a_stmt_instruction", [("ins_name", string_of_ins ins)], (to_xml_indexed_var v) :: (List.map (to_xml_expr eng) (List.map fst args)))
    | Syntax.If (e, c1, c2) -> 
      Xml.Element ("a_stmt_ite", [],
        [(Xml.Element("cond", [], [to_xml_expr eng e])) ; (Xml.Element("then", [], List.map (to_xml_stmt eng) c1)) ; (Xml.Element("else", [], List.map (to_xml_stmt eng) c2))])
    | Syntax.For (v, i, j, c) -> 
      Xml.Element ("a_stmt_for", [("from", string_of_int i) ; ("to", string_of_int j)], 
        
          to_xml_indexed_var v ::
          List.map (to_xml_stmt eng) c
        )
  in Xml.Element ("a_stmt", [], [to_xml_atomic_stmt' eng c])





let to_xml_proc eng {
  Context.proc_pid=k;
  Context.proc_name=s;
  Context.proc_attack=attks;
  Context.proc_channel=chs;
  Context.proc_file=fls;
  Context.proc_variable=vars;
  Context.proc_function=fns;
  Context.proc_main=m
} = 
  let (eng, i) = get_new_proc_id eng in 
  let vars = List.rev vars in 
  let fns = List.rev fns in 
  let xml_ch' (n, acc, attk) =
    Xml.Element("channel_access", [("channel_ref", string_of_int (eng_get_ch eng n)); ("channel_name", n)], [to_xml_accs acc]) in
  let xml_ch = (List.map xml_ch' (List.rev chs)) in 
  let xml_file' (p, data, accs, attks) = 
    Xml.Element("file", [], 
      [
        Xml.Element("path", [], [Xml.PCData p]) ;
        Xml.Element("initial_data", [], [to_xml_expr eng data]) ; 
        to_xml_attks attks ; 
        to_xml_accs accs
      ]) in 
  let xml_file = List.map xml_file' fls in 

  let xml_variable' (id, expr) = 
    Xml.Element("mem_var", [("name", id)], [to_xml_expr eng expr]) in 

  let xml_variable = List.map xml_variable' vars in 

  let xml_function' eng' (id, args, cmds, ret) = 
    let (eng'', j) = eng_add_mem_func eng' id in 
    (eng'', 
      Xml.Element("mem_func", [("name", id);("id", string_of_int j)],
        List.map (fun arg -> Xml.Element ("argument", [("name", arg)], [])) args @
        [Xml.Element ("body", [], List.map (to_xml_stmt eng') cmds) ; 
          Xml.Element ("return", [], [to_xml_indexed_var ret])])) in 
  
  let (eng, xml_function) = List.fold_left (fun (eng, xml_function) func -> let (a, b) = xml_function' eng func in (a, xml_function @ [b])) (eng, []) fns in 

    (eng, Xml.Element("process", 
      [("id", string_of_int i) ; ("name", s ^ (string_of_int k))],
      to_xml_attks attks :: xml_ch @ xml_file @ xml_variable @ xml_function @ [Xml.Element ("main", [], [Xml.Element ("body", [], List.map (to_xml_stmt eng) m)])]))


let to_xml_sys 
  {Context.sys_ctx=ctx; Context.sys_def=def; Context.sys_pol=pol; Context.sys_proc=proc} =
  let eng = eng_init in 
  let (eng, ext_const_xmls) = 
    List.fold_left (fun (eng, ext_const_xmls) ext_const -> 
                    let (eng, ext_const_xml) = to_xml_ext_const eng ext_const in
                    (eng, ext_const_xmls @ [ext_const_xml])) (eng, []) (List.rev ctx.Context.ctx_ext_const) in 
  let (eng, ext_func_xmls) = 
    List.fold_left (fun (eng, ext_func_xmls) ext_func -> 
                    let (eng, ext_func_xml) = to_xml_ext_func eng ext_func in
                    (eng, ext_func_xmls @ [ext_func_xml])) (eng, []) (List.rev ctx.Context.ctx_ext_func) in 
  let (eng, ext_eq_xmls) = 
    List.fold_left (fun (eng, ext_eq_xmls) ext_eq -> 
                    let (eng, ext_eq_xml) = to_xml_ext_eq eng ext_eq in
                    (eng, ext_eq_xmls @ [ext_eq_xml])) (eng, []) (List.rev def.Context.def_ext_eq) in 
  let (eng, event_xmls) = 
    List.fold_left (fun (eng, event_xmls) event -> 
                  let (eng, event_xml) = to_xml_event eng event in
                  (eng, event_xmls @ [event_xml])) (eng, []) (List.rev ctx.Context.ctx_event) in 

  let (eng, ch_xmls) = 
    List.fold_left (fun (eng, ch_xmls) (ch,ty) -> 
                    let attks = List.fold_left (fun attks (s, a) -> if s = ty then a::attks else attks) [] pol.Context.pol_attack in 
                    let (eng, ch_xml) = to_xml_ch eng (ch,attks) in
                    (eng, ch_xmls @ [ch_xml])) (eng, []) (List.rev ctx.Context.ctx_ch) in 

  let (eng, proc_xmls) = List.fold_left (fun (eng, proc_xmls) proc -> let (eng, proc_xml) = to_xml_proc eng proc in (eng, proc_xml::proc_xmls)) (eng, []) proc in
  Xml.Element("system", [], ext_const_xmls @ ext_func_xmls @ ext_eq_xmls @ event_xmls @ ch_xmls @ proc_xmls)

(* <!ELEMENT system (ext_const*,ext_func*,ext_eq*,event*,channel*,process*)

