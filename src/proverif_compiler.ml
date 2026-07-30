open Rabbit_proverif_pv_parse

type error =
  | Unsupported of string

exception Error of error Location.located

let error ~loc err = Stdlib.raise (Error (Location.locate ~loc err))

let print_error err ppf =
  match err with
  | Unsupported s -> Format.pp_print_string ppf s

type env =
  { string_table : (string, Pitptree.ident) Hashtbl.t
  ; syscall_table : (string, Pitptree.ident) Hashtbl.t
  ; allow_entries : (Pitptree.ident * Pitptree.ident * Pitptree.ident) Queue.t
  ; process_type_table : (string, Pitptree.ident) Hashtbl.t
  ; top_process : Pitptree.tprocess_e option ref
  }

let create_env () : env =
  { string_table = Hashtbl.create 16
  ; syscall_table = Hashtbl.create 16
  ; allow_entries = Queue.create ()
  ; process_type_table = Hashtbl.create 16
  ; top_process = ref None
  }

let pv_ident (s : string) : Pitptree.ident = s, Parsing_helper.dummy_ext

let compile_ident (id : Typed.ident) : Pitptree.ident = pv_ident (Ident.to_string id)

let bitstring_ident : Pitptree.ident = pv_ident "bitstring"
let channel_ident : Pitptree.ident = pv_ident "channel"
let proc_t_ident : Pitptree.ident = pv_ident "proc_t"
let acc_data_t_ident : Pitptree.ident = pv_ident "acc_data_t"
let syscall_t_ident : Pitptree.ident = pv_ident "syscall_t"
let access_control_table_ident : Pitptree.ident = pv_ident "access_control_table"
let file_type_table_ident : Pitptree.ident = pv_ident "file_type_table"
let channel_table_ident : Pitptree.ident = pv_ident "channel_table"
let true_ident : Pitptree.ident = pv_ident "true"
let false_ident : Pitptree.ident = pv_ident "false"

let term (t : Pitptree.term) : Pitptree.term_e = t, Parsing_helper.dummy_ext
let pterm (t : Pitptree.pterm) : Pitptree.pterm_e = t, Parsing_helper.dummy_ext
let process (p : Pitptree.tprocess) : Pitptree.tprocess_e = p, Parsing_helper.dummy_ext

let register_process_type (env : env) (process_id : Typed.ident) (typ : Typed.ident) : unit =
  Hashtbl.replace env.process_type_table (Ident.to_string process_id) (compile_ident typ)

let find_process_type ~loc (env : env) (process_id : Typed.ident) : Pitptree.ident =
  match Hashtbl.find_opt env.process_type_table (Ident.to_string process_id) with
  | Some typ -> typ
  | None ->
      error ~loc
        (Unsupported
           (Printf.sprintf "process type for %s is not available in ProVerif system translation"
              (Ident.to_string process_id)))

let is_ident_char = function
  | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> true
  | _ -> false

let sanitize_string_for_ident (s : string) : string =
  let buf = Buffer.create (String.length s) in
  let prev_underscore = ref false in
  String.iter
    (fun c ->
       if is_ident_char c then (
         Buffer.add_char buf c;
         prev_underscore := false
       ) else if not !prev_underscore then (
         Buffer.add_char buf '_';
         prev_underscore := true
       ))
    s;
  let sanitized = Buffer.contents buf in
  let len = String.length sanitized in
  let start =
    let rec find i =
      if i >= len then len
      else if sanitized.[i] = '_' then find (i + 1)
      else i
    in
    find 0
  in
  let stop =
    let rec find i =
      if i < start then start - 1
      else if sanitized.[i] = '_' then find (i - 1)
      else i
    in
    find (len - 1)
  in
  if start > stop then
    "string"
  else
    String.sub sanitized start (stop - start + 1)

let fresh_string_ident (env : env) (s : string) : Pitptree.ident =
  match Hashtbl.find_opt env.string_table s with
  | Some id -> id
  | None ->
      let base = "str__" ^ sanitize_string_for_ident s in
      let rec loop i =
        let name =
          if i = 1 then base else Printf.sprintf "%s__%d" base i
        in
        let id = pv_ident name in
        if Hashtbl.fold (fun _ existing found -> found || existing = id) env.string_table false then
          loop (i + 1)
        else
          id
      in
      let id = loop 1 in
      Hashtbl.add env.string_table s id;
      id

let fresh_syscall_ident (env : env) (id : Typed.ident) : Pitptree.ident =
  let name = Ident.to_string id in
  match Hashtbl.find_opt env.syscall_table name with
  | Some id -> id
  | None ->
      let base = sanitize_string_for_ident name ^ "_s" in
      let rec loop i =
        let candidate =
          if i = 1 then base else Printf.sprintf "%s__%d" base i
        in
        let id = pv_ident candidate in
        if Hashtbl.fold (fun _ existing found -> found || existing = id) env.syscall_table false then
          loop (i + 1)
        else
          id
      in
      let syscall_ident = loop 1 in
      Hashtbl.add env.syscall_table name syscall_ident;
      syscall_ident

let zero_term () : Pitptree.term_e = term (Pitptree.PIdent (pv_ident "0"))

let rec unfold_int (t : Pitptree.term_e) (n : int) : Pitptree.term_e =
  match n with
  | 0 -> t
  | n ->
      term (Pitptree.PFunApp (pv_ident "+", [unfold_int t (n - 1)]))

let unfold_int_minus (t : Pitptree.term_e) (n : int) : Pitptree.term_e =
  match n with
  | 0 -> t
  | n ->
      term (Pitptree.PFunApp (pv_ident ("- " ^ string_of_int n), [t]))

let rec compile_expr_to_term (env : env) (expr : Typed.expr) : Pitptree.term_e =
  match expr.desc with
  | Typed.Ident { id; _ } -> term (PIdent (compile_ident id))
  | Apply (id, args) ->
      term (Pitptree.PFunApp (compile_ident id, List.map (compile_expr_to_term env) args))
  | Tuple exprs -> term (PTuple (List.map (compile_expr_to_term env) exprs))
  | Unit -> term (PTuple [])
  | String s -> term (PIdent (fresh_string_ident env s))
  | Boolean true -> term (PIdent (pv_ident "true"))
  | Boolean false -> term (PIdent (pv_ident "false"))
  | Integer n when n >= 0 -> unfold_int (zero_term ()) n
  | Integer n -> unfold_int_minus (zero_term ()) (-n)
  | Float _ -> error ~loc:expr.loc (Unsupported "Float terms are not supported in ProVerif term translation")

let rec compile_expr_to_pterm (env : env) (expr : Typed.expr) : Pitptree.pterm_e =
  match expr.desc with
  | Typed.Ident { id; _ } -> pterm (PPIdent (compile_ident id))
  | Apply (id, args) ->
      pterm (PPFunApp (compile_ident id, List.map (compile_expr_to_pterm env) args))
  | Tuple exprs -> pterm (PPTuple (List.map (compile_expr_to_pterm env) exprs))
  | Unit -> pterm (PPTuple [])
  | String s -> pterm (PPIdent (fresh_string_ident env s))
  | Boolean true -> pterm (PPIdent true_ident)
  | Boolean false -> pterm (PPIdent false_ident)
  | Integer _ ->
      error ~loc:expr.loc
        (Unsupported "Integer process terms are not supported yet in ProVerif system translation")
  | Float _ ->
      error ~loc:expr.loc
        (Unsupported "Float process terms are not supported in ProVerif system translation")

let compile_function ~loc:(_loc : Location.t) (id : Typed.ident) (arity : int) : Pitptree.tdecl =
  let name = compile_ident id in
  let arg_tys = List.init arity (fun _ -> bitstring_ident) in
  TFunDecl (name, arg_tys, bitstring_ident, [])

let compile_equation ~loc:(_loc : Location.t) (env : env) (lhs : Typed.expr) (rhs : Typed.expr) : Pitptree.tdecl =
  let envdecl =
    List.sort_uniq compare (Typed.vars_of_expr lhs @ Typed.vars_of_expr rhs)
    |> List.map (fun id -> compile_ident id, bitstring_ident)
  in
  let lhs_term = compile_expr_to_term env lhs in
  let rhs_term = compile_expr_to_term env rhs in
  let equality_term =
    term (PFunApp (pv_ident "=", [lhs_term; rhs_term]))
  in
  TEquation ([envdecl, EETerm equality_term], [])

let compile_syscall
    ~loc
    (_id : Typed.ident)
    (_args : Typed.ident list)
    (_cmd : Typed.cmd)
    (_attack : bool)
  =
  error ~loc (Unsupported "compile_syscall is not implemented yet")

let compile_attack
    ~loc
    (_id : Typed.ident)
    (_syscall : Typed.ident)
    (_args : Typed.ident list)
    (_cmd : Typed.cmd)
  =
  error ~loc (Unsupported "compile_attack is not implemented yet")

let compile_type ~loc:(_loc : Location.t) (id : Typed.ident) (typclass : Input.type_class) =
  let ty =
    match typclass with
    | CProc -> proc_t_ident
    | CFsys | CChan -> acc_data_t_ident
  in
  Pitptree.TConstDecl (compile_ident id, ty, [])

let compile_allow
    ~loc
    (env : env)
    (process_typ : Typed.ident)
    (target_typs : Typed.ident list)
    (syscalls : Typed.ident list option)
  =
  let process_typ = compile_ident process_typ in
  let target_typs = List.map compile_ident target_typs in
  match syscalls with
  | None ->
      error ~loc
        (Unsupported "allow ... [.] is not supported yet in ProVerif translation")
  | Some syscalls ->
      List.iter
        (fun target_typ ->
           List.iter
             (fun syscall ->
                let syscall_ident = fresh_syscall_ident env syscall in
                Queue.add (process_typ, target_typ, syscall_ident) env.allow_entries)
             syscalls)
        target_typs;
      []

let compile_allow_attack
    ~loc
    (_process_typs : Typed.ident list)
    (_attacks : Typed.ident list)
  =
  error ~loc (Unsupported "compile_allow_attack is not implemented yet")

let compile_init ~loc (_id : Typed.ident) (_desc : Typed.init_desc) =
  error ~loc (Unsupported "compile_init is not implemented yet")

let compile_channel
    ~loc
    (_id : Typed.ident)
    (_param : unit option)
    (_typ : Typed.ident)
  =
  error ~loc (Unsupported "compile_channel is not implemented yet")

let compile_process
    ~loc
    (_id : Typed.ident)
    (_param : Typed.ident option)
    (_args : Typed.chan_param list)
    (_typ : Typed.ident)
    (_files : (Typed.expr * Typed.ident * Typed.expr) list)
    (_vars : (Typed.ident * Typed.expr) list)
    (_funcs : (Typed.ident * Typed.ident list * Typed.cmd) list)
    (_main : Typed.cmd)
  =
  error ~loc (Unsupported "compile_process is not implemented yet")

let compile_proc_call (env : env) (proc : Typed.proc) : Pitptree.tprocess_e =
  let proc_desc = proc.data in
  let proc_type = find_process_type ~loc:proc.loc env proc_desc.id in
  let args =
    pterm (PPIdent proc_type)
    ::
    (match proc_desc.parameter with
     | None -> []
     | Some _ ->
         error ~loc:proc.loc
           (Unsupported "Parameterized process instantiation is not supported yet"))
    @
    List.map
      (fun ({ channel; parameter; _ } : Typed.chan_arg) ->
         match parameter with
         | None -> pterm (PPIdent (compile_ident channel))
         | Some None | Some (Some _) ->
             error ~loc:proc.loc
               (Unsupported "Parameterized channel instantiation is not supported yet"))
      proc_desc.args
  in
  process (PLetDef (compile_ident proc_desc.id, args, None))

let parallel_processes (procs : Pitptree.tprocess_e list) : Pitptree.tprocess_e =
  match procs with
  | [] -> process PNil
  | proc :: procs ->
      List.fold_left
        (fun acc proc -> process (PPar (acc, proc)))
        proc
        procs

let compile_proc_group_desc (env : env) (proc_group : Typed.proc_group_desc) : Pitptree.tprocess_e =
  match proc_group with
  | Unbounded proc -> compile_proc_call env proc
  | Bounded (_id, procs) ->
      process (PRepl (parallel_processes (List.map (compile_proc_call env) procs)))

let compile_system
    ~loc
    (env : env)
    (procs : Typed.proc_group_desc list)
    (_lemmas : (Typed.ident * Typed.lemma) list)
  =
  let top_process = parallel_processes (List.map (compile_proc_group_desc env) procs) in
  match !(env.top_process) with
  | None ->
      env.top_process := Some top_process;
      []
  | Some _ ->
      error ~loc (Unsupported "Multiple system declarations are not supported yet")

let compile_prelude (_env : env) : Pitptree.tdecl list =
  [ TTypeDecl proc_t_ident
  ; TTypeDecl acc_data_t_ident
  ; TTypeDecl syscall_t_ident
  ; TTableDecl
      (access_control_table_ident, [proc_t_ident; acc_data_t_ident; syscall_t_ident])
  ; TTableDecl
      (file_type_table_ident, [proc_t_ident; acc_data_t_ident; bitstring_ident])
  ; TTableDecl
      (channel_table_ident, [acc_data_t_ident; channel_ident])
  ; TConstDecl (true_ident, bitstring_ident, [])
  ; TConstDecl (false_ident, bitstring_ident, [])
  ]

let compile_generated_string_consts (env : env) : Pitptree.tdecl list =
  Hashtbl.to_seq_values env.string_table
  |> List.of_seq
  |> List.sort_uniq compare
  |> List.map (fun id -> Pitptree.TConstDecl (id, bitstring_ident, []))

let compile_generated_syscall_consts (env : env) : Pitptree.tdecl list =
  Hashtbl.to_seq_values env.syscall_table
  |> List.of_seq
  |> List.sort_uniq compare
  |> List.map (fun id -> Pitptree.TConstDecl (id, syscall_t_ident, []))

let wrap_with_allow_init (env : env) (body : Pitptree.tprocess_e) : Pitptree.tprocess_e =
  let entries = List.of_seq (Queue.to_seq env.allow_entries) in
  List.fold_right
    (fun (process_typ, target_typ, syscall_ident) acc ->
       process
         (PInsert
            ( access_control_table_ident
            , [ pterm (PPIdent process_typ)
              ; pterm (PPIdent target_typ)
              ; pterm (PPIdent syscall_ident)
              ]
            , acc )))
    entries
    body

let rec collect_process_types (env : env) (decls : Typed.decl list) : unit =
  List.iter
    (fun (decl : Typed.decl) ->
       match decl.desc with
       | Process { id; typ; _ } -> register_process_type env id typ
       | Load (_filename, decls) -> collect_process_types env decls
       | _ -> ())
    decls

let rec compile_load (env : env) (_filename : string) (decls : Typed.decl list) : Pitptree.tdecl list =
  List.concat_map (compile_decl env) decls

and compile_decl (env : env) (decl : Typed.decl) : Pitptree.tdecl list =
  match decl.desc with
  | Function { id; arity } -> [compile_function ~loc:decl.loc id arity]
  | Equation (lhs, rhs) -> [compile_equation ~loc:decl.loc env lhs rhs]
  | Syscall { id; args; cmd; attack } -> [compile_syscall ~loc:decl.loc id args cmd attack]
  | Attack { id; syscall; args; cmd } -> [compile_attack ~loc:decl.loc id syscall args cmd]
  | Type { id; typclass } -> [compile_type ~loc:decl.loc id typclass]
  | Allow { process_typ; target_typs; syscalls } ->
      compile_allow ~loc:decl.loc env process_typ target_typs syscalls
  | AllowAttack { process_typs; attacks } ->
      [compile_allow_attack ~loc:decl.loc process_typs attacks]
  | Init { id; desc } -> [compile_init ~loc:decl.loc id desc]
  | Channel { id; param; typ } -> [compile_channel ~loc:decl.loc id param typ]
  | Process { id; param; args; typ; files; vars; funcs; main } ->
      [compile_process ~loc:decl.loc id param args typ files vars funcs main]
  | System (procs, lemmas) -> compile_system ~loc:decl.loc env procs lemmas
  | Load (filename, decls) -> compile_load env filename decls

let compile_program (decls : Typed.decl list) =
  let env = create_env () in
  collect_process_types env decls;
  let body = List.concat_map (compile_decl env) decls in
  let top_process =
    match !(env.top_process) with
    | Some top_process -> wrap_with_allow_init env top_process
    | None -> wrap_with_allow_init env (process PNil)
  in
  ( compile_prelude env
    @ compile_generated_syscall_consts env
    @ compile_generated_string_consts env
    @ body
  , top_process
  , None )
