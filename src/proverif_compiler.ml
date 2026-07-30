open Rabbit_proverif_pv_parse

type error =
  | Unsupported of string
  | Invalid_input of string
  | Internal_error of string

exception Error of error Location.located

let error ~loc err = Stdlib.raise (Error (Location.locate ~loc err))

let print_error err ppf =
  match err with
  | Unsupported s -> Format.pp_print_string ppf s
  | Invalid_input s -> Format.pp_print_string ppf s
  | Internal_error s -> Format.pp_print_string ppf s

type env =
  { string_table : (string, Pitptree.ident) Hashtbl.t
  ; syscall_table : (string, Pitptree.ident) Hashtbl.t
  ; generated_name_table : (string, unit) Hashtbl.t
  ; generated_name_counter : (string, int) Hashtbl.t
  ; allow_entries : (Pitptree.ident * Pitptree.ident * Pitptree.ident) Queue.t
  ; process_type_table : (string, Pitptree.ident) Hashtbl.t
  ; structure_table : (string, int) Hashtbl.t
  ; event_table : (string, int) Hashtbl.t
  ; mutable top_process : Pitptree.tprocess_e option
  }

let create_env () : env =
  { string_table = Hashtbl.create 16
  ; syscall_table = Hashtbl.create 16
  ; generated_name_table = Hashtbl.create 64
  ; generated_name_counter = Hashtbl.create 64
  ; allow_entries = Queue.create ()
  ; process_type_table = Hashtbl.create 16
  ; structure_table = Hashtbl.create 16
  ; event_table = Hashtbl.create 16
  ; top_process = None
  }

let with_dummy_ext x = x, Parsing_helper.dummy_ext

let pv_ident (s : string) : Pitptree.ident = with_dummy_ext s

let compile_ident (id : Typed.ident) : Pitptree.ident =
  pv_ident (Ident.to_string id)

let bitstring_ident : Pitptree.ident = pv_ident "bitstring"
let channel_ident : Pitptree.ident = pv_ident "channel"
let param_data_ident : Pitptree.ident = pv_ident "param_data"
let proc_t_ident : Pitptree.ident = pv_ident "proc_t"
let acc_data_t_ident : Pitptree.ident = pv_ident "acc_data_t"
let syscall_t_ident : Pitptree.ident = pv_ident "syscall_t"
let access_control_table_ident : Pitptree.ident =
  pv_ident "access_control_table"
let file_type_table_ident : Pitptree.ident = pv_ident "file_type_table"
let channel_table_ident : Pitptree.ident = pv_ident "channel_table"
let deleted_address_table_ident : Pitptree.ident =
  pv_ident "deleted_address_table"
let attacker_channel_ident : Pitptree.ident = pv_ident "attacker"
let true_ident : Pitptree.ident = pv_ident "true"
let false_ident : Pitptree.ident = pv_ident "false"
let ptype_arg_ident : Pitptree.ident = pv_ident "ptype"
let none_syscall_ident : Pitptree.ident = pv_ident "none_syscall_s"
let precise_ident : Pitptree.ident = pv_ident "precise"
let private_option : Pitptree.ident * Pitptree.ident list option =
  pv_ident "private", None

let term (t : Pitptree.term) : Pitptree.term_e = with_dummy_ext t
let pterm (t : Pitptree.pterm) : Pitptree.pterm_e = with_dummy_ext t
let process (p : Pitptree.tprocess) : Pitptree.tprocess_e = with_dummy_ext p

let register_process_type env (process_id : Typed.ident) (typ : Typed.ident) =
  Hashtbl.replace
    env.process_type_table
    (Ident.to_string process_id)
    (compile_ident typ)

let find_process_type ~loc env (process_id : Typed.ident) : Pitptree.ident =
  match
    Hashtbl.find_opt env.process_type_table (Ident.to_string process_id)
  with
  | Some typ -> typ
  | None ->
      error ~loc
        (Internal_error
           (Printf.sprintf
              "process type for %s is not available in ProVerif system translation"
              (Ident.to_string process_id)))

let compile_name (name : Typed.name) : Pitptree.ident = pv_ident name

let structure_ctor_ident (name : Typed.name) : Pitptree.ident =
  compile_name name
let structure_addr_ident (name : Typed.name) : Pitptree.ident =
  pv_ident (name ^ "Addr")
let structure_arg_ident (name : Typed.name) (index : int) : Pitptree.ident =
  pv_ident (Printf.sprintf "%sPar%d" name index)

let register_structure ~loc env (name : Typed.name) (arity : int) =
  match Hashtbl.find_opt env.structure_table name with
  | None -> Hashtbl.add env.structure_table name arity
  | Some arity' when arity' = arity -> ()
  | Some arity' ->
      error ~loc
        (Invalid_input
           (Printf.sprintf
              "Structure %s is used with inconsistent arities (%d and %d)"
              name arity' arity))

let register_event env (name : Typed.name) (arity : int) =
  let key = name in
  match Hashtbl.find_opt env.event_table key with
  | None -> Hashtbl.add env.event_table key arity
  | Some arity' when arity' = arity -> ()
  | Some arity' ->
      error ~loc:Location.nowhere
        (Invalid_input
           (Printf.sprintf
              "Event %s is used with inconsistent arities (%d and %d)"
              name arity' arity))

let is_ident_char = function
  | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> true
  | _ -> false

let sanitize_string_for_ident s =
  let sanitized =
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
    Buffer.contents buf
  in
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
    "x"
  else
    String.sub sanitized start (stop - start + 1)

let fresh_generated_ident env ~base : Pitptree.ident =
  let rec loop candidate =
    if Hashtbl.mem env.generated_name_table candidate then (
      let next_index =
        match Hashtbl.find_opt env.generated_name_counter base with
        | None -> 2
        | Some index -> index
      in
      Hashtbl.replace env.generated_name_counter base (next_index + 1);
      loop (Printf.sprintf "%s__%d" base next_index)
    ) else (
      Hashtbl.add env.generated_name_table candidate ();
      pv_ident candidate
    )
  in
  loop base

let fresh_string_ident env s : Pitptree.ident =
  match Hashtbl.find_opt env.string_table s with
  | Some id -> id
  | None ->
      let base = "str__" ^ sanitize_string_for_ident s in
      let id = fresh_generated_ident env ~base in
      Hashtbl.add env.string_table s id;
      id

let fresh_syscall_ident (env : env) (id : Typed.ident) : Pitptree.ident =
  let name = Ident.to_string id in
  match Hashtbl.find_opt env.syscall_table name with
  | Some id -> id
  | None ->
      let base = sanitize_string_for_ident name ^ "_s" in
      let syscall_ident = fresh_generated_ident env ~base in
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

let rec compile_expr_to_term env (expr : Typed.expr) : Pitptree.term_e =
  match expr.desc with
  | Typed.Ident { id; param = Some param; _ } ->
      term (PFunApp (compile_ident id, [compile_expr_to_term env param]))
  | Typed.Ident { id; _ } ->
      term (PIdent (compile_ident id))
  | Apply (id, args) ->
      term (Pitptree.PFunApp (compile_ident id, List.map (compile_expr_to_term env) args))
  | Tuple exprs ->
      term (PTuple (List.map (compile_expr_to_term env) exprs))
  | Unit ->
      term (PTuple [])
  | String s ->
      term (PIdent (fresh_string_ident env s))
  | Boolean true ->
      term (PIdent (pv_ident "true"))
  | Boolean false ->
      term (PIdent (pv_ident "false"))
  | Integer n when n >= 0 ->
      unfold_int (zero_term ()) n
  | Integer n ->
      (* Negative integer -n is represented as `0 - n` *)
      unfold_int_minus (zero_term ()) (-n)
  | Float _ ->
      error
        ~loc:expr.loc
        (Unsupported "Float terms are not supported in ProVerif term translation")

type process_env =
  { bindings : (Typed.ident * Pitptree.pterm_e) list
  ; proc_type : Pitptree.pterm_e
  ; curr_syscall : Pitptree.pterm_e option
  ; file_channel : Pitptree.pterm_e option
  }

let create_process_env
    ~(proc_type : Pitptree.pterm_e)
    ~(curr_syscall : Pitptree.pterm_e option)
    ~(file_channel : Pitptree.pterm_e option)
  : process_env =
  { bindings = []
  ; proc_type
  ; curr_syscall
  ; file_channel
  }

let bind_process_var (env : process_env) (id : Typed.ident) (value : Pitptree.pterm_e) =
  { env with bindings = (id, value) :: List.remove_assoc id env.bindings }

let unbind_process_var (env : process_env) (id : Typed.ident) =
  { env with bindings = List.remove_assoc id env.bindings }

let find_process_var (env : process_env) (id : Typed.ident) : Pitptree.pterm_e option =
  List.assoc_opt id env.bindings

let restore_process_var (env : process_env) (id : Typed.ident) (old_value : Pitptree.pterm_e option) =
  match old_value with
  | Some value -> bind_process_var env id value
  | None -> unbind_process_var env id

let restore_process_vars
    (env : process_env)
    (saved : (Typed.ident * Pitptree.pterm_e option) list)
  : process_env =
  List.fold_left
    (fun env (id, old_value) -> restore_process_var env id old_value)
    env
    saved

let find_process_var_exn ~loc (env : process_env) (id : Typed.ident) : Pitptree.pterm_e =
  match find_process_var env id with
  | Some value -> value
  | None ->
      error ~loc
        (Internal_error
           (Printf.sprintf "Loop-carried variable %s is not available"
              (Ident.to_string id)))

let rec compile_expr_to_pterm (genv : env) (penv : process_env) (expr : Typed.expr) : Pitptree.pterm_e =
  match expr.desc with
  | Typed.Ident { id; param = Some param; _ } ->
      pterm (PPFunApp (compile_ident id, [compile_expr_to_pterm genv penv param]))
  | Typed.Ident { id; _ } ->
      (match find_process_var penv id with
       | Some value -> value
       | None -> pterm (PPIdent (compile_ident id)))
  | Apply (id, args) ->
      pterm (PPFunApp (compile_ident id, List.map (compile_expr_to_pterm genv penv) args))
  | Tuple exprs ->
      pterm (PPTuple (List.map (compile_expr_to_pterm genv penv) exprs))
  | Unit ->
      pterm (PPTuple [])
  | String s ->
      pterm (PPIdent (fresh_string_ident genv s))
  | Boolean true ->
      pterm (PPIdent true_ident)
  | Boolean false ->
      pterm (PPIdent false_ident)
  | Integer _ ->
      error ~loc:expr.loc
        (Unsupported "Integer process terms are not supported yet in ProVerif process translation")
  | Float _ ->
      error ~loc:expr.loc
        (Unsupported "Float process terms are not supported in ProVerif process translation")

let compile_channel_expr (genv : env) (penv : process_env) (expr : Typed.expr) : Pitptree.pterm_e =
  compile_expr_to_pterm genv penv expr

let current_syscall ~loc (penv : process_env) : Pitptree.pterm_e =
  match penv.curr_syscall with
  | Some syscall -> syscall
  | None ->
      error ~loc
        (Internal_error "Current syscall is not available for access-control lowering")

let parallel_output
    (output_proc : Pitptree.tprocess_e)
    (body : Pitptree.tprocess_e)
  : Pitptree.tprocess_e =
  process (PPar (output_proc, body))

let wrap_with_access_control_get
    ~loc
    (penv : process_env)
    (target_type : Pitptree.pterm_e)
    (then_proc : Pitptree.tprocess_e)
    (else_proc : Pitptree.tprocess_e)
  : Pitptree.tprocess_e =
  (* Note: this assumes direct Rabbit accesses are mediated solely by the
     triple (current process type, target access-data type, current syscall).
     The current lowering uses [none_syscall_s] for direct process code via
     [allow ... [.]]. If the spec ends up distinguishing more direct-access
     contexts, this table lookup may need refinement. *)
  process
    (PGet
       ( access_control_table_ident
       , [ PPatEqual penv.proc_type
         ; PPatEqual target_type
         ; PPatEqual (current_syscall ~loc penv)
         ]
       , None
       , then_proc
       , else_proc
       , [] ))

let wrap_with_channel_access_get
    ~loc
    (channel_term : Pitptree.pterm_e)
    (penv : process_env)
    (then_proc : Pitptree.tprocess_e)
    (else_proc : Pitptree.tprocess_e)
  : Pitptree.tprocess_e =
  let channel_type_id = Ident.local "ch_type" in
  let channel_type_term = pterm (PPIdent (compile_ident channel_type_id)) in
  process
    (PGet
       ( channel_table_ident
       , [ PPatVar (compile_ident channel_type_id, Some acc_data_t_ident)
         ; PPatEqual channel_term
         ]
       , None
       , wrap_with_access_control_get ~loc penv channel_type_term then_proc else_proc
       , else_proc
       , [] ))

let wrap_with_file_access_get
    ~loc
    (path_term : Pitptree.pterm_e)
    (penv : process_env)
    (then_proc : Pitptree.tprocess_e)
    (else_proc : Pitptree.tprocess_e)
  : Pitptree.tprocess_e =
  let file_type_id = Ident.local "file_type" in
  let file_type_term = pterm (PPIdent (compile_ident file_type_id)) in
  process
    (PGet
       ( file_type_table_ident
       , [ PPatEqual penv.proc_type
         ; PPatVar (compile_ident file_type_id, Some acc_data_t_ident)
         ; PPatEqual path_term
         ]
       , None
       , wrap_with_access_control_get ~loc penv file_type_term then_proc else_proc
       , else_proc
       , [] ))

let structure_addr_term (name : Typed.name) (struct_term : Pitptree.pterm_e) : Pitptree.pterm_e =
  pterm (PPFunApp (structure_addr_ident name, [struct_term]))

let structure_arg_term (name : Typed.name) (index : int) (struct_term : Pitptree.pterm_e) : Pitptree.pterm_e =
  pterm (PPFunApp (structure_arg_ident name index, [struct_term]))

let loop_state_bindings (penv : process_env) : (Typed.ident * Pitptree.pterm_e) list =
  (* Note: the first loop lowering conservatively carries every current
     process binding across the loop boundary. This is simple and sounder than
     forgetting mutable state, but it may be larger than necessary. A later
     refinement could compute the true loop-carried live subset. *)
  List.rev penv.bindings

let loop_state_message
    ~done_flag
    ~loc
    (penv : process_env)
    (state_ids : Typed.ident list)
  : Pitptree.pterm_e =
  let flag_term =
    pterm (PPIdent (if done_flag then true_ident else false_ident))
  in
  match state_ids with
  | [] -> flag_term
  | _ ->
      pterm
        (PPTuple
           (flag_term
            :: List.map (find_process_var_exn ~loc penv) state_ids))

let loop_state_pattern
    ~done_flag
    (state_pattern_ids : Typed.ident list)
  : Pitptree.tpattern =
  let flag_pattern =
    Pitptree.PPatEqual
      (pterm (PPIdent (if done_flag then true_ident else false_ident)))
  in
  match state_pattern_ids with
  | [] -> flag_pattern
  | _ ->
      Pitptree.PPatTuple
        (flag_pattern
         :: List.map
              (fun id -> Pitptree.PPatVar (compile_ident id, Some bitstring_ident))
              state_pattern_ids)

let bind_loop_state
    (penv : process_env)
    (state_ids : Typed.ident list)
    (state_pattern_ids : Typed.ident list)
  : process_env =
  List.fold_left2
    (fun penv state_id pattern_id ->
       bind_process_var penv state_id (pterm (PPIdent (compile_ident pattern_id))))
    penv
    state_ids
    state_pattern_ids

let compile_event_fact (genv : env) (penv : process_env) (fact : Typed.fact) (body : Pitptree.tprocess_e)
  : Pitptree.tprocess_e =
  match fact.desc with
  | Global (name, args) ->
      register_event genv name (List.length args);
      process
        (PEvent
           ( compile_name name
           , List.map (compile_expr_to_pterm genv penv) args
           , None
           , body ))
  | Plain (name, args) ->
      register_event genv name (List.length args);
      process
        (PEvent
           ( compile_name name
           , List.map (compile_expr_to_pterm genv penv) args
           , None
           , body ))
  | _ ->
      error ~loc:fact.loc
        (Unsupported "Only plain/global event facts are supported in ProVerif event lowering")

let compile_put_fact (genv : env) (penv : process_env) (fact : Typed.fact) (body : Pitptree.tprocess_e)
  : Pitptree.tprocess_e =
  match fact.desc with
  | Channel { channel; name; args } ->
      let channel_term = compile_channel_expr genv penv channel in
      let payload =
        pterm
          (PPFunApp
             ( compile_name name
             , List.map (compile_expr_to_pterm genv penv) args ))
      in
      wrap_with_channel_access_get ~loc:fact.loc channel_term penv
        (parallel_output (process (POutput (channel_term, payload, process PNil))) body)
        (process PNil)
  | File { path; contents } ->
      let path_term = compile_expr_to_pterm genv penv path in
      let contents_term = compile_expr_to_pterm genv penv contents in
      let file_channel =
        match penv.file_channel with
        | Some file_channel -> file_channel
        | None ->
            error ~loc:fact.loc
              (Internal_error "File output requires a process-local file channel")
      in
      let payload = pterm (PPTuple [path_term; contents_term]) in
      wrap_with_file_access_get ~loc:fact.loc path_term penv
        (parallel_output (process (POutput (file_channel, payload, process PNil))) body)
        (process PNil)
  | Global ("Out", [arg]) ->
      process (POutput (pterm (PPIdent attacker_channel_ident), compile_expr_to_pterm genv penv arg, body))
  | Global (name, args) ->
      register_event genv name (List.length args);
      process
        (PEvent
           ( compile_name name
           , List.map (compile_expr_to_pterm genv penv) args
           , None
           , body ))
  | _ ->
      error ~loc:fact.loc
        (Unsupported "Only channel/global output facts are supported in ProVerif put lowering")

let compile_put_facts (genv : env) (penv : process_env) (facts : Typed.fact list) (body : Pitptree.tprocess_e)
  : Pitptree.tprocess_e =
  List.fold_right (compile_put_fact genv penv) facts body

let compile_event_facts (genv : env) (penv : process_env) (facts : Typed.fact list) (body : Pitptree.tprocess_e)
  : Pitptree.tprocess_e =
  List.fold_right (compile_event_fact genv penv) facts body

let eq_pterm (lhs : Pitptree.pterm_e) (rhs : Pitptree.pterm_e) : Pitptree.pterm_e =
  pterm (PPFunApp (pv_ident "=", [lhs; rhs]))

let rec compile_guard_tests
    (genv : env)
    (penv : process_env)
    (fresh : Typed.ident list)
    (facts : Typed.fact list)
    (then_proc : Pitptree.tprocess_e)
    (else_proc : Pitptree.tprocess_e)
  : Pitptree.tprocess_e =
  match facts with
  | [] -> then_proc
  | fact :: facts ->
      (match fact.desc with
       | Eq (lhs, rhs) ->
           let cond =
             eq_pterm
               (compile_expr_to_pterm genv penv lhs)
               (compile_expr_to_pterm genv penv rhs)
           in
           process
             (PTest
                ( cond
                , compile_guard_tests genv penv fresh facts then_proc else_proc
                , else_proc ))
       | Neq (lhs, rhs) ->
           let cond =
             eq_pterm
               (compile_expr_to_pterm genv penv lhs)
               (compile_expr_to_pterm genv penv rhs)
           in
           process
             (PTest
                ( cond
                , else_proc
                , compile_guard_tests genv penv fresh facts then_proc else_proc ))
       | Channel _ ->
           error ~loc:fact.loc
             (Unsupported "Nested channel guard lowering is not supported here")
       | File { path; contents } ->
           let path_term = compile_expr_to_pterm genv penv path in
           let file_channel =
             match penv.file_channel with
             | Some file_channel -> file_channel
             | None ->
                 error ~loc:fact.loc
                   (Internal_error "File guard requires a process-local file channel")
           in
           let payload_id = Ident.local "file_contents" in
           let payload_term = pterm (PPIdent (compile_ident payload_id)) in
           let payload_pattern =
             Pitptree.PPatTuple
               [ Pitptree.PPatEqual path_term
               ; Pitptree.PPatVar (compile_ident payload_id, Some bitstring_ident)
               ]
           in
           let branch_env, then_proc =
             match contents.desc with
             | Typed.Ident { id; _ } when List.mem id fresh ->
                 let branch_env = bind_process_var penv id payload_term in
                 branch_env, compile_guard_tests genv branch_env fresh facts then_proc else_proc
             | _ ->
                 let eq_then =
                   process
                     (PTest
                        ( eq_pterm payload_term (compile_expr_to_pterm genv penv contents)
                        , compile_guard_tests genv penv fresh facts then_proc else_proc
                        , else_proc ))
                 in
                 penv, eq_then
           in
           wrap_with_file_access_get ~loc:fact.loc path_term branch_env
             (process (PInput (file_channel, payload_pattern, then_proc, [precise_ident, None])))
             else_proc
       | Global ("In", [_arg]) ->
           let arg =
             match fact.desc with
             | Global ("In", [arg]) -> arg
             | _ -> assert false
           in
           let payload_id = Ident.local "attacker_input" in
           let payload_term = pterm (PPIdent (compile_ident payload_id)) in
           let then_proc =
             match arg.desc with
             | Typed.Ident { id; _ } when List.mem id fresh ->
                 let branch_env = bind_process_var penv id payload_term in
                 compile_guard_tests genv branch_env fresh facts then_proc else_proc
             | _ ->
                 let eq_then =
                   process
                      (PTest
                         ( eq_pterm payload_term (compile_expr_to_pterm genv penv arg)
                        , compile_guard_tests genv penv fresh facts then_proc else_proc
                        , else_proc ))
                 in
                 eq_then
           in
           process
             (PInput
                ( pterm (PPIdent attacker_channel_ident)
                , Pitptree.PPatVar (compile_ident payload_id, Some bitstring_ident)
                , then_proc
                , [] ))
       | Global _ | Plain _ ->
           error ~loc:fact.loc
             (Unsupported "Only equality/inequality/file guards are supported in ProVerif case lowering"))

let compile_pterm_eq_tests
    (tests : (Pitptree.pterm_e * Pitptree.pterm_e) list)
    (then_proc : Pitptree.tprocess_e)
    (else_proc : Pitptree.tprocess_e)
  : Pitptree.tprocess_e =
  List.fold_right
    (fun (lhs, rhs) acc ->
       process (PTest (eq_pterm lhs rhs, acc, else_proc)))
    tests
    then_proc

let extract_channel_guard (facts : Typed.fact list) =
  let rec go rev_prefix = function
    | [] -> None
    | (fact : Typed.fact) :: rest ->
        (match fact.desc with
         | Channel { channel; name; args } ->
             Some (channel, name, args, List.rev rev_prefix @ rest, fact.loc)
         | _ ->
             go (fact :: rev_prefix) rest)
  in
  go [] facts

let is_fresh_case_var (case : Typed.case) (id : Typed.ident) =
  List.mem id case.fresh

let rec compile_case_branch_body
    (genv : env)
    (penv : process_env)
    (case : Typed.case)
    (k : process_env -> Pitptree.tprocess_e)
  : Pitptree.tprocess_e =
  let saved =
    List.map (fun id -> id, find_process_var penv id) case.fresh
  in
  compile_cmd genv penv case.cmd
    (fun penv -> k (restore_process_vars penv saved))

and filter_map2
    (f : 'a -> 'b -> 'c option)
    (xs : 'a list)
    (ys : 'b list)
  : 'c list =
  match xs, ys with
  | [], [] -> []
  | x :: xs, y :: ys ->
      (match f x y with
       | Some z -> z :: filter_map2 f xs ys
       | None -> filter_map2 f xs ys)
  | _ -> invalid_arg "filter_map2"

and compile_case_no_channel
    (genv : env)
    (penv : process_env)
    (cases : Typed.case list)
    (k : process_env -> Pitptree.tprocess_e)
  : Pitptree.tprocess_e =
  let rec go = function
    | [] -> process PNil
    | case :: cases ->
        let else_proc = go cases in
        let then_proc = compile_case_branch_body genv penv case k in
        compile_guard_tests genv penv case.fresh case.facts then_proc else_proc
  in
  go cases

and compile_case_channelized
    (genv : env)
    (penv : process_env)
    (cases : Typed.case list)
    (k : process_env -> Pitptree.tprocess_e)
  : Pitptree.tprocess_e =
  (* Note: this is an optimized lowering for the common case where all channel
     guards in one [case] read the same fact name from the same channel. The
     full spec also discusses a more general lock-channel encoding for
     nondeterministic cases; if this optimization ever changes semantics on
     overlapping guards, we should fall back to that general form. *)
  let channel_guards =
    List.map
      (fun (case : Typed.case) ->
         match extract_channel_guard case.facts with
         | Some (channel, name, args, other_facts, loc) ->
             case, channel, name, args, other_facts, loc
         | None ->
             error ~loc:case.cmd.loc
               (Unsupported "Mixed channel/non-channel case branches are not supported yet"))
      cases
  in
  let first_channel, first_name, first_args, first_loc =
    match channel_guards with
    | (_, first_channel, first_name, first_args, _, first_loc) :: _ ->
        first_channel, first_name, first_args, first_loc
    | [] -> error ~loc:Location.nowhere (Internal_error "Empty channelized case is not supported")
  in
  let channel_key = Typed.string_of_expr first_channel in
  let arity = List.length first_args in
  List.iter
    (fun (_case, channel, name, args, _facts, loc) ->
       if Typed.string_of_expr channel <> channel_key then
         error ~loc (Invalid_input "All channel guards in one case must use the same channel");
       if name <> first_name then
         error ~loc (Invalid_input "All channel guards in one case must use the same fact name");
       if List.length args <> arity then
         error ~loc (Invalid_input "All channel guards in one case must use the same arity"))
    channel_guards;
  let payload_vars =
    List.init arity (fun i -> Ident.local (Printf.sprintf "case_arg_%d" i))
  in
  let payload_patterns =
    List.map (fun id -> Pitptree.PPatVar (compile_ident id, Some bitstring_ident)) payload_vars
  in
  let input_pattern = Pitptree.PPatFunApp (compile_name first_name, payload_patterns) in
  let payload_terms =
    List.map (fun id -> pterm (PPIdent (compile_ident id))) payload_vars
  in
  let rec branches = function
    | [] -> process PNil
    | (case, _channel, _name, args, facts, _loc) :: rest ->
        let branch_env =
          List.fold_left2
            (fun penv (arg : Typed.expr) payload_term ->
               match arg.desc with
               | Typed.Ident { id; _ } when is_fresh_case_var case id ->
                   bind_process_var penv id payload_term
               | _ -> penv)
            penv
            args
            payload_terms
        in
        let else_proc = branches rest in
        let then_proc = compile_case_branch_body genv branch_env case k in
        let arg_eq_tests =
          filter_map2
            (fun (arg : Typed.expr) payload_term ->
               match arg.desc with
               | Typed.Ident { id; _ } when is_fresh_case_var case id -> None
               | _ ->
                   Some (payload_term, compile_expr_to_pterm genv branch_env arg))
            args
            payload_terms
        in
        compile_guard_tests genv branch_env case.fresh facts
          (compile_pterm_eq_tests arg_eq_tests then_proc else_proc)
          else_proc
  in
  let channel_term = compile_channel_expr genv penv first_channel in
  wrap_with_channel_access_get ~loc:first_loc channel_term penv
    (process (PInput (channel_term, input_pattern, branches channel_guards, [])))
    (process PNil)

and compile_cmd (genv : env) (penv : process_env) (cmd : Typed.cmd) (k : process_env -> Pitptree.tprocess_e)
  : Pitptree.tprocess_e =
  match cmd.desc with
  | Skip -> k penv
  | Sequence (cmd1, cmd2) ->
      compile_cmd genv penv cmd1 (fun penv -> compile_cmd genv penv cmd2 k)
  | Put facts ->
      compile_put_facts genv penv facts (k penv)
  | Event facts ->
      compile_event_facts genv penv facts (k penv)
  | Let (id, expr, body) ->
      let value = compile_expr_to_pterm genv penv expr in
      let old_value = find_process_var penv id in
      compile_cmd genv (bind_process_var penv id value) body
        (fun penv -> k (restore_process_var penv id old_value))
  | Assign (Some id, expr) ->
      let value = compile_expr_to_pterm genv penv expr in
      k (bind_process_var penv id value)
  | Assign (None, expr) ->
      let _ = compile_expr_to_pterm genv penv expr in
      k penv
  | Return expr ->
      let _ = compile_expr_to_pterm genv penv expr in
      k penv
  | Case cases ->
      if List.exists (fun (case : Typed.case) -> Option.is_some (extract_channel_guard case.facts)) cases then
        compile_case_channelized genv penv cases k
      else
        compile_case_no_channel genv penv cases k
  | While (repeat_cases, until_cases) ->
      let state_ids =
        List.map fst (loop_state_bindings penv)
      in
      let parallelize = function
        | [] -> process PNil
        | proc :: procs ->
            List.fold_left
              (fun acc proc -> process (PPar (acc, proc)))
              proc
              procs
      in
      let lock_id = Ident.local "rabbit_loop_ch" in
      let lock_ident = compile_ident lock_id in
      let lock_term = pterm (PPIdent lock_ident) in
      let mk_branch_input_env () =
        let state_pattern_ids =
          List.mapi
            (fun index _id -> Ident.local (Printf.sprintf "loop_state_%d" index))
            state_ids
        in
        let branch_env = bind_loop_state penv state_ids state_pattern_ids in
        state_pattern_ids, branch_env
      in
      let repeat_branch (case : Typed.case) =
        let state_pattern_ids, branch_env = mk_branch_input_env () in
        let else_proc =
          process
            (POutput
               ( lock_term
               , loop_state_message ~done_flag:false ~loc:cmd.loc branch_env state_ids
               , process PNil ))
        in
        let then_proc =
          compile_case_branch_body genv branch_env case
            (fun final_env ->
               process
                 (POutput
                    ( lock_term
                    , loop_state_message ~done_flag:false ~loc:cmd.loc final_env state_ids
                    , process PNil )))
        in
        process
          (PInput
             ( lock_term
             , loop_state_pattern ~done_flag:false state_pattern_ids
             , compile_guard_tests genv branch_env case.fresh case.facts then_proc else_proc
             , [precise_ident, None] ))
      in
      let until_branch (case : Typed.case) =
        let state_pattern_ids, branch_env = mk_branch_input_env () in
        let else_proc =
          process
            (POutput
               ( lock_term
               , loop_state_message ~done_flag:false ~loc:cmd.loc branch_env state_ids
               , process PNil ))
        in
        let then_proc =
          compile_case_branch_body genv branch_env case
            (fun final_env ->
               process
                 (POutput
                    ( lock_term
                    , loop_state_message ~done_flag:true ~loc:cmd.loc final_env state_ids
                    , process PNil )))
        in
        process
          (PInput
             ( lock_term
             , loop_state_pattern ~done_flag:false state_pattern_ids
             , compile_guard_tests genv branch_env case.fresh case.facts then_proc else_proc
             , [precise_ident, None] ))
      in
      let cont_state_pattern_ids =
        List.mapi
          (fun index _id -> Ident.local (Printf.sprintf "loop_done_state_%d" index))
          state_ids
      in
      let cont_env = bind_loop_state penv state_ids cont_state_pattern_ids in
      let continuation =
        process
          (PInput
             ( lock_term
             , loop_state_pattern ~done_flag:true cont_state_pattern_ids
             , k cont_env
             , [precise_ident, None] ))
      in
      let workers =
        match List.map repeat_branch repeat_cases @ List.map until_branch until_cases with
        | [] -> process PNil
        | procs -> process (PRepl (parallelize procs))
      in
      let init_proc =
        process
          (POutput
             ( lock_term
             , loop_state_message ~done_flag:false ~loc:cmd.loc penv state_ids
             , process PNil ))
      in
      process
        (PRestr
           ( lock_ident
           , None
           , channel_ident
           , parallelize [init_proc; workers; continuation] ))
  | New (id, None, body) ->
      let fresh_ident = compile_ident id in
      let fresh_term = pterm (PPIdent fresh_ident) in
      let old_value = find_process_var penv id in
      process
        (PRestr
           ( fresh_ident
           , None
           , bitstring_ident
           , compile_cmd genv (bind_process_var penv id fresh_term) body
               (fun penv -> k (restore_process_var penv id old_value)) ))
  | New (id, Some (name, args), body) ->
      register_structure ~loc:cmd.loc genv name (List.length args);
      let fresh_ident = compile_ident id in
      let fresh_term = pterm (PPIdent fresh_ident) in
      let old_value = find_process_var penv id in
      let struct_term =
        pterm
          (PPFunApp
             ( structure_ctor_ident name
             , fresh_term :: List.map (compile_expr_to_pterm genv penv) args ))
      in
      process
        (PRestr
           ( fresh_ident
           , None
           , bitstring_ident
           , compile_cmd genv (bind_process_var penv id struct_term) body
               (fun penv -> k (restore_process_var penv id old_value)) ))
  | Get (ids, expr, name, body) ->
      register_structure ~loc:cmd.loc genv name (List.length ids);
      let struct_term = compile_expr_to_pterm genv penv expr in
      let addr_term = structure_addr_term name struct_term in
      let saved =
        List.map (fun id -> id, find_process_var penv id) ids
      in
      let body_env =
        List.mapi
          (fun index id -> id, structure_arg_term name (index + 1) struct_term)
          ids
        |> List.fold_left
             (fun penv (id, value) -> bind_process_var penv id value)
             penv
      in
      process
        (PGet
           ( deleted_address_table_ident
           , [Pitptree.PPatEqual addr_term]
           , None
           , process PNil
           , compile_cmd genv body_env body
               (fun penv -> k (restore_process_vars penv saved))
           , [] ))
  | Del (expr, name) ->
      let struct_term = compile_expr_to_pterm genv penv expr in
      let addr_term = structure_addr_term name struct_term in
      process (PInsert (deleted_address_table_ident, [addr_term], k penv))

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
    ~loc:(_loc : Location.t)
    (env : env)
    (process_typ : Typed.ident)
    (target_typs : Typed.ident list)
    (syscalls : Typed.ident list option)
  =
  let process_typ = compile_ident process_typ in
  let target_typs = List.map compile_ident target_typs in
  match syscalls with
  | None ->
      (* Note: [allow ... [.] ] is currently represented by granting access to
         the distinguished pseudo-syscall [none_syscall_s]. This is a pragmatic
         encoding choice for direct process operations, but it is worth
         re-checking against the final spec once syscall lowering is in place. *)
      List.iter
        (fun target_typ ->
           Queue.add (process_typ, target_typ, none_syscall_ident) env.allow_entries)
        target_typs;
      []
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

let compile_init ~loc:(_loc : Location.t) (env : env) (id : Typed.ident) (desc : Typed.init_desc) : Pitptree.tdecl list =
  let init_ident = compile_ident id in
  match desc with
  | Fresh ->
      (* Note: this assumes Rabbit top-level fresh constants are best modeled as
         private free names in ProVerif. If the intended semantics is closer to a
         definitional constant introduced by restriction at process start, this
         lowering should be revisited. *)
      [Pitptree.TFree (init_ident, bitstring_ident, [private_option])]
  | Value expr ->
      let init_term = term (PIdent init_ident) in
      let value_term = compile_expr_to_term env expr in
      (* Note: this currently lowers [const n = e] as a private constant together
         with an equation [n = e]. This is a plausible first encoding, but it is
         worth re-checking whether ProVerif prefers this over a pure equational
         alias or some other definitional form, especially if [e] itself contains
         non-trivial function symbols. *)
      [ Pitptree.TConstDecl (init_ident, bitstring_ident, [private_option])
      ; TEquation
          ( [ [], EETerm (term (PFunApp (pv_ident "=", [init_term; value_term]))) ]
          , [] )
      ]
  | Value_with_param (param, expr) ->
      let param_ident = compile_ident param in
      let init_term =
        term (PFunApp (init_ident, [term (PIdent param_ident)]))
      in
      let value_term = compile_expr_to_term env expr in
      [ TReduc
          ( [ [param_ident, param_data_ident]
            , EETerm (term (PFunApp (pv_ident "=", [init_term; value_term])))
            ]
          , [] )
      ]
  | Fresh_with_param ->
      [Pitptree.TFunDecl (init_ident, [param_data_ident], bitstring_ident, [private_option])]

let compile_channel
    ~loc
    (id : Typed.ident)
    (param : unit option)
    (_typ : Typed.ident)
  =
  match param with
  | Some () ->
      error ~loc (Unsupported "Parameterized channel declarations are not supported yet")
  | None ->
      Pitptree.TFree (compile_ident id, channel_ident, [pv_ident "private", None])

let process_file_channel_ident : Pitptree.ident = pv_ident "rabbit__file_ch"

let wrap_with_channel_init
    ~loc
    (args : Typed.chan_param list)
    (body : Pitptree.tprocess_e)
  : Pitptree.tprocess_e =
  List.fold_right
    (fun ({ channel; param; typ } : Typed.chan_param) acc ->
       match param with
       | Some () ->
           error ~loc
             (Unsupported "Parameterized process channel arguments are not supported yet")
       | None ->
           process
             (PInsert
                ( channel_table_ident
                , [ pterm (PPIdent (compile_ident typ))
                  ; pterm (PPIdent (compile_ident channel))
                  ]
                , acc )))
    args
    body

let wrap_with_file_init
    ~loc
    (genv : env)
    (penv : process_env)
    (files : (Typed.expr * Typed.ident * Typed.expr) list)
    (body : Pitptree.tprocess_e)
  : Pitptree.tprocess_e =
  match penv.file_channel with
  | None ->
      if files = [] then
        body
      else
        error ~loc
          (Internal_error "Internal file channel is not available for process file setup")
  | Some file_channel ->
      let output_processes =
        List.map
          (fun ((path, _typ, contents) : Typed.expr * Typed.ident * Typed.expr) ->
             let payload =
               pterm
                 (PPTuple
                    [ compile_expr_to_pterm genv penv path
                    ; compile_expr_to_pterm genv penv contents
                    ])
             in
             process (POutput (file_channel, payload, process PNil)))
          files
      in
      let parallel_body =
        match output_processes with
        | [] -> body
        | proc :: procs ->
            List.fold_left
              (fun acc proc -> process (PPar (acc, proc)))
              proc
              (body :: procs)
      in
      let with_channel =
        process (PRestr (process_file_channel_ident, None, channel_ident, parallel_body))
      in
      List.fold_right
        (fun ((path, typ, _contents) : Typed.expr * Typed.ident * Typed.expr) acc ->
           process
             (PInsert
                ( file_type_table_ident
                , [ pterm (PPIdent ptype_arg_ident)
                  ; pterm (PPIdent (compile_ident typ))
                  ; compile_expr_to_pterm genv penv path
                  ]
                , acc )))
        files
        with_channel

let compile_process
    (genv : env)
    ~loc
    (id : Typed.ident)
    (param : Typed.ident option)
    (args : Typed.chan_param list)
    (_typ : Typed.ident)
    (files : (Typed.expr * Typed.ident * Typed.expr) list)
    (vars : (Typed.ident * Typed.expr) list)
    (funcs : (Typed.ident * Typed.ident list * Typed.cmd) list)
    (main : Typed.cmd)
  : Pitptree.tdecl =
  match param with
  | Some _ ->
      error ~loc (Unsupported "Parameterized process declarations are not supported yet")
  | None ->
      if funcs <> [] then
        error ~loc (Unsupported "Process-local function declarations are not supported yet");
      let proc_args =
        (ptype_arg_ident, proc_t_ident, false)
        ::
        List.map
          (fun ({ channel; param; _ } : Typed.chan_param) ->
             match param with
             | Some () ->
                 error ~loc (Unsupported "Parameterized process channel arguments are not supported yet")
             | None -> compile_ident channel, channel_ident, false)
          args
      in
      let base_penv =
        if files = [] then
          create_process_env
            ~proc_type:(pterm (PPIdent ptype_arg_ident))
            ~curr_syscall:(Some (pterm (PPIdent none_syscall_ident)))
            ~file_channel:None
        else
          create_process_env
            ~proc_type:(pterm (PPIdent ptype_arg_ident))
            ~curr_syscall:(Some (pterm (PPIdent none_syscall_ident)))
            ~file_channel:(Some (pterm (PPIdent process_file_channel_ident)))
      in
      let rec init_vars penv = function
        | [] ->
            wrap_with_channel_init ~loc args
              (wrap_with_file_init ~loc genv penv files
                 (compile_cmd genv penv main (fun _ -> process PNil)))
        | (var, expr) :: vars ->
            let value = compile_expr_to_pterm genv penv expr in
            init_vars (bind_process_var penv var value) vars
      in
      Pitptree.TPDef (compile_ident id, proc_args, init_vars base_penv vars)

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
  match env.top_process with
  | None ->
      env.top_process <- Some top_process;
      []
  | Some _ ->
      error ~loc (Unsupported "Multiple system declarations are not supported yet")

let compile_prelude (_env : env) : Pitptree.tdecl list =
  [ TTypeDecl param_data_ident
  ; TTypeDecl proc_t_ident
  ; TTypeDecl acc_data_t_ident
  ; TTypeDecl syscall_t_ident
  ; TFree (attacker_channel_ident, channel_ident, [])
  ; TTableDecl
      (access_control_table_ident, [proc_t_ident; acc_data_t_ident; syscall_t_ident])
  ; TTableDecl
      (file_type_table_ident, [proc_t_ident; acc_data_t_ident; bitstring_ident])
  ; TTableDecl (channel_table_ident, [acc_data_t_ident; channel_ident])
  ; TTableDecl (deleted_address_table_ident, [bitstring_ident])
  ; TConstDecl (none_syscall_ident, syscall_t_ident, [])
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

let compile_generated_event_decls (env : env) : Pitptree.tdecl list =
  Hashtbl.to_seq env.event_table
  |> List.of_seq
  |> List.sort_uniq compare
  |> List.map (fun (name, arity) ->
      Pitptree.TEventDecl (compile_name name, List.init arity (fun _ -> bitstring_ident)))

let compile_generated_structure_decls (env : env) : Pitptree.tdecl list =
  (* Note: structure constructors/getters are generated globally from observed
     Rabbit structure usages. This assumes there is no conflicting user-level
     ProVerif declaration with the same generated names and that a per-name
     arity discipline is enough. If the surrounding language grows richer
     namespaces or imported declarations, this generation scheme may need to be
     made more explicit. *)
  let mk_var index = pv_ident (Printf.sprintf "x_%d" index) in
  Hashtbl.to_seq env.structure_table
  |> List.of_seq
  |> List.sort_uniq compare
  |> List.concat_map
       (fun (name, arity) ->
          let envdecl =
            List.init (arity + 1) (fun index -> mk_var index, bitstring_ident)
          in
          let vars =
            List.map (fun (id, _ty) -> term (PIdent id)) envdecl
          in
          let struct_term =
            term (PFunApp (structure_ctor_ident name, vars))
          in
          let ctor_decl =
            Pitptree.TFunDecl
              ( structure_ctor_ident name
              , List.init (arity + 1) (fun _ -> bitstring_ident)
              , bitstring_ident
              , [pv_ident "data", None] )
          in
          let addr_decl =
            Pitptree.TReduc
              ( [ envdecl
                , Pitptree.EETerm
                    (term
                       (PFunApp
                          ( pv_ident "="
                          , [ term (PFunApp (structure_addr_ident name, [struct_term]))
                            ; List.nth vars 0
                            ] )))
                ]
              , [] )
          in
          let arg_decls =
            List.init arity
              (fun index ->
                 Pitptree.TReduc
                   ( [ envdecl
                     , Pitptree.EETerm
                         (term
                            (PFunApp
                               ( pv_ident "="
                               , [ term (PFunApp (structure_arg_ident name (index + 1), [struct_term]))
                                 ; List.nth vars (index + 1)
                                 ] )))
                     ]
                   , [] ))
          in
          ctor_decl :: addr_decl :: arg_decls)

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

let rec collect_process_types (env : env) (decls : Typed.decl list) =
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
  | Function { id; arity } ->
      [compile_function ~loc:decl.loc id arity]
  | Equation (lhs, rhs) ->
      [compile_equation ~loc:decl.loc env lhs rhs]
  | Syscall { id; args; cmd; attack } ->
      [compile_syscall ~loc:decl.loc id args cmd attack]
  | Attack { id; syscall; args; cmd } ->
      [compile_attack ~loc:decl.loc id syscall args cmd]
  | Type { id; typclass } ->
      [compile_type ~loc:decl.loc id typclass]
  | Allow { process_typ; target_typs; syscalls } ->
      compile_allow ~loc:decl.loc env process_typ target_typs syscalls
  | AllowAttack { process_typs; attacks } ->
      [compile_allow_attack ~loc:decl.loc process_typs attacks]
  | Init { id; desc } ->
      compile_init ~loc:decl.loc env id desc
  | Channel { id; param; typ } ->
      [compile_channel ~loc:decl.loc id param typ]
  | Process { id; param; args; typ; files; vars; funcs; main } ->
      [compile_process env ~loc:decl.loc id param args typ files vars funcs main]
  | System (procs, lemmas) -> compile_system ~loc:decl.loc env procs lemmas
  | Load (filename, decls) -> compile_load env filename decls

let compile_program (decls : Typed.decl list) =
  let env = create_env () in
  collect_process_types env decls;
  let body = List.concat_map (compile_decl env) decls in
  let top_process =
    match env.top_process with
    | Some top_process -> wrap_with_allow_init env top_process
    | None -> wrap_with_allow_init env (process PNil)
  in
  ( compile_prelude env
    @ compile_generated_structure_decls env
    @ compile_generated_syscall_consts env
    @ compile_generated_event_decls env
    @ compile_generated_string_consts env
    @ body
  , top_process
  , None )
