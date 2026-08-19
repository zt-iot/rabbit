open Rabbit_proverif_pv_parse
open Pitptree
include Proverif_compiler_env

let check_param_cycle expanding id loc =
  if List.mem id expanding then
    Error.invalid_input ~loc
      "Cyclic parameterized constant definition involving %s"
      (Ident.to_string id)

let rec compile_expr_to_term_with genv bindings expanding (expr : T.expr) : term_e =
  let compile = compile_expr_to_term_with genv bindings expanding in
  let compile_parameter (parameter : T.expr) =
    match parameter.desc with
    | Ident { id; param = None; _ } ->
        Option.value
          (List.assoc_opt id bindings)
          ~default:(term_e @@ PIdent (GEnv.fresh_parameter_ident genv parameter))
    | _ -> term_e @@ PIdent (GEnv.fresh_parameter_ident genv parameter)
  in
  term_e @@ match expr.desc with
  | T.Ident { id; param = Some param; _ } ->
      let parameter = compile_parameter param in
      (match GEnv.find_param_init genv id with
       | None -> PFunApp (compile_ident id, [parameter])
       | Some (formal, body) ->
           check_param_cycle expanding id expr.loc;
           let body, _, _ =
             compile_expr_to_term_with genv
               ((formal, parameter) :: bindings) (id :: expanding) body
           in
           body)
  | T.Ident { id; _ } ->
      (match List.assoc_opt id bindings with
       | Some (term, _, _) -> term
       | None -> PIdent (compile_ident id))
  | Apply (id, args) -> PFunApp (compile_ident id, List.map compile args)
  | Tuple exprs -> PTuple (List.map compile exprs)
  | Unit -> PTuple []
  | String s -> PIdent (GEnv.fresh_string_ident genv s)
  | Boolean true -> PIdent true_ident
  | Boolean false -> PIdent false_ident
  | Integer n -> PIdent (GEnv.fresh_integer_ident genv n)
  | Float _ ->
      Error.unsupported ~loc:expr.loc
        "Float terms are not supported in ProVerif term translation"

let compile_expr_to_term genv expr =
  compile_expr_to_term_with genv [] [] expr

let rec compile_expr_to_gterm_with genv bindings expanding (expr : T.expr) : gterm_e =
  let compile = compile_expr_to_gterm_with genv bindings expanding in
  let compile_parameter (parameter : T.expr) =
    match parameter.desc with
    | Ident { id; param = None; _ } ->
        Option.value
          (List.assoc_opt id bindings)
          ~default:(gterm_e @@ PGIdent (GEnv.fresh_parameter_ident genv parameter))
    | _ -> gterm_e @@ PGIdent (GEnv.fresh_parameter_ident genv parameter)
  in
  gterm_e @@ match expr.desc with
  | T.Ident { id; param = Some param; _ } ->
      let parameter = compile_parameter param in
      (match GEnv.find_param_init genv id with
       | None -> PGFunApp (compile_ident id, [parameter], None)
       | Some (formal, body) ->
           check_param_cycle expanding id expr.loc;
           let body, _, _ =
             compile_expr_to_gterm_with genv
               ((formal, parameter) :: bindings) (id :: expanding) body
           in
           body)
  | Ident { id; param = None; _ } ->
      (match List.assoc_opt id bindings with
       | Some (term, _, _) -> term
       | None -> PGIdent (compile_ident id))
  | Apply (id, args) -> PGFunApp (compile_ident id, List.map compile args, None)
  | Tuple exprs -> PGTuple (List.map compile exprs)
  | Unit -> PGTuple []
  | String s -> PGIdent (GEnv.fresh_string_ident genv s)
  | Boolean true -> PGIdent true_ident
  | Boolean false -> PGIdent false_ident
  | Integer n -> PGIdent (GEnv.fresh_integer_ident genv n)
  | Float _ ->
      Error.unsupported ~loc:expr.loc
        "Float terms are not supported in ProVerif query translation"

let compile_expr_to_gterm genv expr =
  compile_expr_to_gterm_with genv [] [] expr

let rec compile_expr_to_pterm_with genv penv bindings expanding (expr : T.expr) : pterm_e =
  let compile = compile_expr_to_pterm_with genv penv bindings expanding in
  let compile_parameter (parameter : T.expr) =
    match parameter.desc with
    | Ident { id; param = None; _ } ->
        Option.value
          (List.assoc_opt id bindings)
          ~default:(pterm_e @@ PPIdent (GEnv.fresh_parameter_ident genv parameter))
    | _ -> pterm_e @@ PPIdent (GEnv.fresh_parameter_ident genv parameter)
  in
  pterm_e @@ match expr.desc with
  | T.Ident { id; param = Some param; _ } ->
      let parameter = compile_parameter param in
      (match GEnv.find_param_init genv id with
       | None -> PPFunApp (compile_ident id, [parameter])
       | Some (formal, body) ->
           check_param_cycle expanding id expr.loc;
           let body, _, _ =
             compile_expr_to_pterm_with genv penv
               ((formal, parameter) :: bindings) (id :: expanding) body
           in
           body)
  | Ident { id; param = None; _ } ->
      (match List.assoc_opt id bindings with
       | Some (term, _, _) -> term
       | None ->
           match PEnv.find_process_var penv id with
           | Some value ->
               let term, _, _ = value in
               term
           | None -> PPIdent (compile_ident id))
  | Apply (id, args) -> PPFunApp (compile_ident id, List.map compile args)
  | Tuple exprs -> PPTuple (List.map compile exprs)
  | Unit -> PPTuple []
  | String s -> PPIdent (GEnv.fresh_string_ident genv s)
  | Boolean true -> PPIdent true_ident
  | Boolean false -> PPIdent false_ident
  | Integer n -> PPIdent (GEnv.fresh_integer_ident genv n)
  | Float _ ->
      Error.unsupported ~loc:expr.loc
        "Float process terms are not supported in ProVerif process translation"

let compile_expr_to_pterm genv penv expr =
  compile_expr_to_pterm_with genv penv [] [] expr

let ppar
    (proc1 : tprocess_e)
    (proc2 : tprocess_e)
  : tprocess_e =
  process_e @@ PPar (proc1, proc2)

let parallelize = function
  | [] -> process_e PNil
  | proc :: procs -> List.fold_left ppar proc procs

(*
   3.9 Syscall and Attack Encoding

   A single token is sent on a private channel. Each branch races to receive
   that token, so exactly one branch can proceed.
*)
let nondet_choose_processes
    (branches : tprocess_e list)
  : tprocess_e =
  match branches with
  | [] -> process_e @@ PNil
  | [branch] -> branch
  | _ ->
      let choice_id = pv_ident "attack_choice_ch" in
      let choice_term = pterm_e @@ PPIdent choice_id in
      let token = pterm_e @@ PPIdent true_ident in
      let pick_one =
        List.map
          (fun branch ->
             process_e @@
               PInput
                  ( choice_term
                  , PPatAny (Parsing_helper.dummy_ext, Some bitstring_ident)
                  , branch
                  , [] ))
          branches
      in
      let body =
        List.fold_left
          (fun acc branch -> process_e @@ PPar (acc, branch))
          (process_e @@ POutput (choice_term, token, process_e @@ PNil))
          pick_one
      in
      process_e @@ PRestr (choice_id, None, channel_ident, body)

let wrap_with_access_control_get
    (penv : PEnv.t)
    (target_type : pterm_e)
    (then_proc : tprocess_e)
    (else_proc : tprocess_e)
  : tprocess_e =
  (* No spec for allow ... [.] *)
  (* Note: this assumes direct Rabbit accesses are mediated solely by the
     triple (current process type, target access-data type, current syscall).
     The current lowering uses [none__syscall] for direct process code via
     [allow ... [.]]. If the spec ends up distinguishing more direct-access
     contexts, this table lookup may need refinement. *)
  process_e @@
  PGet
    ( access_control_table_ident
    , [ PPatEqual (PEnv.proc_type penv)
      ; PPatEqual target_type
      ; PPatEqual (PEnv.curr_syscall penv)
      ]
    , None
    , then_proc
    , else_proc
    , [] )

let wrap_with_channel_access_get
    (channel_term : pterm_e)
    penv
    (then_proc : tprocess_e)
    (else_proc : tprocess_e)
  : tprocess_e =
  (*
     3.8 Channel facts Encoding

     ```
     case [ ch :: msg(x) ] -> c end
     ```

     ```
     get channel_table(ch_type:acc_data_t, =ch) in
     get access_control_table(=ptype, =ch_type, =curr_syscall) in
     ...
     ```
  *)
  let channel_type_id = Ident.local "ch_type" in
  let channel_type_term = pterm_e @@ PPIdent (compile_ident channel_type_id) in
  process_e @@
  PGet
    ( channel_table_ident
    , [ PPatVar (compile_ident channel_type_id, Some acc_data_t_ident)
      ; PPatEqual channel_term
      ]
    , None
    , wrap_with_access_control_get penv channel_type_term then_proc else_proc
    , else_proc
    , [] )

let wrap_with_file_access_get
    (path_term : pterm_e)
    (penv : PEnv.t)
    (then_proc : tprocess_e)
    (else_proc : tprocess_e)
  : tprocess_e =
  (*
     3.7 File Fact Encoding

     ```
     case [ p.x ] -> c end
     ```

     ```
     get file_type_table(=ptype, ftype:acc_data_t, =p) in
     get access_control_table(=ptype, =ftype, =curr_syscall) in
     ...
     ```
  *)
  let file_type_id = Ident.local "file_type" in
  let file_type_term = pterm_e @@ PPIdent (compile_ident file_type_id) in
  process_e @@
  PGet
    ( file_type_table_ident
    , [ PPatEqual (PEnv.proc_type penv)
      ; PPatVar (compile_ident file_type_id, Some acc_data_t_ident)
      ; PPatEqual path_term
      ]
    , None
    , wrap_with_access_control_get penv file_type_term then_proc else_proc
    , else_proc
    , [] )

let structure_addr_term (name : T.name) (struct_term : pterm_e) : pterm_e =
  pterm_e @@ PPFunApp (structure_addr_ident name, [struct_term])

let structure_arg_term (name : T.name) (index : int) (struct_term : pterm_e) : pterm_e =
  pterm_e @@ PPFunApp (structure_arg_ident name index, [struct_term])

let lock_state_bindings (penv : PEnv.t) : (T.ident * pterm_e) list =
  (* Conservatively carry every current process binding across case and loop
     lock boundaries. This is simple and sounder than forgetting mutable state,
     but it may be larger than necessary. A later refinement could compute the
     true live subset. *)
  List.rev (PEnv.bindings penv)

let lock_state_message
    ~done_flag
    ~loc
    penv
    (state_ids : T.ident list)
  : pterm_e =
  let flag_term =
    pterm_e @@ PPIdent (if done_flag then true_ident else false_ident)
  in
  match state_ids with
  | [] -> flag_term
  | _ ->
      pterm_e @@
      PPTuple
        (flag_term
         :: List.map (PEnv.find_process_var_exn ~loc penv) state_ids)

let lock_state_pattern
    ~done_flag
    (state_pattern_ids : T.ident list)
  : tpattern =
  let flag_pattern =
    PPatEqual
      (pterm_e @@ PPIdent (if done_flag then true_ident else false_ident))
  in
  match state_pattern_ids with
  | [] -> flag_pattern
  | _ ->
      PPatTuple
        (flag_pattern
         :: List.map
              (fun id -> PPatVar (compile_ident id, Some bitstring_ident))
              state_pattern_ids)

let bind_lock_state
    penv
    (state_ids : T.ident list)
    (state_pattern_ids : T.ident list)
  : PEnv.t =
  List.fold_left2
    (fun penv state_id pattern_id ->
       PEnv.bind_process_var penv state_id (pterm_e @@ PPIdent (compile_ident pattern_id)))
    penv
    state_ids
    state_pattern_ids

let compile_event_fact genv penv (fact : T.fact) (body : tprocess_e)
  : tprocess_e =
  (*
     3.1 Encoding Strings, Constants, Events and Function Declarations

     ```
     event [:: ImgSend(image)]
     ```

     ```
     event ImgSend(bitstring).
     ...
     event ImgSend(image);
     ```
  *)
  let loc = fact.loc in
  match fact.desc with
  | Global (name, args) ->
      GEnv.add_event ~loc genv name Global (List.length args);
      process_e @@
      PEvent
        ( compile_event_name name Global
        , List.map (compile_expr_to_pterm genv penv) args
        , None
        , body )
  | Plain (name, args) ->
      GEnv.add_event ~loc genv name Plain (List.length args);
      process_e
      @@ PEvent
        ( compile_event_name name Plain
        , List.map (compile_expr_to_pterm genv penv) args
        , None
        , body )
  | _ ->
      Error.unsupported ~loc
        "Only plain/global event facts are supported in ProVerif event lowering"

let compile_put_fact genv penv (fact : T.fact) (body : tprocess_e)
  : tprocess_e =
  (*
     3.7 File Fact Encoding
     3.8 Channel facts Encoding
     3.9 Syscall and Attack Encoding

     ```
     put [ ch :: msg(v) ]
     put [ p.x ]
     put [ ::Out(v) ]
     ```

     ```
     out(ch, msg(v)) |
     ...
     out(file_ch, (p, x)) |
     ...
     out(attacker, v)
     ```
  *)
  let loc = fact.loc in
  match fact.desc with
  | Channel { channel; name; args } ->
      GEnv.add_channel_fact ~loc genv name (List.length args);
      let channel_term = compile_expr_to_pterm genv penv channel in
      let payload =
        pterm_e @@
        PPFunApp
          ( compile_name name "chan"
          , List.map (compile_expr_to_pterm genv penv) args )
      in
      wrap_with_channel_access_get channel_term penv
        (ppar (process_e @@ POutput (channel_term, payload, process_e PNil)) body)
        (process_e PNil)
  | File { path; contents } ->
      let path_term = compile_expr_to_pterm genv penv path in
      let contents_term = compile_expr_to_pterm genv penv contents in
      let file_channel =
        match PEnv.file_channel penv with
        | Some file_channel -> file_channel
        | None ->
            Error.internal ~loc
              "File output requires a process-local file channel"
      in
      let payload = pterm_e @@ PPTuple [path_term; contents_term] in
      wrap_with_file_access_get path_term penv
        (ppar (process_e @@ POutput (file_channel, payload, process_e PNil)) body)
        (process_e PNil)
  | Global ("Out", [arg]) ->
      process_e @@ POutput (pterm_e @@ PPIdent attacker_channel_ident, compile_expr_to_pterm genv penv arg, body)
  | Global _ ->
      Error.unsupported ~loc
        "Global facts other than ::Out(...) are not supported in ProVerif put lowering"
  | _ ->
      Error.unsupported ~loc
        "Only channel/global output facts are supported in ProVerif put lowering"

let compile_put_facts genv penv (facts : T.fact list) (body : tprocess_e)
  : tprocess_e =
  List.fold_right (compile_put_fact genv penv) facts body

let compile_event_facts genv penv (facts : T.fact list) (body : tprocess_e)
  : tprocess_e =
  List.fold_right (compile_event_fact genv penv) facts body

let eq_pterm (lhs : pterm_e) (rhs : pterm_e) : pterm_e =
  pterm_e @@ PPFunApp (pv_ident "=", [lhs; rhs])

let rec compile_guard_tests
    genv
    penv
    (fresh : T.ident list)
    (facts : T.fact list)
    (then_proc : PEnv.t -> tprocess_e)
    (else_proc : tprocess_e)
  : tprocess_e =
  (*
     3.5 Case Encoding

     ```
     case [x = y, p.z, ::In(v)] -> c end
     ```

     ```
     if x = y then
       get file_type_table(...) in
       get access_control_table(...) in
       in(file_ch, (=p, z:bitstring)) [precise];
       in(attacker, v:bitstring);
       c
     else
       ...
     ```
  *)
  match facts with
  | [] -> then_proc penv
  | fact :: facts ->
      (match fact.desc with
       | Eq (lhs, rhs) ->
           let cond =
             eq_pterm
               (compile_expr_to_pterm genv penv lhs)
               (compile_expr_to_pterm genv penv rhs)
           in
           process_e @@
           PTest
             ( cond
             , compile_guard_tests genv penv fresh facts then_proc else_proc
             , else_proc )
       | Neq (lhs, rhs) ->
           let cond =
             eq_pterm
               (compile_expr_to_pterm genv penv lhs)
               (compile_expr_to_pterm genv penv rhs)
           in
           process_e @@
           PTest
             ( cond
             , else_proc
             , compile_guard_tests genv penv fresh facts then_proc else_proc )
       | Channel _ ->
           Error.unsupported ~loc:fact.loc
             "Nested channel guard lowering is not supported here"
       | File { path; contents } ->
           let path_term = compile_expr_to_pterm genv penv path in
           let file_channel =
             match PEnv.file_channel penv with
             | Some file_channel -> file_channel
             | None ->
                 Error.internal ~loc:fact.loc
                   "File guard requires a process-local file channel"
           in
           let payload_id = Ident.local "file_contents" in
           let payload_term = pterm_e @@ PPIdent (compile_ident payload_id) in
           let payload_pattern =
             PPatTuple
               [ PPatEqual path_term
               ; PPatVar (compile_ident payload_id, Some bitstring_ident)
               ]
           in
           let branch_env, then_proc =
             match contents.desc with
             | T.Ident { id; _ } when List.mem id fresh ->
                 let branch_env = PEnv.bind_process_var penv id payload_term in
                 branch_env, compile_guard_tests genv branch_env fresh facts then_proc else_proc
             | _ ->
                 let eq_then =
                   process_e @@
                   PTest
                     ( eq_pterm payload_term (compile_expr_to_pterm genv penv contents)
                     , compile_guard_tests genv penv fresh facts then_proc else_proc
                     , else_proc )
                 in
                 penv, eq_then
           in
           wrap_with_file_access_get path_term branch_env
             (process_e @@ PInput (file_channel, payload_pattern, then_proc, [precise_ident, None]))
             else_proc
       | Global ("In", [_arg]) ->
           let arg =
             match fact.desc with
             | Global ("In", [arg]) -> arg
             | _ -> assert false
           in
           let payload_id = Ident.local "attacker_input" in
           let payload_term = pterm_e @@ PPIdent (compile_ident payload_id) in
           let then_proc =
             match arg.desc with
             | T.Ident { id; _ } when List.mem id fresh ->
                 let branch_env = PEnv.bind_process_var penv id payload_term in
                 compile_guard_tests genv branch_env fresh facts then_proc else_proc
             | _ ->
                 let eq_then =
                   process_e @@
                   PTest
                     ( eq_pterm payload_term (compile_expr_to_pterm genv penv arg)
                     , compile_guard_tests genv penv fresh facts then_proc else_proc
                     , else_proc )
                 in
                 eq_then
           in
           process_e @@
           PInput
             ( pterm_e @@ PPIdent attacker_channel_ident
             , PPatVar (compile_ident payload_id, Some bitstring_ident)
             , then_proc
             , [] )
       | Global ("False", []) ->
           else_proc
       | Global ("True", []) ->
           compile_guard_tests genv penv fresh facts then_proc else_proc
       | Global _ | Plain _ ->
           Error.unsupported ~loc:fact.loc
             "Only equality/inequality/file guards are supported in ProVerif case lowering")

let compile_pterm_eq_tests
    (tests : (pterm_e * pterm_e) list)
    (then_proc : tprocess_e)
    (else_proc : tprocess_e)
  : tprocess_e =
  List.fold_right
    (fun (lhs, rhs) acc ->
       process_e @@ PTest (eq_pterm lhs rhs, acc, else_proc))
    tests
    then_proc

let extract_channel_guard (facts : T.fact list) =
  let rec go rev_prefix = function
    | [] -> None
    | (fact : T.fact) :: rest ->
        (match fact.desc with
         | Channel { channel; name; args } ->
             Some (channel, name, args, List.rev rev_prefix @ rest, fact.loc)
         | _ ->
             go (fact :: rev_prefix) rest)
  in
  go [] facts

let is_fresh_case_var (case : T.case) (id : T.ident) =
  List.mem id case.fresh

type kont =
  | KStop
  | KProc of tprocess_e
  | KSeq of T.cmd * kont
  | KRestoreVars of (T.ident * pterm_e option) list * kont
  | KLockOutput of bool * Location.t * pterm_e * T.ident list

let rec filter_map2
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

let rec compile_channel_guard_case
    genv
    penv
    (case : T.case)
    (kont : kont)
    (channel : T.expr)
    (name : T.name)
    (args : T.expr list)
    (other_facts : T.fact list)
    ~(else_proc : tprocess_e)
  : tprocess_e =
  GEnv.add_channel_fact ~loc:case.cmd.loc genv name (List.length args);
  let payload_vars =
    List.init (List.length args) (fun i -> Ident.local (Printf.sprintf "case_arg_%d" i))
  in
  let payload_patterns =
    (* BUG: Rabbit consumes a channel fact only when the complete case guard
       matches. Binding every payload here and checking non-fresh arguments and
       the other facts after [in] can consume a message even when the case guard
       ultimately fails. Non-fresh arguments should at least use exact input
       patterns; preserving atomicity with the remaining facts requires a more
       general fix. *)
    List.map
      (fun id -> PPatVar (compile_ident id, Some bitstring_ident))
      payload_vars
  in
  let input_pattern = PPatFunApp (compile_name name "chan", payload_patterns) in
  let payload_terms =
    List.map (fun id -> pterm_e @@ PPIdent (compile_ident id)) payload_vars
  in
  let branch_env =
    List.fold_left2
      (fun penv (arg : T.expr) payload_term ->
         match arg.desc with
         | T.Ident { id; _ } when is_fresh_case_var case id ->
             PEnv.bind_process_var penv id payload_term
         | _ -> penv)
      penv
      args
      payload_terms
  in
  let arg_eq_tests =
    let rec collect acc args payload_terms =
      match args, payload_terms with
      | [], [] -> List.rev acc
      | (arg : T.expr) :: args, payload_term :: payload_terms ->
          (match arg.desc with
           | T.Ident { id; _ } when is_fresh_case_var case id ->
               collect acc args payload_terms
           | _ ->
               collect
                 ((payload_term, compile_expr_to_pterm genv branch_env arg) :: acc)
                 args
                 payload_terms)
      | _ -> invalid_arg "compile_channel_guard_case"
    in
    collect [] args payload_terms
  in
  let channel_term = compile_expr_to_pterm genv penv channel in
  wrap_with_channel_access_get channel_term penv
    (process_e @@
     PInput
       ( channel_term
       , input_pattern
       , compile_guard_tests genv branch_env case.fresh other_facts
           (fun final_env ->
              compile_pterm_eq_tests arg_eq_tests
                (compile_case_branch_body genv final_env case kont)
                else_proc)
           else_proc
       , [] ))
    else_proc

and compile_case_branch_body
    genv
    penv
    (case : T.case)
    (kont : kont)
  : tprocess_e =
  let saved =
    List.map (fun id -> id, PEnv.find_process_var penv id) case.fresh
  in
  compile_cmd genv penv (KRestoreVars (saved, kont)) case.cmd

and compile_case_no_channel
    genv
    penv
  (cases : T.case list)
  (kont : kont)
  : tprocess_e =
  (*
     3.5 Case Encoding

     ```
     case [A1] -> c1 | [A2] -> c2 end
     ```

     ```
     new lock_ch: channel;
     out(lock_ch, (false, s0, ..., sk))
     | (in(lock_ch, (=false, s0, ..., sk));
        if A1 then c1; out(lock_ch, (true, s0', ..., sk'))
        else out(lock_ch, (false, s0, ..., sk)))
     | (in(lock_ch, (=false, s0, ..., sk));
        if A2 then c2; out(lock_ch, (true, s0', ..., sk'))
        else out(lock_ch, (false, s0, ..., sk)))
     | (in(lock_ch, (=true, s0, ..., sk)); rest_of_program)
     ```
  *)
  match cases with
  | [] -> process_e PNil
  | [case] ->
      compile_guard_tests genv penv case.fresh case.facts
        (fun final_env -> compile_case_branch_body genv final_env case kont)
        (process_e PNil)
  | _ ->
      let loc = (List.hd cases).cmd.loc in
      let state_ids = List.map fst (lock_state_bindings penv) in
      let lock_id = Ident.local "case_ch" in
      let lock_ident = compile_ident lock_id in
      let lock_term = pterm_e @@ PPIdent lock_ident in
      let compile_branch (case : T.case) =
        let state_pattern_ids =
          List.mapi
            (fun index _id -> Ident.local (Printf.sprintf "case_state_%d" index))
            state_ids
        in
        let branch_env = bind_lock_state penv state_ids state_pattern_ids in
        let retry =
          process_e @@
          POutput
            ( lock_term
            , lock_state_message ~done_flag:false ~loc branch_env state_ids
            , process_e PNil )
        in
        let guard_proc =
          compile_guard_tests genv branch_env case.fresh case.facts
            (fun final_env ->
               compile_case_branch_body genv final_env case
                 (KLockOutput (true, loc, lock_term, state_ids)))
            retry
        in
        process_e @@
        PInput
          ( lock_term
          , lock_state_pattern ~done_flag:false state_pattern_ids
          , guard_proc
          , [precise_ident, None] )
      in
      let cont_state_pattern_ids =
        List.mapi
          (fun index _id -> Ident.local (Printf.sprintf "case_done_state_%d" index))
          state_ids
      in
      let cont_env = bind_lock_state penv state_ids cont_state_pattern_ids in
      let init_proc =
        process_e @@
        POutput
          ( lock_term
          , lock_state_message ~done_flag:false ~loc penv state_ids
          , process_e PNil )
      in
      let continuation =
        process_e @@
        PInput
          ( lock_term
          , lock_state_pattern ~done_flag:true cont_state_pattern_ids
          , continue_cmd genv cont_env kont
          , [precise_ident, None] )
      in
      let body = parallelize (init_proc :: List.map compile_branch cases @ [continuation]) in
      process_e @@ PRestr (lock_ident, None, channel_ident, body)

and compile_case_channelized
    genv
    penv
    (cases : T.case list)
    (kont : kont)
  : tprocess_e =
  (*
     3.5 Case Encoding

     ```
     case
       [ch :: msg("a")] -> c1
     | [ch :: msg("b")] -> c2
     end
     ```

     ```
     get channel_table(ch_type:acc_data_t, =ch) in
     get access_control_table(=ptype, =ch_type, =curr_syscall) in
     in(ch, msg(x:bitstring));
     if x = "a" then c1 else
     if x = "b" then c2 else
     0
     ```
  *)
  (* This is an optimized lowering for the common case where all channel
     guards in one [case] read the same fact name from the same channel. After
     the shared input, a private token preserves nondeterministic selection
     when multiple payload guards hold. *)
  let channel_guards =
    List.map (fun (case : T.case) ->
        match extract_channel_guard case.facts with
        | Some (channel, name, args, other_facts, loc) ->
            case, channel, name, args, other_facts, loc
        | None ->
            Error.unsupported ~loc:case.cmd.loc
              "Mixed channel/non-channel case branches are not supported yet")
      cases
  in
  List.iter
    (fun (_case, _channel, name, args, _other_facts, loc) ->
       GEnv.add_channel_fact ~loc genv name (List.length args))
    channel_guards;
  let first_channel, first_name, first_args =
    match channel_guards with
    | (_, first_channel, first_name, first_args, _, _) :: _ ->
        first_channel, first_name, first_args
    | [] ->
        Error.internal ~loc:Location.nowhere
          "Empty channelized case is not supported"
  in
  let channel_key = T.string_of_expr first_channel in
  let arity = List.length first_args in
  List.iter
    (fun (_case, channel, name, args, _facts, loc) ->
       if T.string_of_expr channel <> channel_key then
         Error.invalid_input ~loc
           "All channel guards in one case must use the same channel";
       if name <> first_name then
         Error.invalid_input ~loc
           "All channel guards in one case must use the same fact name";
       if List.length args <> arity then
         Error.invalid_input ~loc
           "All channel guards in one case must use the same arity")
    channel_guards;
  let payload_vars =
    List.init arity (fun i -> Ident.local (Printf.sprintf "case_arg_%d" i))
  in
  let payload_patterns =
    List.map (fun id -> PPatVar (compile_ident id, Some bitstring_ident)) payload_vars
  in
  let input_pattern = PPatFunApp (compile_name first_name "chan", payload_patterns) in
  let payload_terms =
    List.map (fun id -> pterm_e @@ PPIdent (compile_ident id)) payload_vars
  in
  let compile_branch base_env ~branch_kont ~else_proc
      (case, _channel, _name, args, facts, _loc) =
        let branch_env =
          List.fold_left2
            (fun penv (arg : T.expr) payload_term ->
               match arg.desc with
               | T.Ident { id; _ } when is_fresh_case_var case id ->
                   PEnv.bind_process_var penv id payload_term
               | _ -> penv)
            base_env
            args
            payload_terms
        in
        let arg_eq_tests =
          filter_map2
            (fun (arg : T.expr) payload_term ->
               match arg.desc with
               | T.Ident { id; _ } when is_fresh_case_var case id -> None
               | _ ->
                   Some (payload_term, compile_expr_to_pterm genv branch_env arg))
            args
            payload_terms
        in
        compile_guard_tests genv branch_env case.fresh facts
          (fun final_env ->
             compile_pterm_eq_tests arg_eq_tests
               (compile_case_branch_body genv final_env case branch_kont)
               else_proc)
          else_proc
  in
  let branches =
    match channel_guards with
    | [] -> process_e PNil
    | [channel_guard] ->
        compile_branch penv ~branch_kont:kont
          ~else_proc:(process_e PNil) channel_guard
    | _ ->
        let loc =
          match channel_guards with
          | (case, _, _, _, _, _) :: _ -> case.cmd.loc
          | [] -> assert false
        in
        let state_ids = List.map fst (lock_state_bindings penv) in
        let choice_id = Ident.local "channel_case_ch" in
        let choice_ident = compile_ident choice_id in
        let choice_term = pterm_e @@ PPIdent choice_ident in
        let compile_choice channel_guard =
          let state_pattern_ids =
            List.mapi
              (fun index _id ->
                 Ident.local (Printf.sprintf "channel_case_state_%d" index))
              state_ids
          in
          let choice_env = bind_lock_state penv state_ids state_pattern_ids in
          let retry =
            process_e @@
            POutput
              ( choice_term
              , lock_state_message ~done_flag:false ~loc choice_env state_ids
              , process_e PNil )
          in
          process_e @@
          PInput
            ( choice_term
            , lock_state_pattern ~done_flag:false state_pattern_ids
            , compile_branch choice_env
                ~branch_kont:(KLockOutput (true, loc, choice_term, state_ids))
                ~else_proc:retry channel_guard
            , [precise_ident, None] )
        in
        let cont_state_pattern_ids =
          List.mapi
            (fun index _id ->
               Ident.local (Printf.sprintf "channel_case_done_state_%d" index))
            state_ids
        in
        let cont_env = bind_lock_state penv state_ids cont_state_pattern_ids in
        let init_proc =
          process_e @@
          POutput
            ( choice_term
            , lock_state_message ~done_flag:false ~loc penv state_ids
            , process_e PNil )
        in
        let continuation =
          process_e @@
          PInput
            ( choice_term
            , lock_state_pattern ~done_flag:true cont_state_pattern_ids
            , continue_cmd genv cont_env kont
            , [precise_ident, None] )
        in
        process_e @@
        PRestr
          ( choice_ident
          , None
          , channel_ident
          , parallelize
              (init_proc :: List.map compile_choice channel_guards @ [continuation]) )
  in
  let channel_term = compile_expr_to_pterm genv penv first_channel in
  wrap_with_channel_access_get channel_term penv
    (process_e @@ PInput (channel_term, input_pattern, branches, []))
    (process_e PNil)

and compile_syscall_call
    genv
    penv
    (id : T.ident)
    (args : T.expr list)
    ~on_return:(on_return : pterm_e -> tprocess_e)
    (on_fallthrough : tprocess_e)
    ~loc
  : tprocess_e =
  (*
     3.9 Syscall and Attack Encoding

     ```
     syscall my_syscall(param) {
       ...
       return v
     }

     let x = my_syscall(arg) in body
     ```

     ```
     let curr_syscall = my_syscall__0__syscall in
     let x = (
       body_of_my_syscall
     ) in
     let curr_syscall = none__syscall in
     body
     ```

     Section 3.9 says that a passive attack is compiled like a syscall: its
     body is copied at the call site. Attacker facts use `attacker_ch`.

     ```
     passive attack eaves_mem(v) {
       put [::Out(v)]
     }
     _ := eaves_mem(value)
     ```

     ```
     out(attacker_ch, value);
     ```

     While compiling the copied body, access-control checks use
     `eaves_mem__0__syscall` as the current syscall.
  *)
  match GEnv.find_syscall_def genv id with
  | None ->
      Error.internal ~loc "syscall definition for %s is not available"
        (Ident.to_string id)
  | Some def ->
      let arg_values = List.map (compile_expr_to_pterm genv penv) args in
      let mk_call_env arg_ids =
        let call_env =
          List.fold_left2
            PEnv.bind_process_var
            (PEnv.with_curr_syscall penv (pterm_e @@ PPIdent def.pv_id))
            arg_ids
            arg_values
        in
        PEnv.with_process_return_cont call_env on_return
      in
      let normal_branch =
        compile_cmd genv (mk_call_env def.args) (KProc on_fallthrough) def.cmd
      in
      let attack_branches =
        if def.passive then
          []
        else
          List.map
            (fun attack_def ->
               compile_cmd genv (mk_call_env attack_def.args) (KProc on_fallthrough) attack_def.cmd)
            (GEnv.find_allowed_attacks ~loc genv
               ~process_typ_id:(PEnv.process_typ_id penv) ~syscall_id:id)
      in
      nondet_choose_processes (normal_branch :: attack_branches)

and compile_local_function_call
    genv
    penv
    (id : T.ident)
    (args : T.expr list)
    ~on_return:(on_return : pterm_e -> tprocess_e)
    (on_fallthrough : tprocess_e)
    ~loc
  : tprocess_e =
  (*
     3.9 Syscall and Attack Encoding

     ```
     function helper(a, b) { ...; return v }
     let x = helper(y, z) in body
     ```

     ```
     let x = (
       body_of_helper
     ) in
     body
     ```
  *)
  match PEnv.find_local_func_def penv id with
  | None ->
      Error.internal ~loc "local function definition for %s is not available"
        (Ident.to_string id)
  | Some (arg_ids, cmd) ->
      let arg_values = List.map (compile_expr_to_pterm genv penv) args in
      let call_env =
        List.fold_left2
          PEnv.bind_process_var
          penv
          arg_ids
          arg_values
      in
      let call_env =
        PEnv.with_process_return_cont call_env on_return
      in
      compile_cmd genv call_env (KProc on_fallthrough) cmd

and compile_let_binding
    genv
    penv
    (kont : kont)
    (id : T.ident)
    (expr : T.expr)
    (body : T.cmd)
  : tprocess_e =
  (*
     3.4 Encoding Structured facts, new, let, delete
     3.9 Syscall and Attack Encoding

     ```
     let x = e in c
     let x = my_syscall(a) in c
     ```

     ```
     let x = e in
     c

     let curr_syscall = my_syscall__0__syscall in
     let x = (body_of_my_syscall) in
     let curr_syscall = none__syscall in
     c
     ```
  *)
  (* A value-binding body cannot run when the call falls through without
     returning: there is no value with which to bind [id]. Discarded calls are
     handled by [compile_assignment] below and do retain their fallthrough
     continuation. *)
  match expr.desc with
  | Apply (syscall_id, args) when Option.is_some (GEnv.find_syscall_def genv syscall_id) ->
      let old_value = PEnv.find_process_var penv id in
      compile_syscall_call genv penv syscall_id args
        ~on_return: (fun value ->
            compile_cmd genv (PEnv.bind_process_var penv id value)
              (KRestoreVars ([id, old_value], kont))
              body)
        (process_e PNil)
        ~loc:expr.loc
  | Apply (func_id, args) when Option.is_some (PEnv.find_local_func_def penv func_id) ->
      let old_value = PEnv.find_process_var penv id in
      compile_local_function_call genv penv func_id args
        ~on_return: (fun value ->
            compile_cmd genv (PEnv.bind_process_var penv id value)
              (KRestoreVars ([id, old_value], kont))
              body)
        (process_e PNil)
        ~loc:expr.loc
  | _ ->
      let value = compile_expr_to_pterm genv penv expr in
      let old_value = PEnv.find_process_var penv id in
      compile_cmd genv (PEnv.bind_process_var penv id value)
        (KRestoreVars ([id, old_value], kont))
        body

and compile_assignment
    genv
    penv
    (kont : kont)
    (id_opt : T.ident option)
    (expr : T.expr)
  : tprocess_e =
  (*
     3.9 Syscall and Attack Encoding

     ```
     x := my_syscall(a)
     _ := my_syscall(a)
     ```

     ```
     let curr_syscall = my_syscall__0__syscall in
     let x = (body_of_my_syscall) in
     let curr_syscall = none__syscall in
     ...
     ```
  *)
  match expr.desc with
  | Apply (syscall_id, args) when Option.is_some (GEnv.find_syscall_def genv syscall_id) ->
      let on_return =
        match id_opt with
        | None -> fun _value -> continue_cmd genv penv kont
        | Some id -> fun value -> continue_cmd genv (PEnv.bind_process_var penv id value) kont
      in
      compile_syscall_call genv penv syscall_id args ~on_return
        (continue_cmd genv penv kont)
        ~loc:expr.loc
  | Apply (func_id, args) when Option.is_some (PEnv.find_local_func_def penv func_id) ->
      let on_return =
        match id_opt with
        | None -> fun _value -> continue_cmd genv penv kont
        | Some id -> fun value -> continue_cmd genv (PEnv.bind_process_var penv id value) kont
      in
      compile_local_function_call genv penv func_id args ~on_return
        (continue_cmd genv penv kont)
        ~loc:expr.loc
  | _ ->
      (match id_opt with
       | Some id ->
           let value = compile_expr_to_pterm genv penv expr in
           continue_cmd genv (PEnv.bind_process_var penv id value) kont
       | None ->
           let _ = compile_expr_to_pterm genv penv expr in
           continue_cmd genv penv kont)

and continue_cmd genv penv (kont : kont) : tprocess_e =
  match kont with
  | KStop -> process_e PNil
  | KProc proc -> proc
  | KSeq (cmd, kont) -> compile_cmd genv penv kont cmd
  | KRestoreVars (saved, kont) ->
      continue_cmd genv (PEnv.restore_process_vars penv saved) kont
  | KLockOutput (done_flag, loc, lock_term, state_ids) ->
      process_e
        (POutput
           ( lock_term
           , lock_state_message ~done_flag ~loc penv state_ids
           , process_e PNil ))

and compile_cmd genv penv (kont : kont) (cmd : T.cmd) : tprocess_e =
  match cmd.desc with
  | Skip -> continue_cmd genv penv kont
  | Sequence (cmd1, cmd2) ->
      compile_cmd genv penv (KSeq (cmd2, kont)) cmd1
  | Put facts ->
      compile_put_facts genv penv facts @@ continue_cmd genv penv kont
  | Event facts ->
      compile_event_facts genv penv facts @@ continue_cmd genv penv kont
  | Let (id, expr, body) ->
      compile_let_binding genv penv kont id expr body
  | Assign (id_opt, expr) ->
      compile_assignment genv penv kont id_opt expr
  | Return expr ->
      let value = compile_expr_to_pterm genv penv expr in
      (match PEnv.return_cont penv with
       | Some return_cont -> return_cont value
       | None ->
           (* return in the main process *)
           continue_cmd genv penv kont
      )
  | Case cases ->
      if List.exists (fun (case : T.case) ->
          Option.is_some (extract_channel_guard case.facts)) cases
      then
        compile_case_channelized genv penv cases kont
      else
        compile_case_no_channel genv penv cases kont
  | While (repeat_cases, until_cases) ->
      (*
         3.6 Repeat Encoding

         ```
         repeat [A1] -> c1 | ... until [B1] -> d1 | ... end
         ```

         ```
         new lock_ch : channel;

         (* start *)
         out(lock_ch, (0, s0, ..., sk))
         |
         (* loop *)
         !( (* loop *)
            in(lock_ch, (=0, s0:bitstring, ..., sk:bitstring)) [precise];
            ...
            if ... then
              case body
              out(lock_ch, (0, s0', ..., sk')) (* keep looping *)
            else
              (* guard failure *)
              out(lock_ch, (0, s0', ..., sk')) (* keep looping *)
            |
            (* until *)
            in(lock_ch, (=0, s0:bitstring, ..., sk:bitstring)) [precise];
            ...
            if ... then
              until case body
              out(lock_ch, (1, s0', ..., sk')) (* exit the loop *)
            else
              (* guard failure *)
              out(lock_ch, (0, s0', ..., sk')) (* keep looping *)
          )
         |
         (* out of the loop *)
         in(lock_ch, (=1, s0:bitstring, ..., sk:bitstring)) [precise];
          rest_of_program
         ```
      *)
      (* `s0, ..., sk` *)
      let state_ids = List.map fst (lock_state_bindings penv) in
      (* `lock_ch` *)
      let lock_id = Ident.local "loop_ch" in
      let lock_ident = compile_ident lock_id in
      let lock_term = pterm_e @@ PPIdent lock_ident in
      let branch is_until (case : T.case) =
        let state_pattern_ids =
          List.mapi (fun index _id ->
              Ident.local @@ Printf.sprintf "loop_state_%d" index)
            state_ids
        in
        let branch_env = bind_lock_state penv state_ids state_pattern_ids in
        let else_proc =
          process_e @@
          POutput
            ( lock_term
            , lock_state_message ~done_flag:false ~loc:cmd.loc branch_env state_ids
            , process_e PNil )
        in
        let guard_proc =
          match extract_channel_guard case.facts with
          | Some (channel, name, args, other_facts, _loc) ->
              compile_channel_guard_case genv branch_env case
                (KLockOutput (is_until, cmd.loc, lock_term, state_ids))
                channel name args other_facts
                ~else_proc
          | None ->
              compile_guard_tests genv branch_env case.fresh case.facts
                (fun final_env ->
                   compile_case_branch_body genv final_env case @@
                   KLockOutput (is_until, cmd.loc, lock_term, state_ids))
                else_proc
        in
        (*
            ```
            in(lock_ch, (=0, s0:bitstring, ..., sk:bitstring)) [precise];
            ...
            if ... then
              case body
              out(lock_ch, (0, s0', ..., sk')) (* keep looping *)
            else
              (* guard failure *)
              out(lock_ch, (0, s0', ..., sk')) (* keep looping *)
            ```
        *)
        process_e @@
        PInput
          ( lock_term
          , lock_state_pattern ~done_flag:false state_pattern_ids
          , guard_proc
          , [precise_ident, None] )
      in
      let repeat_branch = branch false in
      let until_branch = branch true in
      let cont_state_pattern_ids =
        List.mapi
          (fun index _id -> Ident.local (Printf.sprintf "loop_done_state_%d" index))
          state_ids
      in
      let cont_env = bind_lock_state penv state_ids cont_state_pattern_ids in
      let init_proc =
        (* `out(lock_ch, (0, s0, ..., sk))` *)
        process_e
          (POutput
             ( lock_term
             , lock_state_message ~done_flag:false ~loc:cmd.loc penv state_ids
             , process_e PNil ))
      in
      let workers =
        match
          List.map repeat_branch repeat_cases
          @ List.map until_branch until_cases
        with
        | [] -> process_e PNil
        | procs -> process_e @@ PRepl (parallelize procs)
      in
      let continuation =
        (* `in(lock_ch, (=1, s0:bitstring, ..., sk:bitstring)) [precise];` *)
        process_e
          (PInput
             ( lock_term
             , lock_state_pattern ~done_flag:true cont_state_pattern_ids
             , continue_cmd genv cont_env kont
             , [precise_ident, None] ))
      in
      process_e
        (PRestr
           ( lock_ident
           , None
           , channel_ident
           , parallelize [init_proc; workers; continuation] ))

  | New (id, None, body) ->
      (* ```
         new x in c
         ```

         ```
         new x:bitstring; c
         ```
      *)
      let fresh_ident = compile_ident id in
      let fresh_term = pterm_e @@ PPIdent fresh_ident in
      let old_value = PEnv.find_process_var penv id in
      process_e @@
      PRestr
        ( fresh_ident
        , None
        , bitstring_ident
        , compile_cmd genv
            (PEnv.bind_process_var penv id fresh_term) (* compile body with id *)
            (KRestoreVars ([id, old_value], kont)) (* recover the original PEnv for kont *)
            body )
  | New (id, Some (name, args), body) ->
      (* ```
         new x = S(e1, ..., en) in c
         ```

         ```
         new a:bitstring; c[S(a, e1, ..., en)/x]]
         ```
      *)
      (* `compile_generated_structure_decls` handle the declarations *)
      GEnv.add_structure_fact ~loc:cmd.loc genv name (List.length args);
      let fresh_ident = compile_ident id in
      let fresh_term = pterm_e @@ PPIdent fresh_ident in
      let old_value = PEnv.find_process_var penv id in
      let struct_term =
        (* `S(a, e1, ..., en)` *)
        pterm_e @@
        PPFunApp
          ( structure_ctor_ident name
          , fresh_term :: List.map (compile_expr_to_pterm genv penv) args )
      in
      process_e @@
      PRestr
        ( fresh_ident
        , None
        , bitstring_ident
        , compile_cmd genv
            (PEnv.bind_process_var penv id struct_term) (* compile body with id *)
            (KRestoreVars ([id, old_value], kont)) (* recover the original PEnv for kont *)
            body )
  | Get (ids, expr, name, body) ->
      (* ```
         let x1, ..., xn = e.S in c
         ```

         ```
         get deleted_address_table(=S__struct_addr(e))
         else c[S__struct_par_1(e)/x1, ..., S__struct_par_n(e)/xn]
         ```
      *)
      GEnv.add_structure_fact ~loc:cmd.loc genv name (List.length ids);
      let struct_term = compile_expr_to_pterm genv penv expr in
      let addr_term = structure_addr_term name struct_term in
      let saved =
        (* the values of x1, ..., xn before let *)
        List.map (fun id -> id, PEnv.find_process_var penv id) ids
      in
      let body_env =
        (* xi => S__struct_par_i(e) *)
        List.mapi
          (fun index id -> id, structure_arg_term name (index + 1) struct_term)
          ids
        |> List.fold_left
             (fun penv (id, value) -> PEnv.bind_process_var penv id value)
             penv
      in
      process_e @@
      PGet
        ( deleted_address_table_ident
        , [PPatEqual addr_term]
        , None
        , process_e PNil
        , (* else *)
          compile_cmd genv body_env (* compile body under body_env *)
            (KRestoreVars (saved, kont)) (* Recover saved for kont *)
            body
        , [] )
  | Del (expr, name) ->
      (* 3.4  Encoding Structured facts, new, let, delete

         ```
         delete x.Struct
         ```

         ```
         table deleted_address_table(bitstring).
         ...
         insert deleted_address_table(Struct__struct_addr(x_struct));
         ```
      *)
      (* x_struct *)
      let struct_term = compile_expr_to_pterm genv penv expr in
      (* Struct__struct_addr(x_struct) *)
      let addr_term = structure_addr_term name struct_term in
      (* insert deleted_address_table( Struct__struct_addr(x_struct) ); ... *)
      add_comment (Printf.sprintf "delete _.%s" name) @@
      process_e
        (PInsert
           (deleted_address_table_ident, [addr_term], continue_cmd genv penv kont))

let compile_process_body genv penv cmd =
  compile_cmd genv penv KStop cmd
