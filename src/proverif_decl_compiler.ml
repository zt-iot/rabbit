open Rabbit_proverif_pv_parse
open Pitptree
include Proverif_process_compiler

let rec collect_decl (genv : GEnv.t) (decl : T.decl) =
  let loc = decl.loc in
  match decl.desc with
  | Syscall { id; args; cmd; attack = passive } ->
      (* Syscalls and passive attacks are expanded when they are called.
         No declaration is generated at this point.  *)
      GEnv.add_syscall_def ~loc ~passive genv id args cmd
  | Attack { id; syscall; args; cmd } ->
      (* Attacks are expanded when they are called.
         No declaration is generated at this point.  *)
      GEnv.add_attack_def ~loc genv id { syscall; args; cmd; }
  | AllowAttack { process_typs; attacks } ->
      List.iter
        (fun process_typ -> GEnv.add_allowed_attacks genv process_typ attacks)
        process_typs
  | Process { id; typ; _ } ->
      GEnv.add_process_type ~loc genv id typ
  | Init { id; desc = Value_with_param (param, expr) } ->
      GEnv.add_param_init genv id param expr
  | Load (_filename, decls) ->
      List.iter (collect_decl genv) decls
  | _ -> ()

(*
  Line 30:

  ```
  function enc:2

  fun enc__0 ( bitstring, bitstring ): bitstring.
  ```
*)
let compile_function ~loc:_loc (id : T.ident) (typ : Type.callable_type) : tdecl list =
  let name = compile_ident id in
  let arity = List.length typ.argument_types in
  [ TComment (Printf.sprintf "function %s:%d" (Ident.to_string id) arity)
  ; TFunDecl
      ( name
      , List.map compile_value_type typ.argument_types
      , compile_value_type typ.result_type
      , [] )
  ]

(*
   Line 25:  Encoding Equational Theories

   ```
   equation dec(enc(x, y), y) = x

   equation forall d:bitstring, k:bitstring;
     dec(enc(d, k), k) = d.
   ```

   Here we have with a return type:

   ```
   equation forall x__5:bitstring, y__6:bitstring;
     dec(enc(x__5, y__6), y__6) = x__5.
   ```

   TODO: Line 40: Potential Improvement
*)
let compile_equation ~loc:_loc genv (lhs : T.expr) (rhs : T.expr) : tdecl list =
  let envdecl =
    List.sort_uniq compare (T.vars_of_expr lhs @ T.vars_of_expr rhs)
    |> List.map (fun id ->
         let typ =
           match Env.find_opt_by_id lhs.env id with
           | Some desc -> Option.get (Env.type_of_desc desc)
           | None ->
               let desc = Option.get (Env.find_opt_by_id rhs.env id) in
               Option.get (Env.type_of_desc desc)
         in
         compile_ident id, compile_value_type typ)
  in
  let lhs_term = compile_expr_to_term genv lhs in
  let rhs_term = compile_expr_to_term genv rhs in
  let equality_term =
    term_e @@ PFunApp (pv_ident "=", [lhs_term; rhs_term])
  in
  [ TComment (Printf.sprintf "equation %s = %s" (T.string_of_expr lhs) (T.string_of_expr rhs))
  ; TEquation ([envdecl, EETerm equality_term], [])
  ]

(* 3.2 Encoding Process Types, Channel types, File types, and Access

   ```
   type client_t : process
   type udp_t : channel
   ```

   ```
   type proc_t.
   type acc_data_t.

   const client_t : proc_t.
   const udp_t : acc_data_t.
   ```
*)
let compile_type ~loc:_loc (id : T.ident) (typclass : Input.type_class) =
  let ty =
    match typclass with
    | CProc -> proc_t_ident
    | CFsys | CChan -> acc_data_t_ident
  in
  [ TComment (Printf.sprintf "type %s : %s" (Ident.to_string id) (Input.string_of_type_class typclass))
  ; TConstDecl (compile_ident id, ty, [])
  ]

(* 3.2 Encoding Process Types, Channel types, File types, and Control Policies

   ```
   allow client_t udp_t [send]
   ```

   ```
   table access_control_table(proc_t, acc_data_t, syscall_t).
   ...
   insert access_control_table(client_t, udp_t, send__0__syscall);
   ```
*)
let compile_allow
    ~loc
    (genv : GEnv.t)
    (t_process_typ : T.ident)
    (t_target_typs : T.ident list)
    (syscalls : T.ident list option)
  =
  let process_typ = compile_ident t_process_typ in
  let target_typs = List.map compile_ident t_target_typs in
  match syscalls with
  | None ->
      (* Note: there is no specification how to compile `allow ... [.]`. *)
      List.iter2 (fun t_target_typ target_typ ->
          let entry =
            { rabbit_process_type = t_process_typ
            ; rabbit_target_type = t_target_typ
            ; rabbit_syscall = None
            ; pv_process_type = process_typ
            ; pv_target_type = target_typ
            ; pv_syscall = None
            }
          in
          GEnv.add_allow_entry genv entry)
        t_target_typs target_typs;
      []
  | Some syscalls ->
      List.iter2 (fun t_target_typ target_typ ->
          List.iter (fun syscall ->
              match GEnv.find_syscall_def genv syscall with
              | None ->
                  Error.internal ~loc "Syscall %s is not registered"
                    (Ident.to_string syscall)
              | Some def ->
                  let entry =
                    { rabbit_process_type = t_process_typ
                    ; rabbit_target_type = t_target_typ
                    ; rabbit_syscall = Some syscall
                    ; pv_process_type = process_typ
                    ; pv_target_type = target_typ
                    ; pv_syscall = Some def.pv_id
                    }
                  in
                  GEnv.add_allow_entry genv entry)
            syscalls)
        t_target_typs target_typs;
      []

let rec compile_param_init_expr genv (formal : T.ident) (expr : T.expr) : pterm_e =
  let compile = compile_param_init_expr genv formal in
  let compile_argument (argument : T.expr) =
    match argument.desc with
    | Ident { id; param = None; _ } when id = formal ->
        pterm_e @@ PPIdent (compile_ident formal)
    | _ ->
        pterm_e @@ PPIdent (GEnv.fresh_parameter_ident genv argument)
  in
  pterm_e @@
  match expr.desc with
  | Ident { id; param = Some argument; _ } ->
      PPFunApp (compile_ident id, [compile_argument argument])
  | Ident { id; param = None; _ } ->
      PPIdent (compile_ident id)
  | Apply (id, args) ->
      PPFunApp (compile_ident id, List.map compile args)
  | Tuple exprs ->
      PPTuple (List.map compile exprs)
  | Unit ->
      PPTuple []
  | String s ->
      PPIdent (GEnv.fresh_string_ident genv s)
  | Boolean true ->
      PPIdent true_ident
  | Boolean false ->
      PPIdent false_ident
  | Integer n ->
      PPIdent (GEnv.fresh_integer_ident genv n)
  | Float _ ->
      Error.unsupported ~loc:expr.loc
        "Float terms are not supported in ProVerif term translation"

let compile_init ~loc:(_loc : Location.t) genv (id : T.ident) (desc : T.init_desc) : tdecl list =
  (*
     3.1 Encoding Strings, Constants, Events and Function Declarations
     3.10 Parametrized Feature Encoding

     ```
     const fresh priv_k
     const pubkey<k> = pk(priv_k<k>)
     ```

     ```
     const priv_k : bitstring [private].
     reduc forall k:param_data; pubkey(k) = pk(priv_k(k)).
     ```
  *)
  let init_ident = compile_ident id in
  match desc with
  | Fresh ->
      [ TComment (Printf.sprintf "const fresh %s" (Ident.to_string id))
      ; TConstDecl (init_ident, bitstring_ident, [pv_ident "private", None])
      ]
  | Value expr ->
      let init_term = term_e @@ PIdent init_ident in
      let value_term = compile_expr_to_term genv expr in
      [ TComment (Printf.sprintf "const %s = .." (Ident.to_string id))
      ; TConstDecl (init_ident, bitstring_ident, [])
      ; TEquation
          ( [ [], EETerm (term_e @@ PFunApp (pv_ident "=", [init_term; value_term])) ]
          , [] )
      ]
  | Value_with_param (param, expr) ->
      let param_ident = compile_ident param in
      let value_term = compile_param_init_expr genv param expr in
      [ TComment (Printf.sprintf "const %s<%s> = .." (Ident.to_string id) (Ident.to_string param))
      ; TLetFun (init_ident, [param_ident, param_data_ident, false], value_term)
      ]
  | Fresh_with_param ->
      [ TComment (Printf.sprintf "const fresh %s<>" (Ident.to_string id))
      ; TFunDecl
          ( init_ident
          , [param_data_ident]
          , bitstring_ident
          , [pv_ident "private", None] )]

let compile_channel
    ~loc:_loc
    (id : T.ident)
    (param : unit option)
    (typ : T.ident)
  =
  (*
     3.3 Encoding of process and channels declarations

     ```
     channel udp : udp_t
     ```

     ```
     free udp : channel [private].
     ```
  *)
  match param with
  | Some () ->
      (* A private channel-valued constructor preserves instance identity:
         the same family and parameter denote the same channel. Passing the
         family itself to a process is handled separately and remains unsupported. *)
      [ TComment (Printf.sprintf "channel %s<> : %s" (Ident.to_string id) (Ident.to_string typ))
      ; TFunDecl
          (compile_ident id, [param_data_ident], channel_ident, [pv_ident "private", None])
      ]
  | None ->
      [ TComment (Printf.sprintf "channel %s : %s" (Ident.to_string id) (Ident.to_string typ))
      ; TFree (compile_ident id, channel_ident, [pv_ident "private", None])
      ]

let process_file_channel_ident : ident = pv_ident "file_ch"

let wrap_with_channel_init
    ~loc
    (args : T.chan_param list)
    (body : tprocess_e)
  : tprocess_e =
  (*
     3.2 Encoding Process Types, Channel types, File types, and Access Control Policies

     ```
     process client(ch_net : udp_t, ch_rpc : rpc_t) : client_t { ... }
     ```

     ```
     insert channel_table(udp_t, ch_net);
     insert channel_table(rpc_t, ch_rpc);
     ...
     ```
  *)
  List.fold_right
    (fun ({ channel; param; typ } : T.chan_param) acc ->
       match param with
       | Some () ->
           Error.unsupported ~loc
             "Parameterized process channel arguments are not supported yet"
       | None ->
           add_comment (Printf.sprintf "Channel %s : %s" (Ident.to_string channel) (Ident.to_string typ)) @@
           process_e @@
             PInsert
                ( channel_table_ident
                , [ pterm_e @@ PPIdent (compile_ident typ)
                  ; pterm_e @@ PPIdent (compile_ident channel)
                  ]
                , acc ))
    args
    body

let wrap_with_file_init
    ~loc
    (genv : GEnv.t)
    (penv : PEnv.t)
    (files : (T.expr * T.ident * T.expr) list)
    (body : tprocess_e)
  : tprocess_e =
  (*
     3.7 File Fact Encoding

     ```
     process client_ta(...) : client_ta_t {
       file "/secret/priv" : readonly_t = enc(priv_k, sym_k)
       ...
     }
     ```

     ```
     insert file_type_table(ptype, readonly_t, secret_priv__str);
     new file_ch : channel;
     out(file_ch, (secret_priv__str, enc(priv_k, sym_k))) |
     ...
     ```
  *)
  match PEnv.file_channel penv with
  | None ->
      if files = [] then
        body
      else
        Error.internal ~loc
          "Internal file channel is not available for process file setup"
  | Some file_channel ->
      let output_processes =
        List.map
          (fun ((path, _typ, contents) : T.expr * T.ident * T.expr) ->
             let payload =
               pterm_e @@
                 PPTuple
                    [ compile_expr_to_pterm genv penv path
                    ; compile_expr_to_pterm genv penv contents
                    ]
             in
             process_e @@ POutput (file_channel, payload, process_e @@ PNil))
          files
      in
      let parallel_body =
        match output_processes with
        | [] -> body
        | proc :: procs ->
            List.fold_left
              (fun acc proc -> process_e @@ PPar (acc, proc))
              proc
              (body :: procs)
      in
      let with_channel =
        process_e @@ PRestr (process_file_channel_ident, None, channel_ident, parallel_body)
      in
      List.fold_right
        (fun ((path, typ, _contents) : T.expr * T.ident * T.expr) acc ->
           add_comment (Printf.sprintf "file %s : %s = .." (T.string_of_expr path) (Ident.to_string typ)) @@
           process_e @@
             PInsert
                ( file_type_table_ident
                , [ pterm_e @@ PPIdent ptype_arg_ident
                  ; pterm_e @@ PPIdent (compile_ident typ)
                  ; compile_expr_to_pterm genv penv path
                  ]
                , acc ))
        files
        with_channel

(* 3.3 Encoding of process and channels declarations

   ```
   process client(ch_net : udp_t, ch_rpc : rpc_t) : client_t
   {
      ..
   }
   ```

   ```
   let client(ptype : prot_t, ch_net : channel, ch_rpc : channel) = ..
*)
let compile_process
    genv
    ~loc
    (id : T.ident)
    (param : T.ident option)
    (args : T.chan_param list)
    (typ : T.ident)
    (files : (T.expr * T.ident * T.expr) list)
    (vars : (T.ident * T.expr) list)
    (funcs : (T.ident * T.ident list * T.cmd) list)
    (main : T.cmd)
  : tdecl list =
  let funcs =
    List.map (fun (id, args, cmd) -> id, (args, cmd)) funcs
  in
  let proc_args =
    (*
       3.10 Parametrized Feature Encoding

       ```
       process worker<p>() : proc_t { ... }
       ```

       ```
       let worker(ptype:proc_t, p:param_data) = ...
       ```
    *)
    (ptype_arg_ident, proc_t_ident, false)
    ::
    Option.to_list
      (Option.map (fun param -> compile_ident param, param_data_ident, false) param)
    @
    List.map
      (fun ({ channel; param; _ } : T.chan_param) ->
         match param with
         | Some () ->
             Error.unsupported ~loc
               "Parameterized process channel arguments are not supported yet"
         | None -> compile_ident channel, channel_ident, false)
      args
  in
  let base_penv =
    let file_channel =
      match files with
      | [] -> None
      | _ -> Some (pterm_e @@ PPIdent process_file_channel_ident)
    in
    PEnv.create_process_env
      ~local_func_defs:funcs
      ~process_typ_id:typ
      ~proc_type:(pterm_e @@ PPIdent ptype_arg_ident)
      ~curr_syscall:(pterm_e @@ PPIdent none_syscall_ident)
      ~file_channel
  in
  let base_penv =
    match param with
    | None -> base_penv
    | Some param ->
        PEnv.define_process_var base_penv param Type.TParameter
          (pterm_e @@ PPIdent (compile_ident param))
  in
  let penv =
    List.fold_left (fun penv (var, expr) ->
        let value = compile_expr_to_pterm genv penv expr in
        PEnv.define_process_var penv var (T.type_of_expr expr) value)
      base_penv vars
  in
  let process =
    wrap_with_channel_init ~loc args
    @@ wrap_with_file_init ~loc genv penv files
    @@ compile_process_body genv penv main
  in
  [ TComment (Printf.sprintf "process %s(..): %s" (Ident.to_string id) (Ident.to_string typ))
  ; TPDef (compile_ident id, proc_args, process)
  ]

let compile_proc_call genv parameter_bindings (proc : T.proc) : tprocess_e =
  (*
     3.3 Encoding of process and channels declarations

     ```
     client(udp, rpc)
     ```

     ```
     client(client_t, udp, rpc)
     ```
  *)
  let proc_desc = proc.data in
  let proc_type = GEnv.find_process_type ~loc:proc.loc genv proc_desc.id in
  let args =
    (pterm_e @@ PPIdent proc_type)
    ::
    (match proc_desc.parameter with
     | None -> []
     | Some { desc= Ident { id; desc= Env.Param; param= None }; _ } ->
         (match List.assoc_opt id parameter_bindings with
          | Some parameter -> [parameter]
          | None ->
              Error.internal ~loc:proc.loc
                "process parameter %s is not bound"
                (Ident.to_string id))
     | Some _ ->
         Error.unsupported ~loc:proc.loc
           "Only a directly bound process parameter is supported in ProVerif process instantiation")
    @
    List.map
      (fun ({ channel; parameter; _ } : T.chan_arg) ->
         match parameter with
         | None -> pterm_e @@ PPIdent (compile_ident channel)
         | Some (Some parameter) ->
             let parameter_term =
               match parameter.desc with
               | Ident { id; desc = Env.Param; param = None } ->
                   (match List.assoc_opt id parameter_bindings with
                    | Some value -> value
                    | None -> Error.internal ~loc:proc.loc
                        "channel parameter %s is not bound" (Ident.to_string id))
               | Ident { param = None; _ } | Integer _ | String _ | Boolean _ ->
                   pterm_e @@ PPIdent (GEnv.fresh_parameter_ident genv parameter)
               | _ -> Error.unsupported ~loc:proc.loc
                   "Only a directly bound or atomic constant channel parameter is supported"
             in
             pterm_e @@ PPFunApp (compile_ident channel, [parameter_term])
         | Some None ->
             Error.unsupported ~loc:proc.loc
               "Passing a parameterized channel family is not supported yet")
      proc_desc.args
  in
  process_e @@ PLetDef (compile_ident proc_desc.id, args, None)

let parallel_proc (procs : tprocess_e list) : tprocess_e =
  match procs with
  | [] -> process_e @@ PNil
  | proc :: procs ->
      List.fold_left
        (fun acc proc -> process_e @@ PPar (acc, proc))
        proc
        procs

let compile_proc_group_desc genv (proc_group : T.proc_group_desc) : tprocess_e =
  (*
     3.3 Encoding of process and channels declarations

     ```
     !group.(p1 | p2)
     ```

     ```
     !(p1 | p2)
     ```
  *)
  match proc_group with
  | Unbounded proc -> compile_proc_call genv [] proc
  | Bounded (id, procs) ->
      (*
         3.10 Parameter Instantiation

         ```
         !p.(worker<p>() | peer<p>())
         ```

         ```
         !(new p:param_data; (worker(proc_t, p) | peer(proc_t, p)))
         ```
      *)
      let pv_id = compile_ident id in
      let parameter = pterm_e @@ PPIdent pv_id in
      let body =
        parallel_proc (List.map (compile_proc_call genv [id, parameter]) procs)
      in
      process_e @@ PRepl (process_e @@ PRestr (pv_id, None, param_data_ident, body))

let gterm_binary (op : string) (lhs : gterm_e) (rhs : gterm_e) : gterm_e =
  gterm_e @@ PGFunApp (pv_ident op, [lhs; rhs], None)

(* `g1 op g2 op .. op gn` *)
let rec gterm_binary_mult ~loc op = function
  | [] ->
      Error.internal ~loc "Cannot combine an empty list of query facts"
  | [g] -> g
  | g :: gs ->
      gterm_binary op g (gterm_binary_mult ~loc op gs)

let gterm_event_ident (event_ident : ident) (args : gterm_e list) : gterm_e =
  gterm_e @@
  PGFunApp
    ( pv_ident "event"
    , [gterm_e @@ PGFunApp (event_ident, args, None)]
    , None )

let gterm_event
    (name : T.name)
    (kind : event_kind)
    (args : gterm_e list)
  : gterm_e =
  gterm_event_ident (compile_event_name name kind) args

let compile_lemma_fact genv (fact : T.fact) : gterm_e =
  let loc = fact.loc in
  match fact.desc with
  | Global (name, args) ->
      GEnv.add_event ~loc genv name Global (List.map T.type_of_expr args);
      gterm_event name Global (List.map (compile_expr_to_gterm genv) args)
  | Plain (name, args) ->
      GEnv.add_event ~loc genv name Plain (List.map T.type_of_expr args);
      gterm_event name Plain (List.map (compile_expr_to_gterm genv) args)
  | Eq (lhs, rhs) ->
      GEnv.add_comparison_event ~loc genv Equality (T.type_of_expr lhs);
      gterm_event_ident
        (compile_comparison_event_name Equality)
        [ compile_expr_to_gterm genv lhs
        ; compile_expr_to_gterm genv rhs
        ]
  | Neq (lhs, rhs) ->
      GEnv.add_comparison_event ~loc genv Inequality (T.type_of_expr lhs);
      gterm_event_ident
        (compile_comparison_event_name Inequality)
        [ compile_expr_to_gterm genv lhs
        ; compile_expr_to_gterm genv rhs
        ]
  | Channel _ | File _ ->
      (* Section 3.12 does not specify how to translate Channel and File facts *)
      Error.unsupported ~loc
        "Channel/file facts are not supported in ProVerif lemma lowering"

(* 3.12 Encoding Properties

   ```
   system
     ...
   requires
   [
     lemma Reachable :
       reachable ::ClientClose(), ::ClientTAClose(), ::ImgRecvValid(x) ;

     lemma Correspondence : (* falsified *)
       corresponds ::ImgRecvValid(x) ~> ::ImgSend (x)
   ]
   ```

   ```
   query x:bitstring;
     event(ClientClose)
     && event(ClientTAClose)
     && event(ImgRecvValid(x)) .

   query x:bitstring;
     event(ImgRecvValid(x)) ==> event(ImgSend(x)) .
   ```
*)
let compile_lemma
    genv
    ((lemma_id, lemma) : T.ident * T.lemma) : tdecl list =
  let fresh, facts =
    match lemma.desc with
    | T.Plain _ -> [], []
    | Reachability { fresh; facts } -> fresh, facts
    | Correspondence { fresh; premise; conclusion } ->
        fresh, [premise; conclusion]
  in
  let envdecl =
    List.map
      (fun id ->
         let desc =
           List.find_map (fun (fact : T.fact) -> Env.find_opt_by_id fact.env id) facts
           |> Option.get
         in
         compile_ident id, compile_value_type (Option.get (Env.type_of_desc desc)))
      fresh
  in
  let query =
    match lemma.desc with
    | T.Plain s ->
        (* No spec for Plain lemma *)
        Error.unsupported ~loc:lemma.loc
          "Plain lemma %S is not supported in ProVerif query lowering" s
    | Reachability { facts; _ } ->
        add_comment (Printf.sprintf "reachable %s" (String.concat ", " (List.map (fun _ -> "_") facts))) @@
        tquery_e @@
        PRealQuery
          (gterm_binary_mult ~loc:lemma.loc "&&" (List.map (compile_lemma_fact genv) facts), [])
    | Correspondence { premise; conclusion; _ } ->
        add_comment "corresponds _ ~> _" @@
        tquery_e @@
        PRealQuery
          (gterm_binary "==>"
             (compile_lemma_fact genv premise)
             (compile_lemma_fact genv conclusion), [])
  in
  [ TComment (Printf.sprintf "lemma %s" (Ident.to_string lemma_id))
  ; TQuery (envdecl, [query], [])
  ]

(* 3.3 Encoding of process and channels declarations

   ```
   system
     client(udp, rpc)
     | server(udp)
     | client_ta(rpc)
   requires ..
   ```

   ```
   process
     ...
     client(client_t, udp, rpc)
     | server(server_t, udp)
     | client_ta(client_ta_t, rpc)
     ...
   ```
*)
let compile_system
    ~loc
    (genv : GEnv.t)
    (procs : T.proc_group_desc list)
    (lemmas : (T.ident * T.lemma) list) : tdecl list
  =
  if GEnv.top_process genv <> None then
    Error.invalid_input ~loc "Multiple system declarations are not accepted";
  let top_process = parallel_proc @@ List.map (compile_proc_group_desc genv) procs in
  GEnv.set_top_process genv top_process;
  TComment "Requires" :: List.concat_map (compile_lemma genv) lemmas

let compile_prelude (_genv : GEnv.t) : tdecl list =
  (*
     3.2 Encoding Process Types, Channel types, File types, and Access Control Policies
     3.7 File Fact Encoding
     3.9 Syscall and Attack Encoding

     ```
     type client_t : process
     type udp_t : channel
     allow client_t udp_t [send]
     ```

     ```
     type proc_t.
     type acc_data_t.
     type syscall_t.
     free attacker_ch : channel.
     table access_control_table(proc_t, acc_data_t, syscall_t).
     table file_type_table(proc_t, acc_data_t, bitstring).
     table channel_table(acc_data_t, channel).
     table deleted_address_table(bitstring).
     const none__syscall : syscall_t.
     ```
  *)
  [ TComment "Predefined types"
  ; TTypeDecl param_data_ident
  ; TTypeDecl proc_t_ident
  ; TTypeDecl acc_data_t_ident
  ; TTypeDecl syscall_t_ident
  ; TFree (attacker_channel_ident, channel_ident, [])
  ; TComment "Tables"
  ; TTableDecl
      (access_control_table_ident, [proc_t_ident; acc_data_t_ident; syscall_t_ident])
  ; TTableDecl
      (file_type_table_ident, [proc_t_ident; acc_data_t_ident; bitstring_ident])
  ; TTableDecl (channel_table_ident, [acc_data_t_ident; channel_ident])
  ; TTableDecl (deleted_address_table_ident, [bitstring_ident])
  ; TComment "Pattern which matches with any system call"
  ; TConstDecl (none_syscall_ident, syscall_t_ident, [])
  ; TComment "Booleans"
  ; TConstDecl (true_ident, bitstring_ident, [])
  ; TConstDecl (false_ident, bitstring_ident, [])
  ]

let compile_string_consts (genv : GEnv.t) : tdecl list =
  (*
     3.1 Encoding Strings, Constants, Events and Function Declarations

     ```
     put [ ch :: msg("hello world") ]
     ```

     ```
     const hello_world__str : bitstring.
     ...
     out(ch, msg(hello_world__str))
     ```
  *)
  List.concat_map (fun (literal, id) ->
      [ TComment (Printf.sprintf "String constant %S" literal)
      ; TConstDecl (id, bitstring_ident, []) ]) (GEnv.strings genv)

let compile_integer_consts (genv : GEnv.t) : tdecl list =
  List.concat_map
    (fun (value, id) ->
       [ TComment (Printf.sprintf "Integer constant %d" value)
       ; TConstDecl (id, bitstring_ident, []) ])
    (GEnv.integers genv)

let compile_parameter_consts (genv : GEnv.t) : tdecl list =
  List.concat_map
    (fun (value, id) ->
       [ TComment (Printf.sprintf "Parameter value %s" value)
       ; TConstDecl (id, param_data_ident, []) ])
    (GEnv.parameters genv)

let compile_syscall_consts (genv : GEnv.t) : tdecl list =
  (*
     3.2 Encoding Process Types, Channel types, File types, and Access Control Policies
     3.9 Syscall and Attack Encoding

     ```
     syscall send(c, v) { ... }
     passive attack eaves_mem(v) { ... }
     ```

     ```
     const send__0__syscall : syscall_t.
     const eaves_mem__0__syscall : syscall_t.
     ```
  *)
  List.concat_map (fun (id, def) ->
      let kind = if def.passive then "passive attack" else "syscall" in
      [ TComment (Printf.sprintf "%s %s(..)" kind (Ident.to_string id))
      ; TConstDecl (def.pv_id, syscall_t_ident, [])
      ]) (GEnv.syscalls genv)

let compile_event_decls (genv : GEnv.t) : tdecl list =
  (*
     3.1 Encoding Strings, Constants, Events and Function Declarations
     3.12 Encoding Properties

     ```
     event [:: ImgSend(image)]
     lemma Reachable : reachable ::ImgSend(image)
     ```

     ```
     event ImgSend(bitstring).
     query image:bitstring; event(ImgSend(image)).
     ```
  *)
  let named_events =
    List.concat_map (fun (name, (kind, types)) ->
        let source_name =
          match kind with
          | Global -> "::" ^ name
          | Plain -> name
        in
        [ TComment (Printf.sprintf "Event declaration %s(..)" source_name)
        ; TEventDecl (compile_event_name name kind, List.map compile_value_type types)
        ]) (GEnv.events genv)
  in
  let comparison_events =
    List.concat_map
      (fun (kind, typ) ->
         let source_name =
           match kind with
           | Equality -> "equation fact"
           | Inequality -> "inequality fact"
         in
         [ TComment (Printf.sprintf "Event declaration for %s" source_name)
         ; TEventDecl
             ( compile_comparison_event_name kind
             , [compile_value_type typ; compile_value_type typ] )
         ])
      (GEnv.comparison_events genv)
  in
  named_events @ comparison_events

let compile_channel_fact_decls (genv : GEnv.t) : tdecl list =
  List.concat_map
    (fun (name, types) ->
       [ TComment (Printf.sprintf "Channel fact declaration %s(..)" name)
       ; TFunDecl
           ( compile_name name "chan"
           , List.map compile_value_type types
           , bitstring_ident
           , [pv_ident "data", None] )
       ])
    (GEnv.channel_facts genv)

(* 3.4 Encoding Structured facts, new, let, delete

   ```
   new x := Struct(x1, ..., xn)
   ```

   ```
   fun Struct ( bitstring , ... , bitstring ) : bitstring [ data ] .
   reduc forall x_0 : bitstring , ... , x_n : bitstring ;
     Struct__struct_addr ( Struct__struct ( x_0 , ... , x_n ) = x_0 .
   reduc forall x_0 : bitstring , ... , x_n : bitstring ;
     Struct__struct_par_1 ( Struct__struct ( x_0 , ... , x_n ) = x_1 .
   reduc forall x_0 : bitstring , ... , x_n : bitstring ;
     Struct__struct_par_n ( Struct__struct ( x_0 , ... , x_n ) = x_n .
   ...
   ```
*)
let compile_structure_decls (genv : GEnv.t) : tdecl list =
  (* Note: structure constructors/getters are generated globally from observed
     Rabbit structure usages. This assumes there is no conflicting user-level
     ProVerif declaration with the same generated names and that a per-name
     arity discipline is enough. If the surrounding language grows richer
     namespaces or imported declarations, this generation scheme may need to be
     made more explicit. *)
  let mk_var index = pv_ident (Printf.sprintf "x_%d" index) in
  let compile_structure_fact name ftys =
    let arity = List.length ftys in
    let envdecl =
      (mk_var 0, bitstring_ident) ::
      List.mapi (fun i fty -> mk_var (i+1), compile_value_type fty) ftys
    in
    let vars =
      List.map (fun (id, _ty) -> term_e @@ PIdent id) envdecl
    in
    let struct_term =
      (* Struct(x_0, ..., x_n) *)
      term_e @@ PFunApp (structure_ctor_ident name, vars)
    in
    let ctor_decl =
      (* fun Struct (bitstring, ..., bitstring) : bitstring[data]. *)
      TFunDecl
        ( structure_ctor_ident name
        , bitstring_ident :: List.map compile_value_type ftys
        , bitstring_ident
        , [pv_ident "data", None] )
    in
    let addr_decl =
      (* reduc forall x_0:bitstring, ..., x_n:bitstring;
           Struct__struct_addr(Struct__struct(x_0, ..., x_n) = x_0.
      *)
      TReduc
        ( [ envdecl
          , EETerm
              (term_e @@
               PFunApp
                 ( pv_ident "="
                 , [ term_e @@ PFunApp (structure_addr_ident name, [struct_term])
                   ; List.nth vars 0
                   ] ))
          ]
        , [] )
    in
    let arg_decls =
      (* reduc forall x_0:bitstring, ..., x_n:bitstring;
           Struct__struct_par_i(Struct__struct(x_0, ..., x_n) = x_i.
      *)
      List.init arity
        (fun index ->
           TReduc
             ( [ envdecl
               , EETerm
                   (term_e @@
                    PFunApp
                      ( pv_ident "="
                      , [ term_e @@ PFunApp (structure_arg_ident name (index + 1), [struct_term])
                        ; List.nth vars (index + 1)
                        ] ))
               ]
             , [] ))
    in
    TComment (Printf.sprintf "Structure declaration %s(%s)"
                name (String.concat "," @@ List.init arity (fun _ -> "_"))) ::
    ctor_decl :: addr_decl :: arg_decls
  in
  Env.facts (GEnv.tyenv genv) |>
  List.concat_map @@ function
  | (name, (Env.Structure, Some ftys)) ->
      compile_structure_fact name ftys
  | (name, (Env.Structure, None)) ->
      Error.internal ~loc:Location.nowhere "Structure %s lacks field type information" name
  | _ -> []

(*
   3.2 Encoding Process Types, Channel types, File types, and Access Control Policies

   ```
   allow client_t udp_t [send]
   allow client_t readonly_t [.]
   ```

   ```
   insert access_control_table(client_t, udp_t, send__0__syscall);
   insert access_control_table(client_t, readonly_t, none__syscall);
   ...
   ```
*)
let add_allow_inits (genv : GEnv.t) (body : tprocess_e) : tprocess_e =
  List.fold_right
    (fun entry acc ->
       add_comment
         (Printf.sprintf "allow %s %s [%s]"
            (Ident.to_string entry.rabbit_process_type)
            (Ident.to_string entry.rabbit_target_type)
            (match entry.rabbit_syscall with Some s -> Ident.to_string s | None -> ".")) @@
       process_e @@
         PInsert
            ( access_control_table_ident
            , [ pterm_e @@ PPIdent entry.pv_process_type
              ; pterm_e @@ PPIdent entry.pv_target_type
              ; (* Rabbit [.] permits direct access outside a syscall. Since
                   ProVerif table entries require a concrete [syscall_t], encode
                   that case with the distinguished [none__syscall] constant.
                   This encoding choice is not specified in Section 3.2. *)
                pterm_e @@ PPIdent
                  (Option.value entry.pv_syscall ~default:none_syscall_ident)
              ]
            , acc ))
    (List.rev (GEnv.allow_entries genv))
    body

let rec compile_decl (env : Env.t) genv (decl : T.decl) : tdecl list =
  let loc = decl.loc in
  match decl.desc with
  | Syscall _ | Attack _ | AllowAttack _ ->
      (* They are handled by `collect_decl` *)
      []
  | Function { id; typ } ->
      compile_function ~loc id typ
  | Equation (lhs, rhs) ->
      compile_equation ~loc genv lhs rhs
  | Type { id; typclass } ->
      compile_type ~loc id typclass
  | Allow { process_typ; target_typs; syscalls } ->
      compile_allow ~loc genv process_typ target_typs syscalls
  | Init { id; desc } ->
      compile_init ~loc genv id desc
  | Channel { id; param; typ } ->
      compile_channel ~loc id param typ
  | Process { id; param; args; typ; files; vars; funcs; main } ->
      let process_decls =
        compile_process genv ~loc id param args typ files vars funcs main
      in
      GEnv.take_auxiliary_decls genv @ process_decls
  | System (procs, lemmas) ->
      compile_system ~loc genv procs lemmas
  | Load (filename, decls) ->
      compile_load env genv filename decls

(* `load` simply expands its declaration. *)
and compile_load (env : Env.t) genv (filename : string) (decls : T.decl list) : tdecl list =
  TComment (Printf.sprintf "Load %s" filename) ::
  List.concat_map (compile_decl env genv) decls

let rec warn_cmd (cmd : T.cmd) =
  let warn_case (case : T.case) = warn_cmd case.cmd in
  match cmd.desc with
  | Event (_ :: _ :: _ as facts) ->
      Print.message ~loc:cmd.loc "Warning"
        "event [...] contains %d facts; ProVerif emits them sequentially and cannot preserve their simultaneous occurrence"
        (List.length facts)
  | Sequence (lhs, rhs) ->
      warn_cmd lhs;
      warn_cmd rhs
  | Let (_, _, body) | New (_, _, body) | Get (_, _, _, body) ->
      warn_cmd body
  | Case cases ->
      List.iter warn_case cases
  | While (repeat_cases, until_cases) ->
      List.iter warn_case repeat_cases;
      List.iter warn_case until_cases
  | Skip | Put _ | Assign _ | Event _ | Expr _ | Del _ -> ()

let rec warn_decl (decl : T.decl) =
  match decl.desc with
  | Syscall { cmd; _ } | Attack { cmd; _ } ->
      warn_cmd cmd
  | Process { funcs; main; _ } ->
      List.iter (fun (_, _, cmd) -> warn_cmd cmd) funcs;
      warn_cmd main
  | Load (_, decls) ->
      List.iter warn_decl decls
  | Function _ | Equation _ | Type _ | Allow _ | AllowAttack _ | Init _
  | Channel _ | System _ -> ()

let compile_program (env : Env.t) (decls : T.decl list) : Pv_parser.program =
  List.iter warn_decl decls;
  let genv = GEnv.create env in
  List.iter (GEnv.add_decl_strings genv) decls;
  List.iter (collect_decl genv) decls;
  let body = List.concat_map (compile_decl env genv) decls in
  let top_process = Option.value (GEnv.top_process genv) ~default:(process_e PNil) in
  let top_process = add_allow_inits genv top_process in
  ( compile_prelude genv
    @ compile_structure_decls genv
    @ compile_channel_fact_decls genv
    @ compile_syscall_consts genv
    @ compile_event_decls genv
    @ compile_string_consts genv
    @ compile_integer_consts genv
    @ compile_parameter_consts genv
    @ [ TComment "Body" ]
    @ body
    @ [ TComment "System" ]
  , top_process
  , None )
