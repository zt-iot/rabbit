open Rabbit_proverif_pv_parse
open Pitptree
include Proverif_compiler_support

type syscall_def =
  { pv_id : ident (** Proverif id *)
  ; args : T.ident list
  ; cmd : T.cmd
  }

type attack_def =
  { syscall : T.ident (** Target id *)
  ; args : T.ident list
  ; cmd : T.cmd
  }

type allow_entry =
  { rabbit_process_type : T.ident
  ; rabbit_target_type : T.ident
  ; rabbit_syscall : T.ident option
  ; pv_process_type : ident
  ; pv_target_type : ident
  ; pv_syscall : ident
  }

module GEnv = struct

  type t =
    { mutable strings        : (string * ident) list (** string constants and their identifiers *)
    ; mutable syscalls       : (Ident.t * syscall_def) list (** system calls and definitions *)
    ; mutable attacks        : (Ident.t * attack_def) list (** attacks and definitions *)
    ; allow_attack_table     : (Ident.t, T.ident list) Hashtbl.t (** process type and allowed attacks *)
    ; generated_name_counter : (string, int) Hashtbl.t (** Name resolver state *)
    ; mutable allow_entries  : allow_entry list
    ; mutable process_types  : (Ident.t * ident) list (** process types in Rabbit and Proverif *)
    ; mutable structures     : (Name.t * int) list (** structure name and arity *)
    ; mutable events         : (string * int) list (** event name and arity *)
    ; mutable top_process    : tprocess_e option
    }

  let create () : t =
    { strings                = []
    ; syscalls               = []
    ; attacks                = []
    ; allow_attack_table     = Hashtbl.create 101
    ; generated_name_counter = Hashtbl.create 101
    ; allow_entries          = []
    ; process_types          = []
    ; structures             = []
    ; events                 = []
    ; top_process            = None
    }

  let add_allow_entry genv entry =
    genv.allow_entries <- entry :: genv.allow_entries

  let add_allowed_attacks genv process_typ attacks =
    let previous =
      match Hashtbl.find_opt genv.allow_attack_table process_typ with
      | None -> []
      | Some previous -> previous
    in
    Hashtbl.replace genv.allow_attack_table process_typ (previous @ attacks)

  let allow_entries genv = genv.allow_entries
  let strings genv = genv.strings
  let syscalls genv = genv.syscalls
  let structures genv = genv.structures
  let events genv = genv.events
  let top_process genv = genv.top_process
  let set_top_process genv process = genv.top_process <- Some process

  let register_with_arity kind get_entries set_entries ~loc genv (name : T.name) (arity : int) =
    let entries = get_entries genv in
    match List.assoc_opt name entries with
    | None -> set_entries genv (entries @ [name, arity])
    | Some arity' when arity' = arity -> ()
    | Some arity' ->
        Error.invalid_input ~loc
          "%s %s is used with inconsistent arities (%d and %d)"
          kind name arity' arity

  let register_syscall ~loc:_ genv id def =
    genv.syscalls <- (id, def) :: genv.syscalls

  let register_attack_def ~loc:_ genv id def =
    genv.attacks <- (id, def) :: genv.attacks

  let register_structure =
    register_with_arity
      "Structure"
      (fun genv -> genv.structures)
      (fun genv structures -> genv.structures <- structures)

  let register_event =
    register_with_arity
      "Event"
      (fun genv -> genv.events)
      (fun genv events -> genv.events <- events)

  let register_process_type ~loc genv (process_id : T.ident) (typ : T.ident) =
    match List.assoc_opt process_id genv.process_types with
    | Some _ ->
        Error.invalid_input ~loc "Process %s is already defined"
          (Ident.to_string process_id)
    | None ->
        genv.process_types <- (process_id, compile_ident typ) :: genv.process_types

  let find_process_type ~loc genv (process_id : T.ident) : ident =
    match List.assoc_opt process_id genv.process_types with
    | Some typ -> typ
    | None ->
        Error.internal ~loc
          "process type for %s is not available in ProVerif system translation"
          (Ident.to_string process_id)

  let find_syscall_def genv (id : T.ident) : syscall_def option =
    List.assoc_opt id genv.syscalls

  let find_allowed_attacks
      ~loc
      genv
      ~(process_typ_id : T.ident)
      ~(syscall_id : T.ident)
    : attack_def list =
    let allowed =
      match Hashtbl.find_opt genv.allow_attack_table process_typ_id with
      | None -> []
      | Some ids -> ids
    in
    List.filter_map
      (fun attack_id ->
         match List.assoc_opt attack_id genv.attacks with
         | Some def when def.syscall = syscall_id -> Some def
         | _ ->
             Error.internal ~loc "Attack %s has no definition"
               (Ident.to_string attack_id))
      allowed

  (* Propose a variable name for a string constant *)
  let sanitize_string_for_ident s =
    let sanitized =
      s
      |> Str.global_replace (Str.regexp "[^A-Za-z0-9_]+") "_"
      |> Str.global_replace (Str.regexp "_+") "_"
      |> Str.global_replace (Str.regexp "^_\\|_$") ""
    in
    if sanitized = "" then
      "empty"
    else
      sanitized

  let register_ident genv ~base : ident =
    (* make sure `base` does not end with `_g[0-9]+` *)
    let base =
      if Str.string_match (Str.regexp ".*_g[0-9]+$") base 0 then
        base ^ "_"
      else
        base
    in
    match Hashtbl.find_opt genv.generated_name_counter base with
    | None ->
        Hashtbl.add genv.generated_name_counter base 1;
        pv_ident base
    | Some i ->
        Hashtbl.replace genv.generated_name_counter base (i+1);
        pv_ident (Printf.sprintf "%s_g%d" base i)

  (* "hello" -> "hello_str" *)
  let register_string genv s =
    match List.assoc_opt s genv.strings with
    | Some _ -> ()
    | None ->
        let base = sanitize_string_for_ident s ^ "_str" in
        let id = register_ident genv ~base in
        genv.strings <- genv.strings @ [s, id]

  let fresh_string_ident genv s : ident =
    register_string genv s;
    match List.assoc_opt s genv.strings with
    | Some id -> id
    | None -> assert false

  (* "name" -> "name_s" *)
  let fresh_syscall_ident ~loc genv (id : T.ident) : ident =
    let name = Ident.to_string id in
    match List.assoc_opt id genv.syscalls with
    | Some _ ->
        Error.invalid_input ~loc "Syscall %s is already defined" (Ident.to_string id)
    | None ->
        let base = sanitize_string_for_ident name ^ "_s" in
        let syscall_ident = register_ident genv ~base in
        syscall_ident

  let rec register_expr_strings genv (expr : T.expr) =
    match expr.desc with
    | Ident { param; _ } -> Option.iter (register_expr_strings genv) param
    | Apply (_, args) | Tuple args -> List.iter (register_expr_strings genv) args
    | String s -> register_string genv s
    | Boolean _ | Integer _ | Float _ | Unit -> ()

  let register_fact_strings genv (fact : T.fact) =
    match fact.desc with
    | Channel { channel; args; _ } ->
        register_expr_strings genv channel;
        List.iter (register_expr_strings genv) args
    | Plain (_name, args) | Global (_name, args) ->
        List.iter (register_expr_strings genv) args
    | Eq (lhs, rhs) | Neq (lhs, rhs) ->
        register_expr_strings genv lhs;
        register_expr_strings genv rhs
    | File { path; contents } ->
        register_expr_strings genv path;
        register_expr_strings genv contents

  let rec register_cmd_strings genv (cmd : T.cmd) =
    match cmd.desc with
    | Skip -> ()
    | Sequence (lhs, rhs) ->
        register_cmd_strings genv lhs;
        register_cmd_strings genv rhs
    | Put facts | Event facts -> List.iter (register_fact_strings genv) facts
    | Let (_id, expr, body) ->
        register_expr_strings genv expr;
        register_cmd_strings genv body
    | Assign (_, expr) | Return expr | Del (expr, _) ->
        register_expr_strings genv expr
    | Case cases -> List.iter (register_case_strings genv) cases
    | While (repeat_cases, until_cases) ->
        List.iter (register_case_strings genv) repeat_cases;
        List.iter (register_case_strings genv) until_cases
    | New (_id, value, body) ->
        Option.iter
          (fun (_name, args) -> List.iter (register_expr_strings genv) args)
          value;
        register_cmd_strings genv body
    | Get (_ids, expr, _name, body) ->
        register_expr_strings genv expr;
        register_cmd_strings genv body

  and register_case_strings genv ({ facts; cmd; _ } : T.case) =
    List.iter (register_fact_strings genv) facts;
    register_cmd_strings genv cmd

  let register_proc_strings genv (proc : T.proc) =
    let { T.parameter; args; _ } = proc.data in
    Option.iter (register_expr_strings genv) parameter;
    List.iter
      (fun ({ parameter; _ } : T.chan_arg) ->
         Option.iter (Option.iter (register_expr_strings genv)) parameter)
      args

  let register_proc_group_strings genv = function
    | T.Unbounded proc -> register_proc_strings genv proc
    | Bounded (_id, procs) -> List.iter (register_proc_strings genv) procs

  let register_lemma_strings genv (_id, lemma : T.ident * T.lemma) =
    match lemma.desc with
    | Plain _ -> ()
    | Reachability { facts; _ } -> List.iter (register_fact_strings genv) facts
    | Correspondence { premise; conclusion; _ } ->
        register_fact_strings genv premise;
        register_fact_strings genv conclusion

  let rec register_decl_strings genv (decl : T.decl) =
    match decl.desc with
    | Equation (lhs, rhs) ->
        register_expr_strings genv lhs;
        register_expr_strings genv rhs
    | Syscall { cmd; _ } | Attack { cmd; _ } -> register_cmd_strings genv cmd
    | Init { desc = Value expr; _ }
    | Init { desc = Value_with_param (_, expr); _ } ->
        register_expr_strings genv expr
    | Process { files; vars; funcs; main; _ } ->
        List.iter
          (fun (path, _typ, contents) ->
             register_expr_strings genv path;
             register_expr_strings genv contents)
          files;
        List.iter (fun (_id, expr) -> register_expr_strings genv expr) vars;
        List.iter (fun (_id, _args, cmd) -> register_cmd_strings genv cmd) funcs;
        register_cmd_strings genv main
    | System (procs, lemmas) ->
        List.iter (register_proc_group_strings genv) procs;
        List.iter (register_lemma_strings genv) lemmas
    | Load (_filename, decls) -> List.iter (register_decl_strings genv) decls
    | Function _ | Type _ | Allow _ | AllowAttack _
    | Init { desc = Fresh | Fresh_with_param; _ } | Channel _ -> ()

end

module PEnv = struct

  type t =
    { bindings : (T.ident * pterm_e) list
    ; local_func_defs : (T.ident * (T.ident list * T.cmd)) list
    ; process_typ_id : T.ident option
    ; proc_type : pterm_e
    ; curr_syscall : pterm_e option
    ; file_channel : pterm_e option
    ; return_cont : (pterm_e -> tprocess_e) option
    }

  let create_process_env
      ~(local_func_defs : (T.ident * (T.ident list * T.cmd)) list)
      ~(process_typ_id : T.ident option)
      ~(proc_type : pterm_e)
      ~(curr_syscall : pterm_e option)
      ~(file_channel : pterm_e option)
    : t =
    { bindings = []
    ; local_func_defs
    ; process_typ_id
    ; proc_type
    ; curr_syscall
    ; file_channel
    ; return_cont = None
    }

  let bind_process_var (penv : t) (id : T.ident) (value : pterm_e) =
    { penv with bindings = (id, value) :: List.remove_assoc id penv.bindings }

  let bindings penv = penv.bindings
  let process_typ_id penv = penv.process_typ_id
  let proc_type penv = penv.proc_type
  let curr_syscall penv = penv.curr_syscall
  let file_channel penv = penv.file_channel
  let return_cont penv = penv.return_cont
  let with_curr_syscall penv curr_syscall = { penv with curr_syscall }

  let find_process_var penv (id : T.ident) : pterm_e option =
    List.assoc_opt id penv.bindings

  let find_process_var_exn ~loc penv (id : T.ident) : pterm_e =
    match find_process_var penv id with
    | Some value -> value
    | None ->
        Error.internal ~loc "Loop-carried variable %s is not available"
          (Ident.to_string id)

  let restore_process_vars
      penv
      (saved : (T.ident * pterm_e option) list)
    : t =
    List.fold_left
      (fun penv (id, old_value) ->
         match old_value with
         | Some value -> bind_process_var penv id value
         | None -> { penv with bindings = List.remove_assoc id penv.bindings })
      penv
      saved

  let with_process_return_cont
      (penv : t)
      (return_cont : pterm_e -> tprocess_e)
    : t =
    { penv with return_cont = Some return_cont }

  let find_local_func_def penv (id : T.ident)
    : (T.ident list * T.cmd) option =
    List.assoc_opt id penv.local_func_defs

end
