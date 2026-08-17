module T = Typed
open Rabbit_proverif_pv_parse
open Pitptree

module Error = struct
  type error =
    | Unsupported of string
    | Invalid_input of string
    | Internal_error of string

  exception Error of error Location.located

  let _error ~loc err = Stdlib.raise (Error (Location.locate ~loc err))

  let _error_ex ex ~loc fmt = Printf.ksprintf (fun s -> _error ~loc (ex s)) fmt

  let unsupported ~loc fmt = _error_ex (fun s -> Unsupported s) ~loc fmt
  let invalid_input ~loc fmt = _error_ex (fun s -> Invalid_input s) ~loc fmt
  let internal ~loc fmt = _error_ex (fun s -> Internal_error s) ~loc fmt

  let print_error err ppf =
    match err with
    | Unsupported s -> Format.pp_print_string ppf s
    | Invalid_input s -> Format.pp_print_string ppf s
    | Internal_error s -> Format.pp_print_string ppf s
end

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

let with_dummy_ident_ext x = x, Parsing_helper.dummy_ext

let with_dummy_node_ext x = x, Parsing_helper.dummy_ext, []

let pv_ident (s : string) : ident = with_dummy_ident_ext s

let compile_ident (id : T.ident) : ident = pv_ident (Ident.to_string id)

let bitstring_ident             = pv_ident "bitstring"
let channel_ident               = pv_ident "channel"
let param_data_ident            = pv_ident "param_data"
let proc_t_ident                = pv_ident "proc_t"
let acc_data_t_ident            = pv_ident "acc_data_t"
let syscall_t_ident             = pv_ident "syscall_t"
let access_control_table_ident  = pv_ident "access_control_table"
let file_type_table_ident       = pv_ident "file_type_table"
let channel_table_ident         = pv_ident "channel_table"
let deleted_address_table_ident = pv_ident "deleted_address_table"
let attacker_channel_ident      = pv_ident "attacker"
let true_ident                  = pv_ident "true"
let false_ident                 = pv_ident "false"
let ptype_arg_ident             = pv_ident "ptype"
let none_syscall_ident          = pv_ident "none_syscall_s"
let precise_ident               = pv_ident "precise"
let term_e    (t : term)     : term_e     = with_dummy_node_ext t
let pterm_e   (t : pterm)    : pterm_e    = with_dummy_node_ext t
let gterm_e   (t : gterm)    : gterm_e    = with_dummy_node_ext t
let process_e (p : tprocess) : tprocess_e = with_dummy_node_ext p
let tquery_e  (q : tquery)   : tquery_e   = with_dummy_node_ext q

let add_comment c (a, b, comments) = (a, b, c :: comments)

let compile_name (name : T.name) : ident = pv_ident name

(* "Struct" for "Struct" *)
let structure_ctor_ident (name : T.name) : ident =
  compile_name name

(* "StructAddr" for "Struct" *)
let structure_addr_ident (name : T.name) : ident =
  pv_ident (name ^ "Addr")

(* "StructPar1" for "Struct" and 1 *)
let structure_arg_ident (name : T.name) (index : int) : ident =
  pv_ident (Printf.sprintf "%sPar%d" name index)

module Int : sig
  val to_term_e : int -> term_e
  val to_pterm_e : int -> pterm_e
  val to_gterm_e : int -> gterm_e
end = struct
  let zero_term_e () : term_e = term_e @@ PIdent (pv_ident "0")
  let zero_pterm_e () : pterm_e = pterm_e @@ PPIdent (pv_ident "0")
  let zero_gterm_e () : gterm_e = gterm_e @@ PGIdent (pv_ident "0")

  let rec unfold (t : term_e) (n : int) : term_e =
    match n with
    | 0 -> t
    | n ->
        term_e @@ PFunApp (pv_ident "+", [unfold t (n - 1)])

  let unfold_minus (t : term_e) (n : int) : term_e =
    match n with
    | 0 -> t
    | n ->
        term_e @@ PFunApp (pv_ident ("- " ^ string_of_int n), [t])

  let rec unfold_pterm (t : pterm_e) (n : int) : pterm_e =
    match n with
    | 0 -> t
    | n ->
        pterm_e @@ PPFunApp (pv_ident "+", [unfold_pterm t (n - 1)])

  let unfold_minus_pterm (t : pterm_e) (n : int) : pterm_e =
    match n with
    | 0 -> t
    | n ->
        pterm_e @@ PPFunApp (pv_ident ("- " ^ string_of_int n), [t])

  let rec unfold_gterm (t : gterm_e) (n : int) : gterm_e =
    match n with
    | 0 -> t
    | n ->
        gterm_e @@ PGFunApp (pv_ident "+", [unfold_gterm t (n - 1)], None)

  let unfold_minus_gterm (t : gterm_e) (n : int) : gterm_e =
    match n with
    | 0 -> t
    | n ->
        gterm_e @@ PGFunApp (pv_ident ("- " ^ string_of_int n), [t], None)

  let to_term_e (n : int) : term_e =
    if n >= 0 then
      unfold (zero_term_e ()) n
    else
      (* Negative integer -n is represented as `0 - n` *)
      unfold_minus (zero_term_e ()) (-n)

  let to_pterm_e (n : int) : pterm_e =
    if n >= 0 then
      unfold_pterm (zero_pterm_e ()) n
    else
      unfold_minus_pterm (zero_pterm_e ()) (-n)

  let to_gterm_e (n : int) : gterm_e =
    if n >= 0 then
      unfold_gterm (zero_gterm_e ()) n
    else
      unfold_minus_gterm (zero_gterm_e ()) (-n)
end

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

let rec compile_expr_to_term genv (expr : T.expr) : term_e =
  term_e @@ match expr.desc with
  | T.Ident { id; param = Some param; _ } ->
      PFunApp (compile_ident id, [compile_expr_to_term genv param])
  | T.Ident { id; _ } ->
      PIdent (compile_ident id)
  | Apply (id, args) ->
      PFunApp (compile_ident id, List.map (compile_expr_to_term genv) args)
  | Tuple exprs ->
      PTuple (List.map (compile_expr_to_term genv) exprs)
  | Unit ->
      PTuple []
  | String s ->
      PIdent (GEnv.fresh_string_ident genv s)
  | Boolean true ->
      PIdent (pv_ident "true")
  | Boolean false ->
      PIdent (pv_ident "false")
  | Integer n ->
      let term, _, _ = Int.to_term_e n in
      term
  | Float _ ->
      Error.unsupported ~loc:expr.loc
        "Float terms are not supported in ProVerif term translation"

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

  let find_process_var penv (id : T.ident) : pterm_e option =
    List.assoc_opt id penv.bindings

  let find_process_var_exn ~loc penv (id : T.ident) : pterm_e =
    match find_process_var penv id with
    | Some value -> value
    | None ->
        Error.internal ~loc "Loop-carried variable %s is not available"
          (Ident.to_string id)

  let unbind_process_var (penv : t) (id : T.ident) =
    { penv with bindings = List.remove_assoc id penv.bindings }

  let restore_process_var penv (id : T.ident) (old_value : pterm_e option) =
    match old_value with
    | Some value -> bind_process_var penv id value
    | None -> unbind_process_var penv id

  let restore_process_vars
      penv
      (saved : (T.ident * pterm_e option) list)
    : t =
    List.fold_left
      (fun penv (id, old_value) -> restore_process_var penv id old_value)
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

let rec compile_expr_to_gterm genv (expr : T.expr) : gterm_e =
  gterm_e @@
  match expr.desc with
  | T.Ident { id; param = Some param; _ } ->
      PGFunApp
        (compile_ident id, [compile_expr_to_gterm genv param], None)
  | Ident { id; param = None; _ } ->
      PGIdent (compile_ident id)
  | Apply (id, args) ->
      PGFunApp
        (compile_ident id, List.map (compile_expr_to_gterm genv) args, None)
  | Tuple exprs ->
      PGTuple (List.map (compile_expr_to_gterm genv) exprs)
  | Unit ->
      PGTuple []
  | String s ->
      PGIdent (GEnv.fresh_string_ident genv s)
  | Boolean true ->
      PGIdent true_ident
  | Boolean false ->
      PGIdent false_ident
  | Integer n ->
      let term, _, _ = Int.to_gterm_e n in
      term
  | Float _ ->
      Error.unsupported ~loc:expr.loc
        "Float terms are not supported in ProVerif query translation"

let rec compile_expr_to_pterm genv penv (expr : T.expr) : pterm_e =
  pterm_e @@
  match expr.desc with
  | T.Ident { id; param = Some param; _ } ->
      PPFunApp (compile_ident id, [compile_expr_to_pterm genv penv param])
  | Ident { id; param = None; _ } ->
      (match PEnv.find_process_var penv id with
       | Some value ->
           let term, _, _ = value in
           term
       | None -> PPIdent (compile_ident id))
  | Apply (id, args) ->
      PPFunApp (compile_ident id, List.map (compile_expr_to_pterm genv penv) args)
  | Tuple exprs ->
      PPTuple (List.map (compile_expr_to_pterm genv penv) exprs)
  | Unit ->
      PPTuple []
  | String s ->
      PPIdent (GEnv.fresh_string_ident genv s)
  | Boolean true ->
      PPIdent true_ident
  | Boolean false ->
      PPIdent false_ident
  | Integer n ->
      let term, _, _ = Int.to_pterm_e n in
      term
  | Float _ ->
      Error.unsupported ~loc:expr.loc
        "Float process terms are not supported in ProVerif process translation"

let current_syscall ~loc (penv : PEnv.t) : pterm_e =
  match penv.curr_syscall with
  | Some syscall -> syscall
  | None ->
      Error.internal ~loc
        "Current syscall is not available for access-control lowering"

let ppar
    (proc1 : tprocess_e)
    (proc2 : tprocess_e)
  : tprocess_e =
  process_e @@ PPar (proc1, proc2)

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
      let choice_id = pv_ident "rabbit_attack_choice_ch" in
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
    ~loc
    (penv : PEnv.t)
    (target_type : pterm_e)
    (then_proc : tprocess_e)
    (else_proc : tprocess_e)
  : tprocess_e =
  (* No spec for allow ... [.] *)
  (* Note: this assumes direct Rabbit accesses are mediated solely by the
     triple (current process type, target access-data type, current syscall).
     The current lowering uses [none_syscall_s] for direct process code via
     [allow ... [.]]. If the spec ends up distinguishing more direct-access
     contexts, this table lookup may need refinement. *)
  process_e @@
  PGet
    ( access_control_table_ident
    , [ PPatEqual penv.proc_type
      ; PPatEqual target_type
      ; PPatEqual (current_syscall ~loc penv)
      ]
    , None
    , then_proc
    , else_proc
    , [] )

let wrap_with_channel_access_get
    ~loc
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
    , wrap_with_access_control_get ~loc penv channel_type_term then_proc else_proc
    , else_proc
    , [] )

let wrap_with_file_access_get
    ~loc
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
    , [ PPatEqual penv.proc_type
      ; PPatVar (compile_ident file_type_id, Some acc_data_t_ident)
      ; PPatEqual path_term
      ]
    , None
    , wrap_with_access_control_get ~loc penv file_type_term then_proc else_proc
    , else_proc
    , [] )

let structure_addr_term (name : T.name) (struct_term : pterm_e) : pterm_e =
  pterm_e @@ PPFunApp (structure_addr_ident name, [struct_term])

let structure_arg_term (name : T.name) (index : int) (struct_term : pterm_e) : pterm_e =
  pterm_e @@ PPFunApp (structure_arg_ident name index, [struct_term])

let loop_state_bindings (penv : PEnv.t) : (T.ident * pterm_e) list =
  (* Note: the first loop lowering conservatively carries every current
     process binding across the loop boundary. This is simple and sounder than
     forgetting mutable state, but it may be larger than necessary. A later
     refinement could compute the true loop-carried live subset. *)
  List.rev penv.bindings

let loop_state_message
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

let loop_state_pattern
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

let bind_loop_state
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
      GEnv.register_event ~loc genv name (List.length args);
      process_e @@
      PEvent
        ( compile_name name
        , List.map (compile_expr_to_pterm genv penv) args
        , None
        , body )
  | Plain (name, args) ->
      GEnv.register_event ~loc genv name (List.length args);
      process_e
      @@ PEvent
        ( compile_name name
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
      let channel_term = compile_expr_to_pterm genv penv channel in
      let payload =
        pterm_e @@
        PPFunApp
          ( compile_name name
          , List.map (compile_expr_to_pterm genv penv) args )
      in
      wrap_with_channel_access_get ~loc channel_term penv
        (ppar (process_e @@ POutput (channel_term, payload, process_e PNil)) body)
        (process_e PNil)
  | File { path; contents } ->
      let path_term = compile_expr_to_pterm genv penv path in
      let contents_term = compile_expr_to_pterm genv penv contents in
      let file_channel =
        match penv.file_channel with
        | Some file_channel -> file_channel
        | None ->
            Error.internal ~loc
              "File output requires a process-local file channel"
      in
      let payload = pterm_e @@ PPTuple [path_term; contents_term] in
      wrap_with_file_access_get ~loc path_term penv
        (ppar (process_e @@ POutput (file_channel, payload, process_e PNil)) body)
        (process_e PNil)
  | Global ("Out", [arg]) ->
      process_e @@ POutput (pterm_e @@ PPIdent attacker_channel_ident, compile_expr_to_pterm genv penv arg, body)
  | Global (name, args) ->
      GEnv.register_event ~loc genv name (List.length args);
      process_e @@
      PEvent
        ( compile_name name
        , List.map (compile_expr_to_pterm genv penv) args
        , None
        , body )
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
    (then_proc : tprocess_e)
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
  | [] -> then_proc
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
             match penv.file_channel with
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
           wrap_with_file_access_get ~loc:fact.loc path_term branch_env
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
  | KRestoreVar of T.ident * pterm_e option * kont
  | KRestoreVars of (T.ident * pterm_e option) list * kont
  | KLoopOutput of bool * Location.t * pterm_e * T.ident list

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
    ~loc
    ~(else_proc : tprocess_e)
  : tprocess_e =
  let payload_vars =
    List.init (List.length args) (fun i -> Ident.local (Printf.sprintf "case_arg_%d" i))
  in
  let payload_patterns =
    List.map
      (fun id -> PPatVar (compile_ident id, Some bitstring_ident))
      payload_vars
  in
  let input_pattern = PPatFunApp (compile_name name, payload_patterns) in
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
  let then_proc = compile_case_branch_body genv branch_env case kont in
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
  wrap_with_channel_access_get ~loc channel_term penv
    (process_e @@
     PInput
       ( channel_term
       , input_pattern
       , compile_guard_tests genv branch_env case.fresh other_facts
           (compile_pterm_eq_tests arg_eq_tests then_proc else_proc)
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
     if A1 then c1 else
     if A2 then c2 else
     0
     ```
  *)
  let rec go = function
    | [] -> process_e PNil
    | case :: cases ->
        let else_proc = go cases in
        let then_proc = compile_case_branch_body genv penv case kont in
        compile_guard_tests genv penv case.fresh case.facts then_proc else_proc
  in
  go cases

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
  (* Note: this is an optimized lowering for the common case where all channel
     guards in one [case] read the same fact name from the same channel. The
     full spec also discusses a more general lock-channel encoding for
     nondeterministic cases; if this optimization ever changes semantics on
     overlapping guards, we should fall back to that general form. *)
  let channel_guards =
    List.map
      (fun (case : T.case) ->
         match extract_channel_guard case.facts with
         | Some (channel, name, args, other_facts, loc) ->
             case, channel, name, args, other_facts, loc
         | None ->
             Error.unsupported ~loc:case.cmd.loc
               "Mixed channel/non-channel case branches are not supported yet")
      cases
  in
  let first_channel, first_name, first_args, first_loc =
    match channel_guards with
    | (_, first_channel, first_name, first_args, _, first_loc) :: _ ->
        first_channel, first_name, first_args, first_loc
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
  let input_pattern = PPatFunApp (compile_name first_name, payload_patterns) in
  let payload_terms =
    List.map (fun id -> pterm_e @@ PPIdent (compile_ident id)) payload_vars
  in
  let rec branches = function
    | [] -> process_e PNil
    | (case, _channel, _name, args, facts, _loc) :: rest ->
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
        let else_proc = branches rest in
        let then_proc = compile_case_branch_body genv branch_env case kont in
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
          (compile_pterm_eq_tests arg_eq_tests then_proc else_proc)
          else_proc
  in
  let channel_term = compile_expr_to_pterm genv penv first_channel in
  wrap_with_channel_access_get ~loc:first_loc channel_term penv
    (process_e @@ PInput (channel_term, input_pattern, branches channel_guards, []))
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
     let curr_syscall = my_syscall_s in
     let x = (
       body_of_my_syscall
     ) in
     let curr_syscall = none_syscall_s in
     body
     ```
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
            { penv with curr_syscall = Some (pterm_e @@ PPIdent def.pv_id) }
            arg_ids
            arg_values
        in
        PEnv.with_process_return_cont call_env on_return
      in
      let normal_branch =
        compile_cmd genv (mk_call_env def.args) (KProc on_fallthrough) def.cmd
      in
      let attack_branches =
        match penv.process_typ_id with
        | None -> []
        | Some process_typ_id ->
            List.map
              (fun attack_def ->
                 compile_cmd genv (mk_call_env attack_def.args) (KProc on_fallthrough) attack_def.cmd)
              (GEnv.find_allowed_attacks ~loc genv ~process_typ_id ~syscall_id:id)
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

     let curr_syscall = my_syscall_s in
     let x = (body_of_my_syscall) in
     let curr_syscall = none_syscall_s in
     c
     ```
  *)
  match expr.desc with
  | Apply (syscall_id, args) when Option.is_some (GEnv.find_syscall_def genv syscall_id) ->
      let old_value = PEnv.find_process_var penv id in
      compile_syscall_call genv penv syscall_id args
        ~on_return: (fun value ->
            compile_cmd genv (PEnv.bind_process_var penv id value)
              (KRestoreVar (id, old_value, kont))
              body)
        (compile_cmd genv penv kont body)
        ~loc:expr.loc
  | Apply (func_id, args) when Option.is_some (PEnv.find_local_func_def penv func_id) ->
      let old_value = PEnv.find_process_var penv id in
      compile_local_function_call genv penv func_id args
        ~on_return: (fun value ->
            compile_cmd genv (PEnv.bind_process_var penv id value)
              (KRestoreVar (id, old_value, kont))
              body)
        (compile_cmd genv penv kont body)
        ~loc:expr.loc
  | _ ->
      let value = compile_expr_to_pterm genv penv expr in
      let old_value = PEnv.find_process_var penv id in
      compile_cmd genv (PEnv.bind_process_var penv id value)
        (KRestoreVar (id, old_value, kont))
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
     let curr_syscall = my_syscall_s in
     let x = (body_of_my_syscall) in
     let curr_syscall = none_syscall_s in
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
  | KRestoreVar (id, old_value, kont) ->
      continue_cmd genv (PEnv.restore_process_var penv id old_value) kont
  | KRestoreVars (saved, kont) ->
      continue_cmd genv (PEnv.restore_process_vars penv saved) kont
  | KLoopOutput (done_flag, loc, lock_term, state_ids) ->
      process_e
        (POutput
           ( lock_term
           , loop_state_message ~done_flag ~loc penv state_ids
           , process_e PNil ))

and compile_cmd genv penv (kont : kont) (cmd : T.cmd)
  : tprocess_e =
  match cmd.desc with
  | Skip -> continue_cmd genv penv kont
  | Sequence (cmd1, cmd2) ->
      compile_cmd genv penv (KSeq (cmd2, kont)) cmd1
  | Put facts ->
      compile_put_facts genv penv facts (continue_cmd genv penv kont)
  | Event facts ->
      compile_event_facts genv penv facts (continue_cmd genv penv kont)
  | Let (id, expr, body) ->
      compile_let_binding genv penv kont id expr body
  | Assign (id_opt, expr) ->
      compile_assignment genv penv kont id_opt expr
  | Return expr ->
      let value = compile_expr_to_pterm genv penv expr in
      (match penv.return_cont with
       | Some return_cont -> return_cont value
       | None -> continue_cmd genv penv kont)
  | Case cases ->
      if List.exists (fun (case : T.case) -> Option.is_some (extract_channel_guard case.facts)) cases then
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
         out(lock_ch, (0, s0, ..., sk)) |
         !(
           in(lock_ch, (=0, s0:bitstring, ..., sk:bitstring)) [precise];
           ...
         )
         |
         in(lock_ch, (=1, s0:bitstring, ..., sk:bitstring)) [precise];
         rest_of_program
         ```
      *)
      let state_ids =
        List.map fst (loop_state_bindings penv)
      in
      let parallelize = function
        | [] -> process_e PNil
        | proc :: procs ->
            List.fold_left
              (fun acc proc -> process_e @@ PPar (acc, proc))
              proc
              procs
      in
      let lock_id = Ident.local "rabbit_loop_ch" in
      let lock_ident = compile_ident lock_id in
      let lock_term = pterm_e @@ PPIdent lock_ident in
      let mk_branch_input_env () =
        let state_pattern_ids =
          List.mapi
            (fun index _id -> Ident.local (Printf.sprintf "loop_state_%d" index))
            state_ids
        in
        let branch_env = bind_loop_state penv state_ids state_pattern_ids in
        state_pattern_ids, branch_env
      in
      let repeat_branch (case : T.case) =
        let state_pattern_ids, branch_env = mk_branch_input_env () in
        let else_proc =
          process_e
            (POutput
               ( lock_term
               , loop_state_message ~done_flag:false ~loc:cmd.loc branch_env state_ids
               , process_e PNil ))
        in
        let then_proc =
          compile_case_branch_body genv branch_env case
            (KLoopOutput (false, cmd.loc, lock_term, state_ids))
        in
        let guard_proc =
          match extract_channel_guard case.facts with
          | Some (channel, name, args, other_facts, loc) ->
              compile_channel_guard_case genv branch_env case
                (KLoopOutput (false, cmd.loc, lock_term, state_ids))
                channel name args other_facts
                ~loc
                ~else_proc
          | None ->
              compile_guard_tests genv branch_env case.fresh case.facts then_proc else_proc
        in
        process_e
          (PInput
             ( lock_term
             , loop_state_pattern ~done_flag:false state_pattern_ids
             , guard_proc
             , [precise_ident, None] ))
      in
      let until_branch (case : T.case) =
        let state_pattern_ids, branch_env = mk_branch_input_env () in
        let else_proc =
          process_e
            (POutput
               ( lock_term
               , loop_state_message ~done_flag:false ~loc:cmd.loc branch_env state_ids
               , process_e PNil ))
        in
        let then_proc =
          compile_case_branch_body genv branch_env case
            (KLoopOutput (true, cmd.loc, lock_term, state_ids))
        in
        let guard_proc =
          match extract_channel_guard case.facts with
          | Some (channel, name, args, other_facts, loc) ->
              compile_channel_guard_case genv branch_env case
                (KLoopOutput (true, cmd.loc, lock_term, state_ids))
                channel name args other_facts
                ~loc
                ~else_proc
          | None ->
              compile_guard_tests genv branch_env case.fresh case.facts then_proc else_proc
        in
        process_e
          (PInput
             ( lock_term
             , loop_state_pattern ~done_flag:false state_pattern_ids
             , guard_proc
             , [precise_ident, None] ))
      in
      let cont_state_pattern_ids =
        List.mapi
          (fun index _id -> Ident.local (Printf.sprintf "loop_done_state_%d" index))
          state_ids
      in
      let cont_env = bind_loop_state penv state_ids cont_state_pattern_ids in
      let continuation =
        process_e
          (PInput
             ( lock_term
             , loop_state_pattern ~done_flag:true cont_state_pattern_ids
             , continue_cmd genv cont_env kont
             , [precise_ident, None] ))
      in
      let workers =
        match List.map repeat_branch repeat_cases @ List.map until_branch until_cases with
        | [] -> process_e PNil
        | procs -> process_e @@ PRepl (parallelize procs)
      in
      let init_proc =
        process_e
          (POutput
             ( lock_term
             , loop_state_message ~done_flag:false ~loc:cmd.loc penv state_ids
             , process_e PNil ))
      in
      process_e
        (PRestr
           ( lock_ident
           , None
           , channel_ident
           , parallelize [init_proc; workers; continuation] ))
  | New (id, None, body) ->
      let fresh_ident = compile_ident id in
      let fresh_term = pterm_e @@ PPIdent fresh_ident in
      let old_value = PEnv.find_process_var penv id in
      process_e @@
        PRestr
           ( fresh_ident
           , None
           , bitstring_ident
           , compile_cmd genv (PEnv.bind_process_var penv id fresh_term)
               (KRestoreVar (id, old_value, kont))
               body )
  | New (id, Some (name, args), body) ->
      (* `compile_generated_structure_decls` handle the declarations *)
      GEnv.register_structure ~loc:cmd.loc genv name (List.length args);
      let fresh_ident = compile_ident id in
      let fresh_term = pterm_e @@ PPIdent fresh_ident in
      let old_value = PEnv.find_process_var penv id in
      let struct_term =
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
           , compile_cmd genv (PEnv.bind_process_var penv id struct_term)
               (KRestoreVar (id, old_value, kont))
               body )
  | Get (ids, expr, name, body) ->
      GEnv.register_structure ~loc:cmd.loc genv name (List.length ids);
      let struct_term = compile_expr_to_pterm genv penv expr in
      let addr_term = structure_addr_term name struct_term in
      let saved =
        List.map (fun id -> id, PEnv.find_process_var penv id) ids
      in
      let body_env =
        List.mapi
          (fun index id -> id, structure_arg_term name (index + 1) struct_term)
          ids
        |> List.fold_left
             (fun penv (id, value) -> PEnv.bind_process_var penv id value)
             penv
      in
      process_e
        (PGet
           ( deleted_address_table_ident
           , [PPatEqual addr_term]
           , None
           , process_e PNil
           , compile_cmd genv body_env
               (KRestoreVars (saved, kont))
               body
           , [] ))
  | Del (expr, name) ->
      (* 3.4  Encoding Structured facts, new, let, delete

         ```
         delete x.Struct
         ```

         ```
         table deleted_address_table(bitstring).
         ...
         insert deleted_address_table(StructAddr(x_struct));
         ```
      *)
      (* x_struct *)
      let struct_term = compile_expr_to_pterm genv penv expr in
      (* StructAddr(x_struct) *)
      let addr_term = structure_addr_term name struct_term in
      (* insert deleted_address_table( StructAddr(x_struct) ); ... *)
      add_comment (Printf.sprintf "delete _.%s" name) @@
      process_e
        (PInsert
           (deleted_address_table_ident, [addr_term], continue_cmd genv penv kont))


(*
  Line 30:

  ```
  function enc:2

  fun enc ( bitstring, bitstring ).
  ```

  Here a function has a return type `bitstring`:

  ```
  fun enc ( bitstring, bitstring ): bitstring.
  ```
*)
let compile_function ~loc:_loc (id : T.ident) (arity : int) : tdecl list =
  let name = compile_ident id in
  let arg_tys = List.init arity (fun _ -> bitstring_ident) in
  [ TComment (Printf.sprintf "function %s:%d" (fst id) arity)
  ; TFunDecl (name, arg_tys, bitstring_ident, [])
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
    |> List.map (fun id -> compile_ident id, bitstring_ident)
  in
  let lhs_term = compile_expr_to_term genv lhs in
  let rhs_term = compile_expr_to_term genv rhs in
  let equality_term =
    term_e @@ PFunApp (pv_ident "=", [lhs_term; rhs_term])
  in
  [ TComment (Printf.sprintf "equation %s = %s" (T.string_of_expr lhs) (T.string_of_expr rhs))
  ; TEquation ([envdecl, EETerm equality_term], [])
  ]

(* Syscalls are expanded when they are called.
   No declaration is generated at this point.
*)
let collect_syscall
    ~loc
    genv
    (id : T.ident)
    (args : T.ident list)
    (cmd : T.cmd)
  =
  let pv_id = GEnv.fresh_syscall_ident ~loc genv id in
  let def = { pv_id; args; cmd; } in
  GEnv.register_syscall ~loc genv id def

let collect_attack
    ~loc
    genv
    (id : T.ident)
    (syscall : T.ident)
    (args : T.ident list)
    (cmd : T.cmd)
  =
  GEnv.register_attack_def ~loc genv id { syscall; args; cmd; }

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
   insert access_control_table(client_t, udp_t, send_s);
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
      (* Note: [allow ... [.] ] is currently represented by granting access to
         the distinguished pseudo-syscall [none_syscall_s]. This is a pragmatic
         encoding choice for direct process operations, but it is worth
         re-checking against the final spec once syscall lowering is in place. *)
      List.iter2
        (fun t_target_typ target_typ ->
           let entry =
             { rabbit_process_type = t_process_typ
             ; rabbit_target_type = t_target_typ
             ; rabbit_syscall = None
             ; pv_process_type = process_typ
             ; pv_target_type = target_typ
             ; pv_syscall = none_syscall_ident
             }
           in
           genv.allow_entries <- entry :: genv.allow_entries)
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
                    ; pv_syscall = def.pv_id
                    }
                  in
                  genv.allow_entries <- entry :: genv.allow_entries)
            syscalls)
        t_target_typs target_typs;
      []

let collect_allow_attack
    ~loc:(_loc : Location.t)
    (genv : GEnv.t)
    (process_typs : T.ident list)
    (attacks : T.ident list)
  =
  List.iter (fun process_typ ->
      let prev =
        match Hashtbl.find_opt genv.allow_attack_table process_typ with
        | None -> []
        | Some prev -> prev
      in
      Hashtbl.replace genv.allow_attack_table process_typ (prev @ attacks))
    process_typs

let compile_init ~loc:(_loc : Location.t) genv (id : T.ident) (desc : T.init_desc) : tdecl list =
  (*
     3.1 Encoding Strings, Constants, Events and Function Declarations
     3.10 Parametrized Feature Encoding

     ```
     const fresh priv_k
     const pubkey<k> = pk(priv_k<k>)
     ```

     ```
     const priv_k : bitstring.
     reduc forall k:param_data; pubkey(k) = pk(priv_k(k)).
     ```
  *)
  let init_ident = compile_ident id in
  match desc with
  | Fresh ->
      [ TComment (Printf.sprintf "const fresh %s" (Ident.to_string id))
      ; TConstDecl (init_ident, bitstring_ident, [])
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
      let init_term =
        term_e @@ PFunApp (init_ident, [term_e @@ PIdent param_ident])
      in
      let value_term = compile_expr_to_term genv expr in
      [ TComment (Printf.sprintf "const %s<%s> = .." (Ident.to_string id) (Ident.to_string param))
      ; TReduc
          ( [ [param_ident, param_data_ident]
            , EETerm (term_e @@ PFunApp (pv_ident "=", [init_term; value_term]))
            ]
          , [] )
      ]
  | Fresh_with_param ->
      [ TComment (Printf.sprintf "const fresh %s<>" (Ident.to_string id))
      ; TFunDecl (init_ident, [param_data_ident], bitstring_ident, [])]

let compile_channel
    ~loc
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
      Error.unsupported ~loc
        "Parameterized channel declarations are not supported yet"
  | None ->
      [ TComment (Printf.sprintf "channel %s : %s" (Ident.to_string id) (Ident.to_string typ))
      ; TFree (compile_ident id, channel_ident, [pv_ident "private", None])
      ]

let process_file_channel_ident : ident = pv_ident "rabbit__file_ch"

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
     insert file_type_table(ptype, readonly_t, secret_priv_str);
     new file_ch : channel;
     out(file_ch, (secret_priv_str, enc(priv_k, sym_k))) |
     ...
     ```
  *)
  match penv.file_channel with
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
  let local_func_defs =
    List.map (fun (id, args, cmd) -> id, (args, cmd)) funcs
  in
  match param with
  | Some _ ->
      Error.unsupported ~loc
        "Parameterized process declarations are not supported yet"
  | None ->
      let proc_args =
        (ptype_arg_ident, proc_t_ident, false)
        ::
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
        if files = [] then
          PEnv.create_process_env
            ~local_func_defs
            ~process_typ_id:(Some typ)
            ~proc_type:(pterm_e @@ PPIdent ptype_arg_ident)
            ~curr_syscall:(Some (pterm_e @@ PPIdent none_syscall_ident))
            ~file_channel:None
        else
          PEnv.create_process_env
            ~local_func_defs
            ~process_typ_id:(Some typ)
            ~proc_type:(pterm_e @@ PPIdent ptype_arg_ident)
            ~curr_syscall:(Some (pterm_e @@ PPIdent none_syscall_ident))
            ~file_channel:(Some (pterm_e @@ PPIdent process_file_channel_ident))
      in
      let rec init_vars penv = function
        | [] ->
            wrap_with_channel_init ~loc args
            @@ wrap_with_file_init ~loc genv penv files
            @@ compile_cmd genv penv KStop main
        | (var, expr) :: vars ->
            let value = compile_expr_to_pterm genv penv expr in
            init_vars (PEnv.bind_process_var penv var value) vars
      in
      [ TComment (Printf.sprintf "process %s(..): %s" (Ident.to_string id) (Ident.to_string typ))
      ; TPDef (compile_ident id, proc_args, init_vars base_penv vars)
      ]

let compile_proc_call genv (proc : T.proc) : tprocess_e =
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
     | Some _ ->
         Error.unsupported ~loc:proc.loc
           "Parameterized process instantiation is not supported yet")
    @
    List.map
      (fun ({ channel; parameter; _ } : T.chan_arg) ->
         match parameter with
         | None -> pterm_e @@ PPIdent (compile_ident channel)
         | Some None | Some (Some _) ->
             Error.unsupported ~loc:proc.loc
               "Parameterized channel instantiation is not supported yet")
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
  | Unbounded proc -> compile_proc_call genv proc
  | Bounded (_id, procs) ->
      process_e @@ PRepl (parallel_proc (List.map (compile_proc_call genv) procs))

let gterm_binary (op : string) (lhs : gterm_e) (rhs : gterm_e) : gterm_e =
  gterm_e @@ PGFunApp (pv_ident op, [lhs; rhs], None)

(* `g1 op g2 op .. op gn` *)
let rec gterm_binary_mult ~loc op = function
  | [] ->
      Error.internal ~loc "Cannot combine an empty list of query facts"
  | [g] -> g
  | g :: gs ->
      gterm_binary op g (gterm_binary_mult ~loc op gs)

let gterm_event
    (name : T.name)
    (args : gterm_e list)
  : gterm_e =
  gterm_e @@
  PGFunApp
    ( pv_ident "event"
    , [gterm_e @@ PGFunApp (compile_name name, args, None)]
    , None )

let compile_lemma_fact genv (fact : T.fact) : gterm_e =
  let loc = fact.loc in
  match fact.desc with
  | Global (name, args) ->
      GEnv.register_event ~loc genv name (List.length args);
      gterm_event name (List.map (compile_expr_to_gterm genv) args)
  | Plain (name, args) ->
      GEnv.register_event ~loc genv name (List.length args);
      gterm_event name (List.map (compile_expr_to_gterm genv) args)
  | Eq (lhs, rhs) ->
      gterm_binary "="
        (compile_expr_to_gterm genv lhs)
        (compile_expr_to_gterm genv rhs)
  | Neq (lhs, rhs) ->
      gterm_binary "<>"
        (compile_expr_to_gterm genv lhs)
        (compile_expr_to_gterm genv rhs)
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
  let envdecl =
    List.map
      (fun id -> compile_ident id, bitstring_ident)
      (match lemma.desc with
       | T.Plain _ -> []
       | Reachability { fresh; _ } -> fresh
       | Correspondence { fresh; _ } -> fresh)
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
  if genv.top_process <> None then
    Error.invalid_input ~loc "Multiple system declarations are not accepted";
  let top_process = parallel_proc @@ List.map (compile_proc_group_desc genv) procs in
  genv.top_process <- Some top_process;
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
     free attacker : channel.
     table access_control_table(proc_t, acc_data_t, syscall_t).
     table file_type_table(proc_t, acc_data_t, bitstring).
     table channel_table(acc_data_t, channel).
     table deleted_address_table(bitstring).
     const none_syscall_s : syscall_t.
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
     const hello_world_str : bitstring.
     ...
     out(ch, msg(hello_world_str))
     ```
  *)
  List.concat_map (fun (literal, id) ->
      [ TComment (Printf.sprintf "String constant %S" literal)
      ; TConstDecl (id, bitstring_ident, []) ]) genv.strings

let compile_syscall_consts (genv : GEnv.t) : tdecl list =
  (*
     3.2 Encoding Process Types, Channel types, File types, and Access Control Policies
     3.9 Syscall and Attack Encoding

     ```
     syscall send(c, v) { ... }
     ```

     ```
     const send_s : syscall_t.
     ```
  *)
  List.concat_map (fun (id, def) ->
      [ TComment (Printf.sprintf "syscall %s(..)" (Ident.to_string id))
      ; TConstDecl (def.pv_id, syscall_t_ident, [])
      ]) genv.syscalls

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
  List.concat_map (fun (name, arity) ->
      [ TComment (Printf.sprintf "Event declaration ::%s(..)" name)
      ; TEventDecl (compile_name name, List.init arity (fun _ -> bitstring_ident))
      ]) genv.events

(* 3.4 Encoding Structured facts, new, let, delete

   ```
   new x := Struct(x1, ..., xn)
   ```

   ```
   fun Struct ( bitstring , ... , bitstring ) : bitstring [ data ] .
   reduc forall x_0 : bitstring , ... , x_n : bitstring ;
     StructAddr ( Struct ( x_0 , ... , x_n ) = x_0 .
   reduc forall x_0 : bitstring , ... , x_n : bitstring ;
     StructPar1 ( Struct ( x_0 , ... , x_n ) = x_1 .
   reduc forall x_0 : bitstring , ... , x_n : bitstring ;
     StructParn ( Struct ( x_0 , ... , x_n ) = x_n .
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
  genv.structures
  |> List.concat_map @@ fun (name, arity) ->
      let envdecl =
        List.init (arity + 1) (fun index -> mk_var index, bitstring_ident)
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
          , List.init (arity + 1) (fun _ -> bitstring_ident)
          , bitstring_ident
          , [pv_ident "data", None] )
      in
      let addr_decl =
        (* reduc forall x_0:bitstring, ..., x_n:bitstring;
             StructAddr(Struct(x_0, ..., x_n) = x_0.
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
             StructPari(Struct(x_0, ..., x_n) = x_i.
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

(*
   3.2 Encoding Process Types, Channel types, File types, and Access Control Policies

   ```
   allow client_t udp_t [send]
   allow client_t readonly_t [.]
   ```

   ```
   insert access_control_table(client_t, udp_t, send_s);
   insert access_control_table(client_t, readonly_t, none_syscall_s);
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
              ; pterm_e @@ PPIdent entry.pv_syscall
              ]
            , acc ))
    (List.rev genv.allow_entries)
    body

let rec collect_decl (genv : GEnv.t) (decl : T.decl) =
  let loc = decl.loc in
  match decl.desc with
  | Syscall { id; args; cmd; attack=_ } ->
      collect_syscall ~loc genv id args cmd
  | Attack { id; syscall; args; cmd } ->
      collect_attack ~loc genv id syscall args cmd
  | AllowAttack { process_typs; attacks } ->
      collect_allow_attack ~loc genv process_typs attacks
  | Process { id; typ; _ } ->
      GEnv.register_process_type ~loc genv id typ
  | Load (_filename, decls) ->
      List.iter (collect_decl genv) decls
  | _ -> ()

let rec compile_decl genv (decl : T.decl) : tdecl list =
  let loc = decl.loc in
  match decl.desc with
  | Syscall _ | Attack _ | AllowAttack _ ->
      (* They are handled by `collect_decl` *)
      []
  | Function { id; arity } ->
      compile_function ~loc id arity
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
      compile_process genv ~loc id param args typ files vars funcs main
  | System (procs, lemmas) ->
      compile_system ~loc genv procs lemmas
  | Load (filename, decls) ->
      compile_load genv filename decls

(* `load` simply expands its declaration. *)
and compile_load genv (filename : string) (decls : T.decl list) : tdecl list =
  TComment (Printf.sprintf "Load %s" filename) ::
  List.concat_map (compile_decl genv) decls


let compile_program (decls : T.decl list) : Pv_parser.program =
  let genv = GEnv.create () in
  List.iter (GEnv.register_decl_strings genv) decls;
  List.iter (collect_decl genv) decls;
  let body = List.concat_map (compile_decl genv) decls in
  let top_process = Option.value genv.top_process ~default:(process_e PNil) in
  let top_process = add_allow_inits genv top_process in
  ( compile_prelude genv
    @ compile_structure_decls genv
    @ compile_syscall_consts genv
    @ compile_event_decls genv
    @ compile_string_consts genv
    @ [ TComment "Body" ]
    @ body
    @ [ TComment "System" ]
  , top_process
  , None )
