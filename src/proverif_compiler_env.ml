open Rabbit_proverif_pv_parse
open Pitptree
include Proverif_compiler_support

type syscall_def =
  { pv_id : ident (** Proverif id *)
  ; args : T.ident list
  ; cmd : T.cmd
  ; passive : bool
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
  ; pv_syscall : ident option (** `None` for `[.]` *)
  }

type event_kind =
  | Global
  | Plain

let compile_event_name (name : T.name) = function
  | Global -> compile_name name "event_global"
  | Plain -> compile_name name "event_plain"

type comparison_event_kind =
  | Equality
  | Inequality

let compile_comparison_event_name = function
  | Equality -> pv_ident "eq__fact_event"
  | Inequality -> pv_ident "neq__fact_event"

module GEnv = struct

  type t =
    { mutable strings       : (string * ident) list (** string constants and their identifiers *)
    ; mutable integers      : (int * ident) list (** integer constants and their identifiers *)
    ; mutable parameters    : (string * ident) list (** concrete parameter values *)
    ; mutable param_inits   : (T.ident * (T.ident * T.expr)) list
        (** parameterized derived constants and their definitions *)
    ; mutable syscalls      : (Ident.t * syscall_def) list (** system calls and definitions *)
    ; mutable attacks       : (Ident.t * attack_def) list (** attacks and definitions *)
    ; allow_attack_table    : (Ident.t, T.ident list) Hashtbl.t (** process type and allowed attacks *)
    ; generated_names       : (string, unit) Hashtbl.t (** Generated ProVerif identifiers in use *)
    ; mutable allow_entries : allow_entry list
    ; mutable process_types : (Ident.t * ident) list (** process types in Rabbit and Proverif *)
    ; mutable structure_facts : (Name.t * Type.type_ list) list (** structure fact constructor and arity *)
    ; mutable channel_facts   : (Name.t * Type.type_ list) list
    ; mutable events        : (Name.t * (event_kind * Type.type_ list)) list
    ; mutable comparison_events : (comparison_event_kind * Type.type_) list
    ; mutable top_process   : tprocess_e option
    }

  let create () : t =
    { strings            = []
    ; integers           = []
    ; parameters         = []
    ; param_inits        = []
    ; syscalls           = []
    ; attacks            = []
    ; allow_attack_table = Hashtbl.create 101
    ; generated_names    = Hashtbl.create 101
    ; allow_entries      = []
    ; process_types      = []
    ; structure_facts    = []
    ; channel_facts      = []
    ; events             = []
    ; comparison_events  = []
    ; top_process        = None
    }

  let add_with_types kind get_entries set_entries ~loc genv (name : T.name) types =
    let entries = get_entries genv in
    match List.assoc_opt name entries with
    | None -> set_entries genv (entries @ [name, types])
    | Some types' ->
        if List.length types <> List.length types' then
          Error.invalid_input ~loc
            "%s %s is used with inconsistent arities (%d and %d)"
            kind name (List.length types') (List.length types);
        (try List.iter2 Type.unify types types' with
         | Type.Cannot_unify _ ->
             Error.invalid_input ~loc
               "%s %s is used with inconsistent argument types"
               kind name)

  (* strings **********************************************)

  let strings genv = genv.strings

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
    else if Str.string_match (Str.regexp "[0-9]") sanitized 0 then
      "value_" ^ sanitized
    else
      sanitized

  let add_ident genv ~base : ident =
    let rec find_available index =
      let candidate =
        if index = 0 then base else Printf.sprintf "%s_%d" base index
      in
      if Hashtbl.mem genv.generated_names candidate then
        find_available (index + 1)
      else
        candidate
    in
    let name = find_available 0 in
    Hashtbl.add genv.generated_names name ();
    pv_ident name

  (* "hello" -> "hello__str" *)
  let add_string genv s =
    match List.assoc_opt s genv.strings with
    | Some _ -> ()
    | None ->
        let base = sanitize_string_for_ident s ^ "__str" in
        let id = add_ident genv ~base in
        genv.strings <- genv.strings @ [s, id]

  let fresh_string_ident genv s : ident =
    add_string genv s;
    match List.assoc_opt s genv.strings with
    | Some id -> id
    | None -> assert false

  (* integers *********************************************)

  let integers genv = genv.integers

  let fresh_integer_ident genv n : ident =
    match List.assoc_opt n genv.integers with
    | Some id -> id
    | None ->
        let printed = string_of_int n in
        let suffix =
          if printed.[0] = '-' then
            "neg_" ^ String.sub printed 1 (String.length printed - 1)
          else
            "pos_" ^ printed
        in
        let id = add_ident genv ~base:("int__" ^ suffix) in
        genv.integers <- genv.integers @ [n, id];
        id

  (* concrete parameter values *****************************)

  let parameters genv = genv.parameters

  let fresh_parameter_ident genv (expr : T.expr) : ident =
    let value = T.string_of_expr expr in
    match List.assoc_opt value genv.parameters with
    | Some id -> id
    | None ->
        let suffix = sanitize_string_for_ident value in
        let id = add_ident genv ~base:(suffix ^ "__param") in
        genv.parameters <- genv.parameters @ [value, id];
        id

  let add_param_init genv id param expr =
    genv.param_inits <- genv.param_inits @ [id, (param, expr)]

  let find_param_init genv id =
    List.assoc_opt id genv.param_inits

  let rec add_expr_strings genv (expr : T.expr) =
    match expr.desc with
    | Ident { param; _ } -> Option.iter (add_expr_strings genv) param
    | Apply (_, args) | Tuple args -> List.iter (add_expr_strings genv) args
    | String s -> add_string genv s
    | Boolean _ | Integer _ | Float _ | Unit -> ()

  let add_fact_strings genv (fact : T.fact) =
    match fact.desc with
    | Channel { channel; args; _ } ->
        add_expr_strings genv channel;
        List.iter (add_expr_strings genv) args
    | Plain (_name, args) | Global (_name, args) ->
        List.iter (add_expr_strings genv) args
    | Eq (lhs, rhs) | Neq (lhs, rhs) ->
        add_expr_strings genv lhs;
        add_expr_strings genv rhs
    | File { path; contents } ->
        add_expr_strings genv path;
        add_expr_strings genv contents

  let rec add_cmd_strings genv (cmd : T.cmd) =
    match cmd.desc with
    | Skip -> ()
    | Sequence (lhs, rhs) ->
        add_cmd_strings genv lhs;
        add_cmd_strings genv rhs
    | Put facts | Event facts -> List.iter (add_fact_strings genv) facts
    | Let (_id, expr, body) ->
        add_expr_strings genv expr;
        add_cmd_strings genv body
    | Assign (_, expr) | Expr expr | Del (expr, _) ->
        add_expr_strings genv expr
    | Case cases -> List.iter (add_case_strings genv) cases
    | While (repeat_cases, until_cases) ->
        List.iter (add_case_strings genv) repeat_cases;
        List.iter (add_case_strings genv) until_cases
    | New (_id, value, body) ->
        Option.iter
          (fun (_name, args) -> List.iter (add_expr_strings genv) args)
          value;
        add_cmd_strings genv body
    | Get (_ids, expr, _name, body) ->
        add_expr_strings genv expr;
        add_cmd_strings genv body

  and add_case_strings genv ({ facts; cmd; _ } : T.case) =
    List.iter (add_fact_strings genv) facts;
    add_cmd_strings genv cmd

  let add_proc_strings genv (proc : T.proc) =
    let { T.parameter; args; _ } = proc.data in
    Option.iter (add_expr_strings genv) parameter;
    List.iter
      (fun ({ parameter; _ } : T.chan_arg) ->
         Option.iter (Option.iter (add_expr_strings genv)) parameter)
      args

  let add_proc_group_strings genv = function
    | T.Unbounded proc -> add_proc_strings genv proc
    | Bounded (_id, procs) -> List.iter (add_proc_strings genv) procs

  let add_lemma_strings genv (_id, lemma : T.ident * T.lemma) =
    match lemma.desc with
    | Plain _ -> ()
    | Reachability { facts; _ } -> List.iter (add_fact_strings genv) facts
    | Correspondence { premise; conclusion; _ } ->
        add_fact_strings genv premise;
        add_fact_strings genv conclusion

  let rec add_decl_strings genv (decl : T.decl) =
    match decl.desc with
    | Equation (lhs, rhs) ->
        add_expr_strings genv lhs;
        add_expr_strings genv rhs
    | Syscall { cmd; _ } | Attack { cmd; _ } -> add_cmd_strings genv cmd
    | Init { desc = Value expr; _ }
    | Init { desc = Value_with_param (_, expr); _ } ->
        add_expr_strings genv expr
    | Process { files; vars; funcs; main; _ } ->
        List.iter
          (fun (path, _typ, contents) ->
             add_expr_strings genv path;
             add_expr_strings genv contents)
          files;
        List.iter (fun (_id, expr) -> add_expr_strings genv expr) vars;
        List.iter (fun (_id, _args, cmd) -> add_cmd_strings genv cmd) funcs;
        add_cmd_strings genv main
    | System (procs, lemmas) ->
        List.iter (add_proc_group_strings genv) procs;
        List.iter (add_lemma_strings genv) lemmas
    | Load (_filename, decls) -> List.iter (add_decl_strings genv) decls
    | Function _ | Type _ | Allow _ | AllowAttack _
    | Init { desc = Fresh | Fresh_with_param; _ } | Channel _ -> ()


  (* syscalls ***********************************************)

  let syscalls genv = genv.syscalls

  let find_syscall_def genv (id : T.ident) : syscall_def option =
    List.assoc_opt id genv.syscalls

  (* ("name", stamp) -> "name__stamp__syscall" *)
  let compile_syscall_ident ~loc genv (id : T.ident) : ident =
    match List.assoc_opt id genv.syscalls with
    | Some _ ->
        Error.invalid_input ~loc "Syscall %s is already defined" (Ident.to_string id)
    | None -> compile_ident_kind id "syscall"

  let add_syscall_def
      ~loc
      ~passive
      genv
      (id : T.ident)
      (args : T.ident list)
      (cmd : T.cmd)
    =
    let pv_id = compile_syscall_ident ~loc genv id in
    let def = { pv_id; args; cmd; passive; } in
    genv.syscalls <- (id, def) :: genv.syscalls

  (* attacks ************************************************)

  let add_attack_def ~loc:_ genv id def =
    genv.attacks <- (id, def) :: genv.attacks

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
         | Some _ -> None
         | None ->
             Error.internal ~loc "Attack %s has no definition"
               (Ident.to_string attack_id))
      allowed

  let add_allowed_attacks genv process_typ attacks =
    let previous =
      match Hashtbl.find_opt genv.allow_attack_table process_typ with
      | None -> []
      | Some previous -> previous
    in
    Hashtbl.replace genv.allow_attack_table process_typ (previous @ attacks)

  (* allow entries ******************************************)

  let allow_entries genv = genv.allow_entries

  let add_allow_entry genv entry =
    genv.allow_entries <- entry :: genv.allow_entries

  (* process types ******************************************)

  let find_process_type ~loc genv (process_id : T.ident) : ident =
    match List.assoc_opt process_id genv.process_types with
    | Some typ -> typ
    | None ->
        Error.internal ~loc
          "process type for %s is not available in ProVerif system translation"
          (Ident.to_string process_id)

  let add_process_type ~loc genv (process_id : T.ident) (typ : T.ident) =
    match List.assoc_opt process_id genv.process_types with
    | Some _ ->
        Error.invalid_input ~loc "Process %s is already defined"
          (Ident.to_string process_id)
    | None ->
        genv.process_types <- (process_id, compile_ident typ) :: genv.process_types

  (* structure facts ****************************************)

  let structure_facts genv = genv.structure_facts

  let find_structure_fact ~loc genv name =
    match List.assoc_opt name genv.structure_facts with
    | None -> Error.internal ~loc "structure fact %s is not declared" name
    | Some ftys -> ftys

  (* called when predeclared using `structure s(_, channel, parameter)` declaration *)
  let add_structure_fact ~loc genv name ftys =
    match List.assoc_opt name genv.structure_facts with
    | None -> genv.structure_facts <- genv.structure_facts @ [name, ftys]
    | Some _ -> Error.internal ~loc "structure fact %s is already defined" name

  (* channel facts *****************************************)

  let channel_facts genv = genv.channel_facts

  let add_channel_fact =
    add_with_types
      "Channel fact"
      (fun genv -> genv.channel_facts)
      (fun genv channel_facts -> genv.channel_facts <- channel_facts)

  (* events *************************************************)

  let events genv = genv.events

  let add_event ~loc genv (name : T.name) kind types =
    match List.assoc_opt name genv.events with
    | None ->
        genv.events <- genv.events @ [name, (kind, types)]
    | Some (kind', _) when kind <> kind' ->
        Error.invalid_input ~loc
          "Event %s is used as both a global and a plain fact"
          name
    | Some (_, types') ->
        if List.length types <> List.length types' then
          Error.invalid_input ~loc
            "Event %s is used with inconsistent arities (%d and %d)"
            name (List.length types') (List.length types);
        (try List.iter2 Type.unify types types' with
         | Type.Cannot_unify _ ->
             Error.invalid_input ~loc
               "Event %s is used with inconsistent argument types" name)

  let comparison_events genv = genv.comparison_events

  let add_comparison_event ~loc genv kind typ =
    match List.assoc_opt kind genv.comparison_events with
    | None -> genv.comparison_events <- genv.comparison_events @ [kind, typ]
    | Some typ' ->
        (try Type.unify typ typ' with
         | Type.Cannot_unify _ ->
             Error.invalid_input ~loc
               "Comparison events of one kind have inconsistent argument types")

  (* top process ********************************************)

  let top_process genv = genv.top_process
  let set_top_process genv process = genv.top_process <- Some process

end

module PEnv = struct

  type binding =
    { value : pterm_e
    ; typ : Type.type_
    }

  type t =
    { bindings : (T.ident * binding) list
    ; local_func_defs : (T.ident * (T.ident list * T.cmd)) list
    ; process_typ_id : T.ident
    ; proc_type : pterm_e
    ; curr_syscall : pterm_e
    ; file_channel : pterm_e option
    ; result : pterm_e
    ; result_type : Type.type_
    }

  let create_process_env
      ~(local_func_defs : (T.ident * (T.ident list * T.cmd)) list)
      ~(process_typ_id : T.ident)
      ~(proc_type : pterm_e)
      ~(curr_syscall : pterm_e)
      ~(file_channel : pterm_e option)
    : t =
    { bindings = []
    ; local_func_defs
    ; process_typ_id
    ; proc_type
    ; curr_syscall
    ; file_channel
    ; result = pterm_e @@ PPTuple []
    ; result_type = Type.TValue
    }

  (* bindings **********************************************)

  let bindings penv =
    List.map (fun (id, binding) -> id, binding.value) penv.bindings

  let binding_type_exn ~loc penv id =
    match List.assoc_opt id penv.bindings with
    | Some binding -> binding.typ
    | None ->
        Error.internal ~loc "Type of process variable %s is not available"
          (Ident.to_string id)

  let find_process_var penv (id : T.ident) : pterm_e option =
    Option.map (fun binding -> binding.value) (List.assoc_opt id penv.bindings)

  let find_process_var_exn ~loc penv (id : T.ident) : pterm_e =
    match find_process_var penv id with
    | Some value -> value
    | None ->
        Error.internal ~loc "Loop-carried variable %s is not available"
          (Ident.to_string id)

  let define_process_var (penv : t) (id : T.ident) (typ : Type.type_) (value : pterm_e) =
    { penv with bindings = (id, { value; typ }) :: penv.bindings }

  let assign_process_var (penv : t) (id : T.ident) (value : pterm_e) =
    let rec assign = function
      | [] -> assert false
      | (id', binding) :: bindings when id = id' ->
          (id, { binding with value }) :: bindings
      | binding :: bindings -> binding :: assign bindings
    in
    { penv with bindings = assign penv.bindings }

  let remove_process_vars (penv : t) (ids : T.ident list) =
    { penv with
      bindings =
        List.fold_left
          (fun bindings id -> List.remove_assoc id bindings)
          penv.bindings
          ids
    }

  (* local func defs ****************************************)

  let find_local_func_def penv (id : T.ident)
    : (T.ident list * T.cmd) option =
    List.assoc_opt id penv.local_func_defs

  (* process type id ****************************************)

  let process_typ_id penv = penv.process_typ_id

  (* process type *******************************************)

  let proc_type penv = penv.proc_type

  (* current syscall ****************************************)

  let curr_syscall penv = penv.curr_syscall

  let with_curr_syscall penv curr_syscall = { penv with curr_syscall }

  (* file channel *******************************************)

  let file_channel penv = penv.file_channel

  (* result register ****************************************)

  let result penv = penv.result

  let result_type penv = penv.result_type

  let with_result penv result_type result = { penv with result; result_type }

end
