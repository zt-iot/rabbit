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

type syscall_def =
  { id : Typed.ident
  ; syscall_ident : Pitptree.ident
  ; args : Typed.ident list
  ; cmd : Typed.cmd
  ; attack : bool
  ; loc : Location.t
  }
[@@warning "-69"]

type attack_def =
  { id : Typed.ident
  ; syscall : Typed.ident
  ; args : Typed.ident list
  ; cmd : Typed.cmd
  ; loc : Location.t
  }
[@@warning "-69"]

type env =
  { string_table : (string, Pitptree.ident) Hashtbl.t
  ; syscall_table : (string, Pitptree.ident) Hashtbl.t
  ; syscall_def_table : (string, syscall_def) Hashtbl.t
  ; attack_def_table : (string, attack_def) Hashtbl.t
  ; allow_attack_table : (string, Typed.ident list) Hashtbl.t
  ; generated_name_table : (string, unit) Hashtbl.t
  ; generated_name_counter : (string, int) Hashtbl.t
  ; mutable allow_entries : (Pitptree.ident * Pitptree.ident * Pitptree.ident) list
  ; process_type_table : (string, Pitptree.ident) Hashtbl.t
  ; structure_table : (string, int) Hashtbl.t
  ; event_table : (string, int) Hashtbl.t
  ; mutable top_process : Pitptree.tprocess_e option
  }

let create_env () : env =
  { string_table = Hashtbl.create 101
  ; syscall_table = Hashtbl.create 101
  ; syscall_def_table = Hashtbl.create 101
  ; attack_def_table = Hashtbl.create 101
  ; allow_attack_table = Hashtbl.create 101
  ; generated_name_table = Hashtbl.create 101
  ; generated_name_counter = Hashtbl.create 101
  ; allow_entries = []
  ; process_type_table = Hashtbl.create 101
  ; structure_table = Hashtbl.create 101
  ; event_table = Hashtbl.create 101
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
      error ~loc @@
      Internal_error
        (Printf.sprintf
           "process type for %s is not available in ProVerif system translation"
           (Ident.to_string process_id))

let compile_name (name : Typed.name) : Pitptree.ident = pv_ident name

(* "Struct" for "Struct" *)
let structure_ctor_ident (name : Typed.name) : Pitptree.ident =
  compile_name name

(* "StructAddr" for "Struct" *)
let structure_addr_ident (name : Typed.name) : Pitptree.ident =
  pv_ident (name ^ "Addr")

(* "StructPar1" for "Struct" and 1 *)
let structure_arg_ident (name : Typed.name) (index : int) : Pitptree.ident =
  pv_ident (Printf.sprintf "%sPar%d" name index)

let register_structure ~loc env (name : Typed.name) (arity : int) =
  match Hashtbl.find_opt env.structure_table name with
  | None -> Hashtbl.add env.structure_table name arity
  | Some arity' when arity' = arity -> ()
  | Some arity' ->
      error ~loc @@
      Invalid_input
        (Printf.sprintf
           "Structure %s is used with inconsistent arities (%d and %d)"
           name arity' arity)

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

(* `"hello-world"`  ->  `"hello_world"`
   `"__x y__"`  ->  `"x_y"` *)
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

let fresh_syscall_ident env (id : Typed.ident) : Pitptree.ident =
  let name = Ident.to_string id in
  match Hashtbl.find_opt env.syscall_table name with
  | Some id -> id
  | None ->
      let base = sanitize_string_for_ident name ^ "_s" in
      let syscall_ident = fresh_generated_ident env ~base in
      Hashtbl.add env.syscall_table name syscall_ident;
      syscall_ident

let register_syscall_def env (def : syscall_def) =
  let name = Ident.to_string def.id in
  match Hashtbl.find_opt env.syscall_def_table name with
  | None -> Hashtbl.add env.syscall_def_table name def
  | Some _ ->
      error ~loc:def.loc
        (Invalid_input
           (Printf.sprintf "Syscall %s is defined more than once" name))

let register_attack_def env (def : attack_def) =
  let name = Ident.to_string def.id in
  match Hashtbl.find_opt env.attack_def_table name with
  | None -> Hashtbl.add env.attack_def_table name def
  | Some _ ->
      error ~loc:def.loc
        (Invalid_input
           (Printf.sprintf "Attack %s is defined more than once" name))

module Int : sig
  val to_term : int -> Pitptree.term_e
  val to_pterm : int -> Pitptree.pterm_e
  val to_gterm : int -> Pitptree.gterm_e
end = struct
  let zero_term () : Pitptree.term_e = term (Pitptree.PIdent (pv_ident "0"))
  let zero_pterm () : Pitptree.pterm_e = pterm (Pitptree.PPIdent (pv_ident "0"))
  let zero_gterm () : Pitptree.gterm_e = with_dummy_ext (Pitptree.PGIdent (pv_ident "0"))

  let rec unfold (t : Pitptree.term_e) (n : int) : Pitptree.term_e =
    match n with
    | 0 -> t
    | n ->
        term (Pitptree.PFunApp (pv_ident "+", [unfold t (n - 1)]))

  let unfold_minus (t : Pitptree.term_e) (n : int) : Pitptree.term_e =
    match n with
    | 0 -> t
    | n ->
        term (Pitptree.PFunApp (pv_ident ("- " ^ string_of_int n), [t]))

  let rec unfold_pterm (t : Pitptree.pterm_e) (n : int) : Pitptree.pterm_e =
    match n with
    | 0 -> t
    | n ->
        pterm (Pitptree.PPFunApp (pv_ident "+", [unfold_pterm t (n - 1)]))

  let unfold_minus_pterm (t : Pitptree.pterm_e) (n : int) : Pitptree.pterm_e =
    match n with
    | 0 -> t
    | n ->
        pterm (Pitptree.PPFunApp (pv_ident ("- " ^ string_of_int n), [t]))

  let rec unfold_gterm (t : Pitptree.gterm_e) (n : int) : Pitptree.gterm_e =
    match n with
    | 0 -> t
    | n ->
        with_dummy_ext (Pitptree.PGFunApp (pv_ident "+", [unfold_gterm t (n - 1)], None))

  let unfold_minus_gterm (t : Pitptree.gterm_e) (n : int) : Pitptree.gterm_e =
    match n with
    | 0 -> t
    | n ->
        with_dummy_ext (Pitptree.PGFunApp (pv_ident ("- " ^ string_of_int n), [t], None))

  let to_term (n : int) : Pitptree.term_e =
    if n >= 0 then
      unfold (zero_term ()) n
    else
      (* Negative integer -n is represented as `0 - n` *)
      unfold_minus (zero_term ()) (-n)

  let to_pterm (n : int) : Pitptree.pterm_e =
    if n >= 0 then
      unfold_pterm (zero_pterm ()) n
    else
      unfold_minus_pterm (zero_pterm ()) (-n)

  let to_gterm (n : int) : Pitptree.gterm_e =
    if n >= 0 then
      unfold_gterm (zero_gterm ()) n
    else
      unfold_minus_gterm (zero_gterm ()) (-n)
end

let rec compile_expr_to_term env (expr : Typed.expr) : Pitptree.term_e =
  match expr.desc with
  | Typed.Ident { id; param = Some param; _ } ->
      term @@ PFunApp (compile_ident id, [compile_expr_to_term env param])
  | Typed.Ident { id; _ } ->
      term @@ PIdent (compile_ident id)
  | Apply (id, args) ->
      term @@ Pitptree.PFunApp (compile_ident id, List.map (compile_expr_to_term env) args)
  | Tuple exprs ->
      term @@ PTuple (List.map (compile_expr_to_term env) exprs)
  | Unit ->
      term @@ PTuple []
  | String s ->
      term @@ PIdent (fresh_string_ident env s)
  | Boolean true ->
      term @@ PIdent (pv_ident "true")
  | Boolean false ->
      term @@ PIdent (pv_ident "false")
  | Integer n ->
      Int.to_term n
  | Float _ ->
      error ~loc:expr.loc
      @@ Unsupported "Float terms are not supported in ProVerif term translation"

type process_env =
  { bindings : (Typed.ident * Pitptree.pterm_e) list
  ; local_func_defs : (Typed.ident * (Typed.ident list * Typed.cmd)) list
  ; process_typ_id : Typed.ident option
  ; proc_type : Pitptree.pterm_e
  ; curr_syscall : Pitptree.pterm_e option
  ; file_channel : Pitptree.pterm_e option
  ; return_cont : (process_env -> Pitptree.pterm_e -> Pitptree.tprocess_e) option
  }

let create_process_env
    ~(local_func_defs : (Typed.ident * (Typed.ident list * Typed.cmd)) list)
    ~(process_typ_id : Typed.ident option)
    ~(proc_type : Pitptree.pterm_e)
    ~(curr_syscall : Pitptree.pterm_e option)
    ~(file_channel : Pitptree.pterm_e option)
  : process_env =
  { bindings = []
  ; local_func_defs
  ; process_typ_id
  ; proc_type
  ; curr_syscall
  ; file_channel
  ; return_cont = None
  }

let bind_process_var penv (id : Typed.ident) (value : Pitptree.pterm_e) =
  { penv with bindings = (id, value) :: List.remove_assoc id penv.bindings }

let unbind_process_var penv (id : Typed.ident) =
  { penv with bindings = List.remove_assoc id penv.bindings }

let with_process_return_cont
    penv
    (return_cont : process_env -> Pitptree.pterm_e -> Pitptree.tprocess_e)
  : process_env =
  { penv with return_cont = Some return_cont }

let find_process_var penv (id : Typed.ident) : Pitptree.pterm_e option =
  List.assoc_opt id penv.bindings

let restore_process_var penv (id : Typed.ident) (old_value : Pitptree.pterm_e option) =
  match old_value with
  | Some value -> bind_process_var penv id value
  | None -> unbind_process_var penv id

let restore_process_vars
    penv
    (saved : (Typed.ident * Pitptree.pterm_e option) list)
  : process_env =
  List.fold_left
    (fun penv (id, old_value) -> restore_process_var penv id old_value)
    penv
    saved

let find_process_var_exn ~loc penv (id : Typed.ident) : Pitptree.pterm_e =
  match find_process_var penv id with
  | Some value -> value
  | None ->
      error ~loc
        (Internal_error
           (Printf.sprintf "Loop-carried variable %s is not available"
              (Ident.to_string id)))

let find_syscall_def env (id : Typed.ident) : syscall_def option =
  Hashtbl.find_opt env.syscall_def_table (Ident.to_string id)

let find_local_func_def penv (id : Typed.ident)
  : (Typed.ident list * Typed.cmd) option =
  List.assoc_opt id penv.local_func_defs

let find_allowed_attacks
    env
    ~(process_typ_id : Typed.ident)
    ~(syscall_id : Typed.ident)
  : attack_def list =
  let allowed =
    match Hashtbl.find_opt env.allow_attack_table (Ident.to_string process_typ_id) with
    | None -> []
    | Some ids -> ids
  in
  List.filter_map
    (fun attack_id ->
       match Hashtbl.find_opt env.attack_def_table (Ident.to_string attack_id) with
       | Some def when def.syscall = syscall_id -> Some def
       | _ -> None)
    allowed

let rec compile_expr_to_gterm env (expr : Typed.expr) : Pitptree.gterm_e =
  match expr.desc with
  | Typed.Ident { id; param = Some param; _ } ->
      with_dummy_ext
        (Pitptree.PGFunApp
           (compile_ident id, [compile_expr_to_gterm env param], None))
  | Typed.Ident { id; _ } ->
      with_dummy_ext (Pitptree.PGIdent (compile_ident id))
  | Apply (id, args) ->
      with_dummy_ext
        (Pitptree.PGFunApp
           (compile_ident id, List.map (compile_expr_to_gterm env) args, None))
  | Tuple exprs ->
      with_dummy_ext
        (Pitptree.PGTuple (List.map (compile_expr_to_gterm env) exprs))
  | Unit ->
      with_dummy_ext (Pitptree.PGTuple [])
  | String s ->
      with_dummy_ext (Pitptree.PGIdent (fresh_string_ident env s))
  | Boolean true ->
      with_dummy_ext (Pitptree.PGIdent true_ident)
  | Boolean false ->
      with_dummy_ext (Pitptree.PGIdent false_ident)
  | Integer n ->
      Int.to_gterm n
  | Float _ ->
      error ~loc:expr.loc
        (Unsupported "Float terms are not supported in ProVerif query translation")

let rec compile_expr_to_pterm env penv (expr : Typed.expr) : Pitptree.pterm_e =
  match expr.desc with
  | Typed.Ident { id; param = Some param; _ } ->
      pterm (PPFunApp (compile_ident id, [compile_expr_to_pterm env penv param]))
  | Typed.Ident { id; _ } ->
      (match find_process_var penv id with
       | Some value -> value
       | None -> pterm (PPIdent (compile_ident id)))
  | Apply (id, args) ->
      pterm (PPFunApp (compile_ident id, List.map (compile_expr_to_pterm env penv) args))
  | Tuple exprs ->
      pterm (PPTuple (List.map (compile_expr_to_pterm env penv) exprs))
  | Unit ->
      pterm (PPTuple [])
  | String s ->
      pterm (PPIdent (fresh_string_ident env s))
  | Boolean true ->
      pterm (PPIdent true_ident)
  | Boolean false ->
      pterm (PPIdent false_ident)
  | Integer n ->
      Int.to_pterm n
  | Float _ ->
      error ~loc:expr.loc
        (Unsupported "Float process terms are not supported in ProVerif process translation")

let compile_channel_expr env penv (expr : Typed.expr) : Pitptree.pterm_e =
  compile_expr_to_pterm env penv expr

let current_syscall ~loc penv : Pitptree.pterm_e =
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

(*
   3.9 Syscall and Attack Encoding

   ```
   put [ c :: store(v) ];
   rest
   ```

   ```
   out(c, store(v)) |
   rest
   ```
*)
let nondet_choose_processes
    (branches : Pitptree.tprocess_e list)
  : Pitptree.tprocess_e =
  match branches with
  | [] -> process PNil
  | [branch] -> branch
  | _ ->
      let choice_id = pv_ident "rabbit_attack_choice_ch" in
      let choice_term = pterm (PPIdent choice_id) in
      let token = pterm (PPIdent true_ident) in
      let pick_one =
        List.map
          (fun branch ->
             process
               (PInput
                  ( choice_term
                  , Pitptree.PPatAny (Parsing_helper.dummy_ext, Some bitstring_ident)
                  , branch
                  , [] )))
          branches
      in
      let body =
        List.fold_left
          (fun acc branch -> process (PPar (acc, branch)))
          (process (POutput (choice_term, token, process PNil)))
          pick_one
      in
      process (PRestr (choice_id, None, channel_ident, body))

let wrap_with_access_control_get
    ~loc
    penv
    (target_type : Pitptree.pterm_e)
    (then_proc : Pitptree.tprocess_e)
    (else_proc : Pitptree.tprocess_e)
  : Pitptree.tprocess_e =
  (* No spec for allow ... [.] *)
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
    penv
    (then_proc : Pitptree.tprocess_e)
    (else_proc : Pitptree.tprocess_e)
  : Pitptree.tprocess_e =
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
    penv
    (then_proc : Pitptree.tprocess_e)
    (else_proc : Pitptree.tprocess_e)
  : Pitptree.tprocess_e =
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

let loop_state_bindings penv : (Typed.ident * Pitptree.pterm_e) list =
  (* Note: the first loop lowering conservatively carries every current
     process binding across the loop boundary. This is simple and sounder than
     forgetting mutable state, but it may be larger than necessary. A later
     refinement could compute the true loop-carried live subset. *)
  List.rev penv.bindings

let loop_state_message
    ~done_flag
    ~loc
    penv
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
    penv
    (state_ids : Typed.ident list)
    (state_pattern_ids : Typed.ident list)
  : process_env =
  List.fold_left2
    (fun penv state_id pattern_id ->
       bind_process_var penv state_id (pterm (PPIdent (compile_ident pattern_id))))
    penv
    state_ids
    state_pattern_ids

let compile_event_fact env penv (fact : Typed.fact) (body : Pitptree.tprocess_e)
  : Pitptree.tprocess_e =
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
  match fact.desc with
  | Global (name, args) ->
      register_event env name (List.length args);
      process
        (PEvent
           ( compile_name name
           , List.map (compile_expr_to_pterm env penv) args
           , None
           , body ))
  | Plain (name, args) ->
      register_event env name (List.length args);
      process
        (PEvent
           ( compile_name name
           , List.map (compile_expr_to_pterm env penv) args
           , None
           , body ))
  | _ ->
      error ~loc:fact.loc
        (Unsupported "Only plain/global event facts are supported in ProVerif event lowering")

let compile_put_fact env penv (fact : Typed.fact) (body : Pitptree.tprocess_e)
  : Pitptree.tprocess_e =
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
  match fact.desc with
  | Channel { channel; name; args } ->
      let channel_term = compile_channel_expr env penv channel in
      let payload =
        pterm
          (PPFunApp
             ( compile_name name
             , List.map (compile_expr_to_pterm env penv) args ))
      in
      wrap_with_channel_access_get ~loc:fact.loc channel_term penv
        (parallel_output (process (POutput (channel_term, payload, process PNil))) body)
        (process PNil)
  | File { path; contents } ->
      let path_term = compile_expr_to_pterm env penv path in
      let contents_term = compile_expr_to_pterm env penv contents in
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
      process (POutput (pterm (PPIdent attacker_channel_ident), compile_expr_to_pterm env penv arg, body))
  | Global (name, args) ->
      register_event env name (List.length args);
      process
        (PEvent
           ( compile_name name
           , List.map (compile_expr_to_pterm env penv) args
           , None
           , body ))
  | _ ->
      error ~loc:fact.loc
        (Unsupported "Only channel/global output facts are supported in ProVerif put lowering")

let compile_put_facts env penv (facts : Typed.fact list) (body : Pitptree.tprocess_e)
  : Pitptree.tprocess_e =
  List.fold_right (compile_put_fact env penv) facts body

let compile_event_facts env penv (facts : Typed.fact list) (body : Pitptree.tprocess_e)
  : Pitptree.tprocess_e =
  List.fold_right (compile_event_fact env penv) facts body

let eq_pterm (lhs : Pitptree.pterm_e) (rhs : Pitptree.pterm_e) : Pitptree.pterm_e =
  pterm (PPFunApp (pv_ident "=", [lhs; rhs]))

let rec compile_guard_tests
    env
    penv
    (fresh : Typed.ident list)
    (facts : Typed.fact list)
    (then_proc : Pitptree.tprocess_e)
    (else_proc : Pitptree.tprocess_e)
  : Pitptree.tprocess_e =
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
               (compile_expr_to_pterm env penv lhs)
               (compile_expr_to_pterm env penv rhs)
           in
           process
             (PTest
                ( cond
                , compile_guard_tests env penv fresh facts then_proc else_proc
                , else_proc ))
       | Neq (lhs, rhs) ->
           let cond =
             eq_pterm
               (compile_expr_to_pterm env penv lhs)
               (compile_expr_to_pterm env penv rhs)
           in
           process
             (PTest
                ( cond
                , else_proc
                , compile_guard_tests env penv fresh facts then_proc else_proc ))
       | Channel _ ->
           error ~loc:fact.loc
             (Unsupported "Nested channel guard lowering is not supported here")
       | File { path; contents } ->
           let path_term = compile_expr_to_pterm env penv path in
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
                 branch_env, compile_guard_tests env branch_env fresh facts then_proc else_proc
             | _ ->
                 let eq_then =
                   process
                     (PTest
                        ( eq_pterm payload_term (compile_expr_to_pterm env penv contents)
                        , compile_guard_tests env penv fresh facts then_proc else_proc
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
                 compile_guard_tests env branch_env fresh facts then_proc else_proc
             | _ ->
                 let eq_then =
                   process
                      (PTest
                         ( eq_pterm payload_term (compile_expr_to_pterm env penv arg)
                        , compile_guard_tests env penv fresh facts then_proc else_proc
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
       | Global ("False", []) ->
           else_proc
       | Global ("True", []) ->
           compile_guard_tests env penv fresh facts then_proc else_proc
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

type kont =
  | KStop
  | KProc of Pitptree.tprocess_e
  | KSeq of Typed.cmd * kont
  | KRestoreVar of Typed.ident * Pitptree.pterm_e option * kont
  | KRestoreVars of (Typed.ident * Pitptree.pterm_e option) list * kont
  | KLoopOutput of bool * Location.t * Pitptree.pterm_e * Typed.ident list

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

and compile_channel_guard_case
    env
    penv
    (case : Typed.case)
    (kont : kont)
    (channel : Typed.expr)
    (name : Typed.name)
    (args : Typed.expr list)
    (other_facts : Typed.fact list)
    ~loc
    ~(else_proc : Pitptree.tprocess_e)
  : Pitptree.tprocess_e =
  let payload_vars =
    List.init (List.length args) (fun i -> Ident.local (Printf.sprintf "case_arg_%d" i))
  in
  let payload_patterns =
    List.map
      (fun id -> Pitptree.PPatVar (compile_ident id, Some bitstring_ident))
      payload_vars
  in
  let input_pattern = Pitptree.PPatFunApp (compile_name name, payload_patterns) in
  let payload_terms =
    List.map (fun id -> pterm (PPIdent (compile_ident id))) payload_vars
  in
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
  let then_proc = compile_case_branch_body env branch_env case kont in
  let arg_eq_tests =
    let rec collect acc args payload_terms =
      match args, payload_terms with
      | [], [] -> List.rev acc
      | (arg : Typed.expr) :: args, payload_term :: payload_terms ->
          (match arg.desc with
           | Typed.Ident { id; _ } when is_fresh_case_var case id ->
               collect acc args payload_terms
           | _ ->
               collect
                 ((payload_term, compile_expr_to_pterm env branch_env arg) :: acc)
                 args
                 payload_terms)
      | _ -> invalid_arg "compile_channel_guard_case"
    in
    collect [] args payload_terms
  in
  let channel_term = compile_channel_expr env penv channel in
  wrap_with_channel_access_get ~loc channel_term penv
    (process
       (PInput
          ( channel_term
          , input_pattern
          , compile_guard_tests env branch_env case.fresh other_facts
              (compile_pterm_eq_tests arg_eq_tests then_proc else_proc)
              else_proc
          , [] )))
    else_proc

and compile_case_branch_body
    env
    penv
    (case : Typed.case)
    (kont : kont)
  : Pitptree.tprocess_e =
  let saved =
    List.map (fun id -> id, find_process_var penv id) case.fresh
  in
  compile_cmd env penv (KRestoreVars (saved, kont)) case.cmd

and compile_case_no_channel
    env
    penv
    (cases : Typed.case list)
    (kont : kont)
  : Pitptree.tprocess_e =
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
    | [] -> process PNil
    | case :: cases ->
        let else_proc = go cases in
        let then_proc = compile_case_branch_body env penv case kont in
        compile_guard_tests env penv case.fresh case.facts then_proc else_proc
  in
  go cases

and compile_case_channelized
    env
    penv
    (cases : Typed.case list)
    (kont : kont)
  : Pitptree.tprocess_e =
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
        let then_proc = compile_case_branch_body env branch_env case kont in
        let arg_eq_tests =
          filter_map2
            (fun (arg : Typed.expr) payload_term ->
               match arg.desc with
               | Typed.Ident { id; _ } when is_fresh_case_var case id -> None
               | _ ->
                   Some (payload_term, compile_expr_to_pterm env branch_env arg))
            args
            payload_terms
        in
        compile_guard_tests env branch_env case.fresh facts
          (compile_pterm_eq_tests arg_eq_tests then_proc else_proc)
          else_proc
  in
  let channel_term = compile_channel_expr env penv first_channel in
  wrap_with_channel_access_get ~loc:first_loc channel_term penv
    (process (PInput (channel_term, input_pattern, branches channel_guards, [])))
    (process PNil)

and compile_syscall_call
    env
    penv
    (id : Typed.ident)
    (args : Typed.expr list)
    (on_return : Pitptree.pterm_e -> Pitptree.tprocess_e)
    (on_fallthrough : Pitptree.tprocess_e)
    ~loc
  : Pitptree.tprocess_e =
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
  match find_syscall_def env id with
  | None ->
      error ~loc
        (Internal_error
           (Printf.sprintf "syscall definition for %s is not available"
              (Ident.to_string id)))
  | Some def ->
      let arg_values = List.map (compile_expr_to_pterm env penv) args in
      let mk_call_env arg_ids =
        List.fold_left2
          bind_process_var
          { penv with curr_syscall = Some (pterm (PPIdent def.syscall_ident)) }
          arg_ids
          arg_values
        |> fun call_env ->
        with_process_return_cont call_env (fun _call_env value -> on_return value)
      in
      let normal_branch =
        compile_cmd env (mk_call_env def.args) (KProc on_fallthrough) def.cmd
      in
      let attack_branches =
        match penv.process_typ_id with
        | None -> []
        | Some process_typ_id ->
            List.map
              (fun attack_def ->
                 compile_cmd env (mk_call_env attack_def.args) (KProc on_fallthrough) attack_def.cmd)
              (find_allowed_attacks env ~process_typ_id ~syscall_id:id)
      in
      nondet_choose_processes (normal_branch :: attack_branches)

and compile_local_function_call
    env
    penv
    (id : Typed.ident)
    (args : Typed.expr list)
    (on_return : Pitptree.pterm_e -> Pitptree.tprocess_e)
    (on_fallthrough : Pitptree.tprocess_e)
    ~loc
  : Pitptree.tprocess_e =
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
  match find_local_func_def penv id with
  | None ->
      error ~loc
        (Internal_error
           (Printf.sprintf "local function definition for %s is not available"
              (Ident.to_string id)))
  | Some (arg_ids, cmd) ->
      let arg_values = List.map (compile_expr_to_pterm env penv) args in
      let call_env =
        List.fold_left2
          bind_process_var
          penv
          arg_ids
          arg_values
      in
      let call_env =
        with_process_return_cont call_env (fun _call_env value -> on_return value)
      in
      compile_cmd env call_env (KProc on_fallthrough) cmd

and compile_let_binding
    env
    penv
    (kont : kont)
    (id : Typed.ident)
    (expr : Typed.expr)
    (body : Typed.cmd)
  : Pitptree.tprocess_e =
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
  | Apply (syscall_id, args) when Option.is_some (find_syscall_def env syscall_id) ->
      let old_value = find_process_var penv id in
      compile_syscall_call env penv syscall_id args
        (fun value ->
           compile_cmd env (bind_process_var penv id value)
             (KRestoreVar (id, old_value, kont))
             body)
        (compile_cmd env penv kont body)
        ~loc:expr.loc
  | Apply (func_id, args) when Option.is_some (find_local_func_def penv func_id) ->
      let old_value = find_process_var penv id in
      compile_local_function_call env penv func_id args
        (fun value ->
           compile_cmd env (bind_process_var penv id value)
             (KRestoreVar (id, old_value, kont))
             body)
        (compile_cmd env penv kont body)
        ~loc:expr.loc
  | _ ->
      let value = compile_expr_to_pterm env penv expr in
      let old_value = find_process_var penv id in
      compile_cmd env (bind_process_var penv id value)
        (KRestoreVar (id, old_value, kont))
        body

and compile_assignment
    env
    penv
    (kont : kont)
    (id_opt : Typed.ident option)
    (expr : Typed.expr)
  : Pitptree.tprocess_e =
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
  | Apply (syscall_id, args) when Option.is_some (find_syscall_def env syscall_id) ->
      let on_return =
        match id_opt with
        | None -> fun _value -> continue_cmd env penv kont
        | Some id -> fun value -> continue_cmd env (bind_process_var penv id value) kont
      in
      compile_syscall_call env penv syscall_id args on_return
        (continue_cmd env penv kont)
        ~loc:expr.loc
  | Apply (func_id, args) when Option.is_some (find_local_func_def penv func_id) ->
      let on_return =
        match id_opt with
        | None -> fun _value -> continue_cmd env penv kont
        | Some id -> fun value -> continue_cmd env (bind_process_var penv id value) kont
      in
      compile_local_function_call env penv func_id args on_return
        (continue_cmd env penv kont)
        ~loc:expr.loc
  | _ ->
      (match id_opt with
       | Some id ->
           let value = compile_expr_to_pterm env penv expr in
           continue_cmd env (bind_process_var penv id value) kont
       | None ->
           let _ = compile_expr_to_pterm env penv expr in
           continue_cmd env penv kont)

and continue_cmd env penv (kont : kont) : Pitptree.tprocess_e =
  match kont with
  | KStop -> process PNil
  | KProc proc -> proc
  | KSeq (cmd, kont) -> compile_cmd env penv kont cmd
  | KRestoreVar (id, old_value, kont) ->
      continue_cmd env (restore_process_var penv id old_value) kont
  | KRestoreVars (saved, kont) ->
      continue_cmd env (restore_process_vars penv saved) kont
  | KLoopOutput (done_flag, loc, lock_term, state_ids) ->
      process
        (POutput
           ( lock_term
           , loop_state_message ~done_flag ~loc penv state_ids
           , process PNil ))

and compile_cmd env penv (kont : kont) (cmd : Typed.cmd)
  : Pitptree.tprocess_e =
  match cmd.desc with
  | Skip -> continue_cmd env penv kont
  | Sequence (cmd1, cmd2) ->
      compile_cmd env penv (KSeq (cmd2, kont)) cmd1
  | Put facts ->
      compile_put_facts env penv facts (continue_cmd env penv kont)
  | Event facts ->
      compile_event_facts env penv facts (continue_cmd env penv kont)
  | Let (id, expr, body) ->
      compile_let_binding env penv kont id expr body
  | Assign (id_opt, expr) ->
      compile_assignment env penv kont id_opt expr
  | Return expr ->
      let value = compile_expr_to_pterm env penv expr in
      (match penv.return_cont with
       | Some return_cont -> return_cont penv value
       | None -> continue_cmd env penv kont)
  | Case cases ->
      if List.exists (fun (case : Typed.case) -> Option.is_some (extract_channel_guard case.facts)) cases then
        compile_case_channelized env penv cases kont
      else
        compile_case_no_channel env penv cases kont
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
          compile_case_branch_body env branch_env case
            (KLoopOutput (false, cmd.loc, lock_term, state_ids))
        in
        let guard_proc =
          match extract_channel_guard case.facts with
          | Some (channel, name, args, other_facts, loc) ->
              compile_channel_guard_case env branch_env case
                (KLoopOutput (false, cmd.loc, lock_term, state_ids))
                channel name args other_facts
                ~loc
                ~else_proc
          | None ->
              compile_guard_tests env branch_env case.fresh case.facts then_proc else_proc
        in
        process
          (PInput
             ( lock_term
             , loop_state_pattern ~done_flag:false state_pattern_ids
             , guard_proc
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
          compile_case_branch_body env branch_env case
            (KLoopOutput (true, cmd.loc, lock_term, state_ids))
        in
        let guard_proc =
          match extract_channel_guard case.facts with
          | Some (channel, name, args, other_facts, loc) ->
              compile_channel_guard_case env branch_env case
                (KLoopOutput (true, cmd.loc, lock_term, state_ids))
                channel name args other_facts
                ~loc
                ~else_proc
          | None ->
              compile_guard_tests env branch_env case.fresh case.facts then_proc else_proc
        in
        process
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
        process
          (PInput
             ( lock_term
             , loop_state_pattern ~done_flag:true cont_state_pattern_ids
             , continue_cmd env cont_env kont
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
           , compile_cmd env (bind_process_var penv id fresh_term)
               (KRestoreVar (id, old_value, kont))
               body ))
  | New (id, Some (name, args), body) ->
      (* `compile_generated_structure_decls` handle the declarations *)
      register_structure ~loc:cmd.loc env name (List.length args);
      let fresh_ident = compile_ident id in
      let fresh_term = pterm (PPIdent fresh_ident) in
      let old_value = find_process_var penv id in
      let struct_term =
        pterm @@
        PPFunApp
          ( structure_ctor_ident name
          , fresh_term :: List.map (compile_expr_to_pterm env penv) args )
      in
      process
        (PRestr
           ( fresh_ident
           , None
           , bitstring_ident
           , compile_cmd env (bind_process_var penv id struct_term)
               (KRestoreVar (id, old_value, kont))
               body ))
  | Get (ids, expr, name, body) ->
      register_structure ~loc:cmd.loc env name (List.length ids);
      let struct_term = compile_expr_to_pterm env penv expr in
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
           , compile_cmd env body_env
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
      let struct_term = compile_expr_to_pterm env penv expr in
      (* StructAddr(x_struct) *)
      let addr_term = structure_addr_term name struct_term in
      (* insert deleted_address_table( StructAddr(x_struct) ); ... *)
      process
        (PInsert
           (deleted_address_table_ident, [addr_term], continue_cmd env penv kont))


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
let compile_function ~loc:_loc (id : Typed.ident) (arity : int) : Pitptree.tdecl =
  let name = compile_ident id in
  let arg_tys = List.init arity (fun _ -> bitstring_ident) in
  TFunDecl (name, arg_tys, bitstring_ident, [])

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

   TODO: Lnie 40: Potential Improvement
*)
let compile_equation ~loc:_loc env (lhs : Typed.expr) (rhs : Typed.expr) : Pitptree.tdecl =
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

(* Syscalls are expanded when they are called.
   No declaration is generated at this point.
*)
let compile_syscall
    ~loc
    env
    (id : Typed.ident)
    (args : Typed.ident list)
    (cmd : Typed.cmd)
    (attack : bool)
  =
  let syscall_ident = fresh_syscall_ident env id in
  let def = { id; syscall_ident; args; cmd; attack; loc } in
  register_syscall_def env def;
  []

let compile_attack
    ~loc
    env
    (id : Typed.ident)
    (syscall : Typed.ident)
    (args : Typed.ident list)
    (cmd : Typed.cmd)
  =
  register_attack_def env { id; syscall; args; cmd; loc };
  []

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
let compile_type ~loc:_loc (id : Typed.ident) (typclass : Input.type_class) =
  let ty =
    match typclass with
    | CProc -> proc_t_ident
    | CFsys | CChan -> acc_data_t_ident
  in
  Pitptree.TConstDecl (compile_ident id, ty, [])

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
    ~loc:_loc
    env
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
           env.allow_entries <- (process_typ, target_typ, none_syscall_ident) :: env.allow_entries)
        target_typs;
      []
  | Some syscalls ->
      List.iter
        (fun target_typ ->
           List.iter
             (fun syscall ->
                let syscall_ident = fresh_syscall_ident env syscall in
                env.allow_entries <- (process_typ, target_typ, syscall_ident) :: env.allow_entries)
             syscalls)
        target_typs;
      []

let compile_allow_attack
    ~loc:(_loc : Location.t)
    env
    (process_typs : Typed.ident list)
    (attacks : Typed.ident list)
  =
  List.iter
    (fun process_typ ->
       let key = Ident.to_string process_typ in
       let prev =
         match Hashtbl.find_opt env.allow_attack_table key with
         | None -> []
         | Some prev -> prev
       in
       Hashtbl.replace env.allow_attack_table key (prev @ attacks))
    process_typs;
  []

let compile_init ~loc:(_loc : Location.t) env (id : Typed.ident) (desc : Typed.init_desc) : Pitptree.tdecl list =
  (*
     3.1 Encoding Strings, Constants, Events and Function Declarations
     3.10 Parametrized Feature Encoding

     ```
     const fresh priv_k
     const pubkey<k> = pk(priv_k<k>)
     ```

     ```
     free priv_k : bitstring [private].
     reduc forall k:param_data; pubkey(k) = pk(priv_k(k)).
     ```
  *)
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
      error ~loc (Unsupported "Parameterized channel declarations are not supported yet")
  | None ->
      Pitptree.TFree (compile_ident id, channel_ident, [pv_ident "private", None])

let process_file_channel_ident : Pitptree.ident = pv_ident "rabbit__file_ch"

let wrap_with_channel_init
    ~loc
    (args : Typed.chan_param list)
    (body : Pitptree.tprocess_e)
  : Pitptree.tprocess_e =
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
    env
    penv
    (files : (Typed.expr * Typed.ident * Typed.expr) list)
    (body : Pitptree.tprocess_e)
  : Pitptree.tprocess_e =
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
        error ~loc
          (Internal_error "Internal file channel is not available for process file setup")
  | Some file_channel ->
      let output_processes =
        List.map
          (fun ((path, _typ, contents) : Typed.expr * Typed.ident * Typed.expr) ->
             let payload =
               pterm
                 (PPTuple
                    [ compile_expr_to_pterm env penv path
                    ; compile_expr_to_pterm env penv contents
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
                  ; compile_expr_to_pterm env penv path
                  ]
                , acc )))
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
    env
    ~loc
    (id : Typed.ident)
    (param : Typed.ident option)
    (args : Typed.chan_param list)
    (typ : Typed.ident)
    (files : (Typed.expr * Typed.ident * Typed.expr) list)
    (vars : (Typed.ident * Typed.expr) list)
    (funcs : (Typed.ident * Typed.ident list * Typed.cmd) list)
    (main : Typed.cmd)
  : Pitptree.tdecl =
  let local_func_defs =
    List.map (fun (id, args, cmd) -> id, (args, cmd)) funcs
  in
  match param with
  | Some _ ->
      error ~loc @@
      Unsupported "Parameterized process declarations are not supported yet"
  | None ->
      let proc_args =
        (ptype_arg_ident, proc_t_ident, false)
        ::
        List.map
          (fun ({ channel; param; _ } : Typed.chan_param) ->
             match param with
             | Some () ->
                 error ~loc
                 @@ Unsupported "Parameterized process channel arguments are not supported yet"
             | None -> compile_ident channel, channel_ident, false)
          args
      in
      let base_penv =
        if files = [] then
          create_process_env
            ~local_func_defs
            ~process_typ_id:(Some typ)
            ~proc_type:(pterm (PPIdent ptype_arg_ident))
            ~curr_syscall:(Some (pterm (PPIdent none_syscall_ident)))
            ~file_channel:None
        else
          create_process_env
            ~local_func_defs
            ~process_typ_id:(Some typ)
            ~proc_type:(pterm (PPIdent ptype_arg_ident))
            ~curr_syscall:(Some (pterm (PPIdent none_syscall_ident)))
            ~file_channel:(Some (pterm (PPIdent process_file_channel_ident)))
      in
      let rec init_vars penv = function
        | [] ->
            wrap_with_channel_init ~loc args
              (wrap_with_file_init ~loc env penv files
                 (compile_cmd env penv KStop main))
        | (var, expr) :: vars ->
            let value = compile_expr_to_pterm env penv expr in
            init_vars (bind_process_var penv var value) vars
      in
      Pitptree.TPDef (compile_ident id, proc_args, init_vars base_penv vars)

let compile_proc_call env (proc : Typed.proc) : Pitptree.tprocess_e =
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

let compile_proc_group_desc env (proc_group : Typed.proc_group_desc) : Pitptree.tprocess_e =
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
  | Unbounded proc -> compile_proc_call env proc
  | Bounded (_id, procs) ->
      process (PRepl (parallel_processes (List.map (compile_proc_call env) procs)))

let gterm_binary (name : string) (lhs : Pitptree.gterm_e) (rhs : Pitptree.gterm_e) : Pitptree.gterm_e =
  with_dummy_ext (Pitptree.PGFunApp (pv_ident name, [lhs; rhs], None))

(* ??? Question
   Why is this encoded as `PGFunApp ("event", [PGFunApp (name, args, None)], None)`
   instead of using a dedicated event constructor?
   Answer: `Pitptree.gterm` has no dedicated event node for query terms; events in
   lemmas/queries are represented syntactically as the predicate `event(...)`
   whose single argument must itself be a function application naming the event.
   This matches the shape accepted by ProVerif's query checker. *)
let gterm_event
    (name : Typed.name)
    (args : Pitptree.gterm_e list)
  : Pitptree.gterm_e =
  with_dummy_ext @@
  Pitptree.PGFunApp
    ( pv_ident "event"
    , [with_dummy_ext @@ Pitptree.PGFunApp (compile_name name, args, None)]
    , None )

(* `g1 op g2 op .. op gn` *)
let rec combine_gterms_with ~loc op = function
  | [] ->
      error ~loc @@
      Internal_error "Cannot combine an empty list of query facts"
  | [g] -> g
  | g :: gs ->
      gterm_binary op g (combine_gterms_with ~loc op gs)

let compile_lemma_fact env (fact : Typed.fact) : Pitptree.gterm_e =
  match fact.desc with
  | Global (name, args) ->
      register_event env name (List.length args);
      gterm_event name (List.map (compile_expr_to_gterm env) args)
  | Plain (name, args) ->
      register_event env name (List.length args);
      gterm_event name (List.map (compile_expr_to_gterm env) args)
  | Eq (lhs, rhs) ->
      gterm_binary "="
        (compile_expr_to_gterm env lhs)
        (compile_expr_to_gterm env rhs)
  | Neq (lhs, rhs) ->
      gterm_binary "<>"
        (compile_expr_to_gterm env lhs)
        (compile_expr_to_gterm env rhs)
  | Channel _ | File _ ->
      (* Section 3.12 does not specify how to translate Channel and File facts *)
      error ~loc:fact.loc @@
      Unsupported "Channel/file facts are not supported in ProVerif lemma lowering"

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
    env
    ((_lemma_id, lemma) : Typed.ident * Typed.lemma) : Pitptree.tdecl =
  let envdecl =
    List.map
      (fun id -> compile_ident id, bitstring_ident)
      (match lemma.desc with
       | Typed.Plain _ -> []
       | Reachability { fresh; _ } -> fresh
       | Correspondence { fresh; _ } -> fresh)
  in
  let query =
    match lemma.desc with
    | Typed.Plain s ->
        (* No spec for Plain lemma *)
        error ~loc:lemma.loc
          (Unsupported
             (Printf.sprintf
                "Plain lemma %S is not supported in ProVerif query lowering"
                s))
    | Reachability { facts; _ } ->
        with_dummy_ext @@
        Pitptree.PRealQuery
          (combine_gterms_with ~loc:lemma.loc "&&" (List.map (compile_lemma_fact env) facts), [])
    | Correspondence { premise; conclusion; _ } ->
        with_dummy_ext @@
        Pitptree.PRealQuery
          (gterm_binary "==>"
             (compile_lemma_fact env premise)
             (compile_lemma_fact env conclusion), [])
  in
  TQuery (envdecl, [query], [])

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
    env
    (procs : Typed.proc_group_desc list)
    (lemmas : (Typed.ident * Typed.lemma) list) : Pitptree.tdecl list
  =
  if env.top_process <> None then
    error ~loc (Invalid_input "Multiple system declarations are not accepted");
  let top_process = parallel_processes (List.map (compile_proc_group_desc env) procs) in
  env.top_process <- Some top_process;
  List.map (compile_lemma env) lemmas

let compile_prelude (_env : env) : Pitptree.tdecl list =
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

let compile_generated_string_consts env : Pitptree.tdecl list =
  (*
     3.1 Encoding Strings, Constants, Events and Function Declarations

     ```
     put [ ch :: msg("hello world") ]
     ```

     ```
     const str__hello_world : bitstring.
     ...
     out(ch, msg(str__hello_world))
     ```
  *)
  Hashtbl.to_seq_values env.string_table
  |> List.of_seq
  |> List.sort_uniq compare
  |> List.map (fun id -> Pitptree.TConstDecl (id, bitstring_ident, []))

let compile_generated_syscall_consts env : Pitptree.tdecl list =
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
  Hashtbl.to_seq_values env.syscall_table
  |> List.of_seq
  |> List.sort_uniq compare
  |> List.map (fun id -> Pitptree.TConstDecl (id, syscall_t_ident, []))

let compile_generated_event_decls env : Pitptree.tdecl list =
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
  Hashtbl.to_seq env.event_table
  |> List.of_seq
  |> List.sort_uniq compare
  |> List.map (fun (name, arity) ->
      Pitptree.TEventDecl (compile_name name, List.init arity (fun _ -> bitstring_ident)))

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
let compile_generated_structure_decls env : Pitptree.tdecl list =
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
  |> List.concat_map @@ fun (name, arity) ->
      let envdecl =
        List.init (arity + 1) (fun index -> mk_var index, bitstring_ident)
      in
      let vars =
        List.map (fun (id, _ty) -> term (PIdent id)) envdecl
      in
      let struct_term =
        (* Struct(x_0, ..., x_n) *)
        term (PFunApp (structure_ctor_ident name, vars))
      in
      let ctor_decl =
        (* fun Struct (bitstring, ..., bitstring) : bitstring[data]. *)
        Pitptree.TFunDecl
          ( structure_ctor_ident name
          , List.init (arity + 1) (fun _ -> bitstring_ident)
          , bitstring_ident
          , [pv_ident "data", None] )
      in
      let addr_decl =
        (* reduc forall x_0:bitstring, ..., x_n:bitstring;
             StructAddr(Struct(x_0, ..., x_n) = x_0.
        *)
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
        (* reduc forall x_0:bitstring, ..., x_n:bitstring;
             StructPari(Struct(x_0, ..., x_n) = x_i.
        *)
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
let add_allow_inits env (body : Pitptree.tprocess_e) : Pitptree.tprocess_e =
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
    (List.rev env.allow_entries)
    body

let rec collect_process_types env (decls : Typed.decl list) =
  List.iter
    (fun (decl : Typed.decl) ->
       match decl.desc with
       | Process { id; typ; _ } -> register_process_type env id typ
       | Load (_filename, decls) -> collect_process_types env decls
       | _ -> ())
    decls

(* `load` simply expands its declaration. *)
let rec compile_load env (_filename : string) (decls : Typed.decl list) : Pitptree.tdecl list =
  List.concat_map (compile_decl env) decls

and compile_decl env (decl : Typed.decl) : Pitptree.tdecl list =
  let loc = decl.loc in
  match decl.desc with
  | Function { id; arity } ->
      [compile_function ~loc id arity]
  | Equation (lhs, rhs) ->
      [compile_equation ~loc env lhs rhs]
  | Syscall { id; args; cmd; attack } ->
      compile_syscall ~loc env id args cmd attack
  | Attack { id; syscall; args; cmd } ->
      compile_attack ~loc env id syscall args cmd
  | Type { id; typclass } ->
      [compile_type ~loc id typclass]
  | Allow { process_typ; target_typs; syscalls } ->
      compile_allow ~loc env process_typ target_typs syscalls
  | AllowAttack { process_typs; attacks } ->
      compile_allow_attack ~loc env process_typs attacks
  | Init { id; desc } ->
      compile_init ~loc env id desc
  | Channel { id; param; typ } ->
      [compile_channel ~loc id param typ]
  | Process { id; param; args; typ; files; vars; funcs; main } ->
      [compile_process env ~loc id param args typ files vars funcs main]
  | System (procs, lemmas) -> compile_system ~loc env procs lemmas
  | Load (filename, decls) -> compile_load env filename decls

let compile_program (decls : Typed.decl list) =
  let env = create_env () in
  (* Types must be first scanned for `compile_proc_call` *)
  collect_process_types env decls;
  let body = List.concat_map (compile_decl env) decls in
  let top_process = Option.value env.top_process ~default:(process PNil) in
  let top_process = add_allow_inits env top_process in
  ( compile_prelude env
    @ compile_generated_structure_decls env
    @ compile_generated_syscall_consts env
    @ compile_generated_event_decls env
    @ compile_generated_string_consts env
    @ body
  , top_process
  , None )
