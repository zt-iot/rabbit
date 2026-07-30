open Rabbit_proverif_pv_parse

type env =
  { string_table : (string, Pitptree.ident) Hashtbl.t
  }

let create_env () : env =
  { string_table = Hashtbl.create 16
  }

let pv_ident (s : string) : Pitptree.ident = s, Parsing_helper.dummy_ext

let compile_ident (id : Typed.ident) : Pitptree.ident = pv_ident (Ident.to_string id)

let bitstring_ident : Pitptree.ident = pv_ident "bitstring"

let term (t : Pitptree.term) : Pitptree.term_e = t, Parsing_helper.dummy_ext

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
  | Typed.Ident { id; _ } -> term (Pitptree.PIdent (compile_ident id))
  | Apply (id, args) ->
      term (Pitptree.PFunApp (compile_ident id, List.map (compile_expr_to_term env) args))
  | Tuple exprs -> term (Pitptree.PTuple (List.map (compile_expr_to_term env) exprs))
  | Unit -> term (Pitptree.PTuple [])
  | String s -> term (Pitptree.PIdent (fresh_string_ident env s))
  | Boolean true -> term (Pitptree.PIdent (pv_ident "true"))
  | Boolean false -> term (Pitptree.PIdent (pv_ident "false"))
  | Integer n when n >= 0 -> unfold_int (zero_term ()) n
  | Integer n -> unfold_int_minus (zero_term ()) (-n)
  | Float _ -> assert false

let compile_function (id : Typed.ident) (arity : int) : Pitptree.tdecl =
  let name = compile_ident id in
  let arg_tys = List.init arity (fun _ -> bitstring_ident) in
  Pitptree.TFunDecl (name, arg_tys, bitstring_ident, [])

let compile_equation (env : env) (lhs : Typed.expr) (rhs : Typed.expr) : Pitptree.tdecl =
  let envdecl =
    List.sort_uniq compare (Typed.vars_of_expr lhs @ Typed.vars_of_expr rhs)
    |> List.map (fun id -> compile_ident id, bitstring_ident)
  in
  let lhs_term = compile_expr_to_term env lhs in
  let rhs_term = compile_expr_to_term env rhs in
  let equality_term =
    term (Pitptree.PFunApp (pv_ident "=", [lhs_term; rhs_term]))
  in
  Pitptree.TEquation ([envdecl, Pitptree.EETerm equality_term], [])

let compile_syscall
    (_id : Typed.ident)
    (_args : Typed.ident list)
    (_cmd : Typed.cmd)
    (_attack : bool)
  =
  assert false

let compile_attack
    (_id : Typed.ident)
    (_syscall : Typed.ident)
    (_args : Typed.ident list)
    (_cmd : Typed.cmd)
  =
  assert false

let compile_type (_id : Typed.ident) (_typclass : Input.type_class) = assert false

let compile_allow
    (_process_typ : Typed.ident)
    (_target_typs : Typed.ident list)
    (_syscalls : Typed.ident list option)
  =
  assert false

let compile_allow_attack
    (_process_typs : Typed.ident list)
    (_attacks : Typed.ident list)
  =
  assert false

let compile_init (_id : Typed.ident) (_desc : Typed.init_desc) = assert false

let compile_channel
    (_id : Typed.ident)
    (_param : unit option)
    (_typ : Typed.ident)
  =
  assert false

let compile_process
    (_id : Typed.ident)
    (_param : Typed.ident option)
    (_args : Typed.chan_param list)
    (_typ : Typed.ident)
    (_files : (Typed.expr * Typed.ident * Typed.expr) list)
    (_vars : (Typed.ident * Typed.expr) list)
    (_funcs : (Typed.ident * Typed.ident list * Typed.cmd) list)
    (_main : Typed.cmd)
  =
  assert false

let compile_system
    (_procs : Typed.proc_group_desc list)
    (_lemmas : (Typed.ident * Typed.lemma) list)
  =
  assert false

let compile_load (_filename : string) (_decls : Typed.decl list) = assert false
