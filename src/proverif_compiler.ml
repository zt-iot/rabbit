open Rabbit_proverif_pv_parse

let pv_ident (s : string) : Pitptree.ident = s, Parsing_helper.dummy_ext

let compile_ident (id : Typed.ident) : Pitptree.ident = pv_ident (Ident.to_string id)

let bitstring_ident : Pitptree.ident = pv_ident "bitstring"

let term (t : Pitptree.term) : Pitptree.term_e = t, Parsing_helper.dummy_ext

let rec compile_expr_to_term (expr : Typed.expr) : Pitptree.term_e =
  match expr.desc with
  | Typed.Ident { id; _ } -> term (Pitptree.PIdent (compile_ident id))
  | Apply (id, args) ->
      term (Pitptree.PFunApp (compile_ident id, List.map compile_expr_to_term args))
  | Tuple exprs -> term (Pitptree.PTuple (List.map compile_expr_to_term exprs))
  | Unit -> term (Pitptree.PTuple [])
  | String _ -> assert false
  | Boolean _ -> assert false
  | Integer _ -> assert false
  | Float _ -> assert false

let compile_function (id : Typed.ident) (arity : int) : Pitptree.tdecl =
  let name = compile_ident id in
  let arg_tys = List.init arity (fun _ -> bitstring_ident) in
  Pitptree.TFunDecl (name, arg_tys, bitstring_ident, [])

let compile_equation (lhs : Typed.expr) (rhs : Typed.expr) : Pitptree.tdecl =
  let envdecl =
    List.sort_uniq compare (Typed.vars_of_expr lhs @ Typed.vars_of_expr rhs)
    |> List.map (fun id -> compile_ident id, bitstring_ident)
  in
  let lhs_term = compile_expr_to_term lhs in
  let rhs_term = compile_expr_to_term rhs in
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
