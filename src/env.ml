type var_desc = Syntax.variable_desc =
  | Top of int
  | Loc of int
  | Meta of int
  | MetaNew of int
  | Param

type named_fact_desc =
  | NoName
  | Global
  | Channel
  | Process

let string_of_named_fact_desc = function
  | NoName -> "plain"
  | Global -> "global"
  | Channel -> "channel"
  | Process -> "process"

type desc =
  | Var of var_desc
  | ExtFun of int
  | ExtConst
  | ExtSyscall of int
  | Const of bool
  | Channel of bool * Ident.t
  | Attack
  | Type of Input.type_class
  | Function of int
  | Process

let print_desc desc ppf =
  let f = Format.fprintf in
  match desc with
  | Var (Top i) -> f ppf "Top %d" i
  | Var (Loc i) -> f ppf "Loc %d" i
  | Var (Meta i) -> f ppf "Meta %d" i
  | Var (MetaNew i) -> f ppf "MetaNew %d" i
  | Var Param -> f ppf "Param"
  | ExtFun i -> f ppf "ExtFun (arity=%d)" i
  | ExtConst -> f ppf "ExtConst"
  | ExtSyscall i -> f ppf "ExtSyscall (arity=%d)" i
  | Const b -> f ppf "Const (param=%b)" b
  | Channel (b, id) -> f ppf "Channel (param=%b) : %t" b (Ident.print id)
  | Attack -> f ppf "Attack"
  | Type CProc -> f ppf "ty process"
  | Type CFsys -> f ppf "ty filesys"
  | Type CChan -> f ppf "ty channel"
  | Function i -> f ppf "Function (arity=%d)" i
  | Process -> f ppf "Process"

type t = {
  vars : (Ident.t * desc) list;
  facts : (Name.ident * (named_fact_desc * int)) list ref
}

let empty () = { vars= []; facts= ref [] }

let find_opt env name =
  List.find_opt (fun (id, _desc) -> name = fst id) env.vars

let find_opt_by_id env id = List.assoc_opt id env.vars

let mem env name = find_opt env name <> None

let add env id desc = { env with vars = (id, desc) :: env.vars }

let add_fact env name fact_desc =
  if List.mem_assoc name !(env.facts) then assert false;
  env.facts := (name, fact_desc) :: !(env.facts)

let find_fact_opt env name = List.assoc_opt name !(env.facts)
