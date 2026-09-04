type named_fact_desc =
  | Channel
  | Structure
  | Plain
  | Global

let string_of_named_fact_desc = function
  | Channel -> "channel"
  | Structure -> "struture"
  | Plain -> "plain"
  | Global -> "global"

type desc =
  | Var of Type.type_
  | Param
  | ExtFun of Type.callable_type
  | ExtConst
  | ExtSyscall of Type.callable_type
  | Const of bool
  | Channel of bool * Ident.t
  | Attack
  | Type of Input.type_class
  | Function of Type.callable_type
  | Process
  | Rho

let callable_type_of_desc = function
  | ExtFun typ | ExtSyscall typ | Function typ -> Some typ
  | Var _ | Param | ExtConst | Const _ | Channel _ | Attack | Type _ | Process | Rho -> None

let type_of_desc = function
  | Var typ -> Some typ
  | Param -> Some TParameter
  | ExtConst | Const _ -> Some TValue
  | Channel _ -> Some TChannel
  | Rho -> Some TValue
  | ExtFun _ | ExtSyscall _ | Attack | Type _ | Function _ | Process -> None

let print_desc desc ppf =
  let f = Format.fprintf in
  match desc with
  | Var typ -> f ppf "Var : %a" (fun ppf typ -> Type.print_type typ ppf) typ
  | Param -> f ppf "Param"
  | ExtFun typ -> f ppf "ExtFun (arity=%d)" (List.length typ.argument_types)
  | ExtConst -> f ppf "ExtConst"
  | ExtSyscall typ -> f ppf "ExtSyscall (arity=%d)" (List.length typ.argument_types)
  | Const b -> f ppf "Const (param=%b)" b
  | Channel (b, id) -> f ppf "Channel (param=%b) : %t" b (Ident.print id)
  | Attack -> f ppf "Attack"
  | Type CProc -> f ppf "ty process"
  | Type CFsys -> f ppf "ty filesys"
  | Type CChan -> f ppf "ty channel"
  | Function typ -> f ppf "Function (arity=%d)" (List.length typ.argument_types)
  | Process -> f ppf "Process"
  | Rho -> f ppf "Rho"

type t =
  { vars : (Ident.t * desc) list
  ; mutable facts : (Name.ident * (named_fact_desc * Type.type_ list option)) list
    (* The fact environment is global therefore implemented as mutable *)
  }

let bindings x = x.vars

let empty () = { vars= []; facts= [] }

let singleton id desc = { vars= [(id, desc)]; facts= [] }

let find_opt env name =
  List.find_opt (fun (id, _desc) -> name = fst id) env.vars

let find_opt_by_id env id = List.assoc_opt id env.vars

let mem env name = find_opt env name <> None

let add env id desc = { env with vars = (id, desc) :: env.vars }

let update_fact env name v =
  let rec update rev_facts = function
    | [] -> (name, v) :: List.rev rev_facts
    | (name', _) :: facts when name = name' ->
        List.rev_append rev_facts ((name, v) :: facts)
    | f :: facts -> update (f :: rev_facts) facts
  in
  env.facts <- update [] env.facts

let find_fact_opt env name = List.assoc_opt name env.facts
