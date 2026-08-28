type named_fact_desc =
  | Channel
  | Structure of Input.field_type list
  | Plain
  | Global

type type_ =
  | TValue
  | TChannel
  | TParameter
  | TVar of type_var ref

and type_var =
  | Unbound of int
  | Link of type_

type callable_type =
  { argument_types : type_ list
  ; result_type : type_
  }

exception Cannot_unify of type_ * type_

let next_type_var = ref 0
let type_vars = ref []

let fresh_type () =
  let id = !next_type_var in
  incr next_type_var;
  let var = ref (Unbound id) in
  type_vars := (id, var) :: !type_vars;
  TVar var

let type_variable_mark () = !next_type_var

let rec repr = function
  | TVar ({ contents = Link typ } as var) ->
      let typ = repr typ in
      var := Link typ;
      typ
  | typ -> typ

let unify typ1 typ2 =
  let typ1 = repr typ1 in
  let typ2 = repr typ2 in
  match typ1, typ2 with
  | TValue, TValue | TChannel, TChannel | TParameter, TParameter -> ()
  | TVar var1, TVar var2 when var1 == var2 -> ()
  | TVar ({ contents = Unbound _ } as var), typ
  | typ, TVar ({ contents = Unbound _ } as var) -> var := Link typ
  | _ -> raise (Cannot_unify (typ1, typ2))

let default_type typ =
  match repr typ with
  | TVar ({ contents = Unbound _ } as var) ->
      var := Link TValue;
      TValue
  | typ -> typ

let default_types_since mark =
  let current, older =
    List.partition (fun (id, _) -> id >= mark) !type_vars
  in
  List.iter
    (fun (_id, var) ->
       match !var with
       | Unbound _ -> var := Link TValue
       | Link _ -> ())
    current;
  type_vars := older

let discard_types_since mark =
  type_vars := List.filter (fun (id, _) -> id < mark) !type_vars

let type_of_field_type = function
  | Input.Value -> TValue
  | Channel -> TChannel
  | Parameter -> TParameter

let print_type typ ppf =
  match repr typ with
  | TValue -> Format.pp_print_string ppf "value"
  | TChannel -> Format.pp_print_string ppf "channel"
  | TParameter -> Format.pp_print_string ppf "parameter"
  | TVar { contents = Unbound id } -> Format.fprintf ppf "'%d" id
  | TVar { contents = Link _ } -> assert false

let string_of_named_fact_desc = function
  | Channel -> "channel"
  | Structure _ -> "struture"
  | Plain -> "plain"
  | Global -> "global"

type desc =
  | Var of type_
  | Param
  | ExtFun of callable_type
  | ExtConst
  | ExtSyscall of callable_type
  | Const of bool
  | Channel of bool * Ident.t
  | Attack
  | Type of Input.type_class
  | Function of callable_type
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
  | Var typ -> f ppf "Var : %a" (fun ppf typ -> print_type typ ppf) typ
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
  ; facts : (Name.ident * (named_fact_desc * type_ list option)) list ref
    (* The fact environment is global therefore implemented as mutable *)
  }

let empty () = { vars= []; facts= ref [] }

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
  env.facts := update [] !(env.facts)

let find_fact_opt env name = List.assoc_opt name !(env.facts)
