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

let kind_of_desc = function
  | Var _ -> "mutable variable"
  | Param -> "parameter"
  | ExtFun _ -> "external function"
  | ExtConst -> "external constant"
  | ExtSyscall _ -> "system call"
  | Const _ -> "constant"
  | Channel _ -> "channel"
  | Attack -> "attack"
  | Type CProc -> "process type"
  | Type CFsys -> "filesys type"
  | Type CChan -> "channel type"
  | Function _ -> "function"
  | Process -> "process"
  | Rho -> "rho"
;;

(* XXX Make a functor
   Fixed: use [Error.Make] to define the exception, raiser, and printer. *)
(** Conversion errors *)
type error =
  | IdentifierAlreadyBound of Name.ident
  | UnknownName of Name.ident
  | InvalidVariable of
      { ident : Ident.t
      ; def : desc
      ; use : desc
      }
  | InvalidFact of
      { name : Name.ident
      ; def : named_fact_desc
      ; use : named_fact_desc
      }
  | ArityMismatch of
      { arity : int
      ; use : int
      }
  | TypeMismatch of Type.type_ * Type.type_
(*
  | Misc of string
  | NonCallableIdentifier of Ident.t * desc
  | NonParameterizableIdentifier of Ident.t * desc
  | InvalidVariableAtAssign of Ident.t * desc
  | UnboundFact of Name.ident
  | NonCallableInExpression of Ident.t * desc
  | InvalidAnonymousAssignment
  | GlobalChannelInExpr of Ident.t
  | WildcardNotAllowed
  | StructureFactMustBePredeclared
*)

(* let misc_errorf ~loc fmt = Format.kasprintf (fun s -> error ~loc (Misc s)) fmt *)

include Error.Make (struct
    type nonrec error = error

    (** Print error description. *)
    let print_error err ppf =
      match err with
      | IdentifierAlreadyBound id -> Format.fprintf ppf "Identifier %s is already bound" id
      | UnknownName name -> Format.fprintf ppf "Unknown identifier %s" name
      | ArityMismatch { arity; use } ->
          Format.fprintf ppf "Object of arity %d takes %d arguments" arity use
      | InvalidFact { name; def; use } ->
          Format.fprintf
            ppf
            "%s is %s fact but used as %s"
            name
            (string_of_named_fact_desc def)
            (string_of_named_fact_desc use)
      | InvalidVariable { ident; def; use } ->
          Format.fprintf
            ppf
            "%t is %s but used as %s"
            (Ident.print ident)
            (kind_of_desc def)
            (kind_of_desc use)
      | TypeMismatch (expected, actual) ->
          Format.fprintf
            ppf
            "Expected a value of type %a but found %a"
            (fun ppf typ -> Type.print_type typ ppf)
            expected
            (fun ppf typ -> Type.print_type typ ppf)
            actual
  end)

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




let must_be_fresh ~loc env name =
  if mem env name then error ~loc (IdentifierAlreadyBound name)
;;

let find ~loc env name =
  match find_opt env name with
  | None -> error ~loc (UnknownName name)
  | Some id_desc -> id_desc
;;

let find_desc ~loc env name desc =
  let id, desc' = find ~loc env name in
  if desc <> desc'
  then error ~loc @@ InvalidVariable { ident = id; def = desc'; use = desc }
  else id
;;

let add_global ~loc env name desc =
  must_be_fresh ~loc env name;
  let id = Ident.global name in
  add env id desc, id
;;

let add_fact ~loc env name (desc, argument_types) =
  match find_fact_opt env name with
  | Some (desc', argument_types') ->
      if desc <> desc'
      then error ~loc @@ InvalidFact { name; def = desc'; use = desc }
      else (
        match argument_types, argument_types' with
        | Some types, Some types' ->
            if List.length types <> List.length types' then
              error ~loc @@
              ArityMismatch { arity= List.length types; use= List.length types' };
            (try List.iter2 Type.unify types types' with
             | Type.Cannot_unify (expected, actual) ->
                 error ~loc @@ TypeMismatch (expected, actual))
        | None, Some _ -> ()
        | Some _, None -> update_fact env name (desc, argument_types)
        | None, None -> ())
  | None -> update_fact env name (desc, argument_types)
;;
