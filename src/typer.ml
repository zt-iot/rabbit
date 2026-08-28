(** Conversion errors *)
type error =
  | Misc of string
  | IdentifierAlreadyBound of Name.ident
  | UnknownName of Name.ident
  | ArityMismatch of
      { arity : int
      ; use : int
      }
  | NonCallableIdentifier of Ident.t * Env.desc
  | NonParameterizableIdentifier of Ident.t * Env.desc
  | InvalidFact of
      { name : Name.ident
      ; def : Env.named_fact_desc
      ; use : Env.named_fact_desc
      }
  | InvalidVariable of
      { ident : Ident.t
      ; def : Env.desc
      ; use : Env.desc
      }
  | InvalidVariableAtAssign of Ident.t * Env.desc
  | UnboundFact of Name.ident
  | NonCallableInExpression of Ident.t * Env.desc
  | InvalidAnonymousAssignment
  | GlobalChannelInExpr of Ident.t
  | WildcardNotAllowed
  | StructureFactMustBePredeclared
  | TypeMismatch of Env.type_ * Env.type_

exception Error of error Location.located

(** [error ~loc err] raises the given runtime error. *)
let error ~loc err = Stdlib.raise (Error (Location.locate ~loc err))

let misc_errorf ~loc fmt = Format.kasprintf (fun s -> error ~loc (Misc s)) fmt

let kind_of_desc = function
  | Env.Var _ -> "mutable variable"
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

(** Print error description. *)
let print_error err ppf =
  match err with
  | Misc s -> Format.fprintf ppf "%s" s
  | IdentifierAlreadyBound id -> Format.fprintf ppf "Identifier %s is already bound" id
  | UnknownName name -> Format.fprintf ppf "Unknown identifier %s" name
  | ArityMismatch { arity; use } ->
      Format.fprintf ppf "Object of arity %d takes %d arguments" arity use
  | NonCallableIdentifier (id, desc) ->
      Format.fprintf
        ppf
        "%s %t cannot be called"
        (String.capitalize_ascii (kind_of_desc desc))
        (Ident.print id)
  | NonCallableInExpression (id, desc) ->
      Format.fprintf
        ppf
        "%s %t can be called only at command x := %t(..)"
        (String.capitalize_ascii (kind_of_desc desc))
        (Ident.print id)
        (Ident.print id)
  | NonParameterizableIdentifier (id, desc) ->
      Format.fprintf
        ppf
        "%s variable %t cannot be parameterized"
        (String.capitalize_ascii (kind_of_desc desc))
        (Ident.print id)
  | InvalidFact { name; def; use } ->
      Format.fprintf
        ppf
        "%s is %s fact but used as %s"
        name
        (Env.string_of_named_fact_desc def)
        (Env.string_of_named_fact_desc use)
  | InvalidVariable { ident; def; use } ->
      Format.fprintf
        ppf
        "%t is %s but used as %s"
        (Ident.print ident)
        (kind_of_desc def)
        (kind_of_desc use)
  | InvalidVariableAtAssign (id, desc) ->
      Format.fprintf
        ppf
        "%s variable %t cannot be assigned"
        (String.capitalize_ascii (kind_of_desc desc))
        (Ident.print id)
  | UnboundFact id -> Format.fprintf ppf "Unbound fact %s" id
  | InvalidAnonymousAssignment ->
      Format.pp_print_string ppf "Pure expression is used at _ := e, which has no effect"
  | GlobalChannelInExpr id ->
      Format.fprintf ppf "Global channel %t cannot be used in an expression" (Ident.print id)
  | WildcardNotAllowed ->
      Format.pp_print_string ppf "Wildcard '_' is only allowed in case/while guards"
  | StructureFactMustBePredeclared ->
      Format.pp_print_string ppf "Structure fact must be predeclared"
  | TypeMismatch (expected, actual) ->
      Format.fprintf
        ppf
        "Expected a value of type %a but found %a"
        (fun ppf typ -> Env.print_type typ ppf) expected
        (fun ppf typ -> Env.print_type typ ppf) actual
;;

let unify ~loc expected actual =
  try Env.unify expected actual with
  | Env.Cannot_unify (expected, actual) -> error ~loc @@ TypeMismatch (expected, actual)
;;

let fresh_callable arity =
  Env.
    { argument_types = List.init arity (fun _ -> fresh_type ())
    ; result_type = fresh_type ()
    }
;;

let type_of_field_type = Env.type_of_field_type

let type_of_value_desc = Env.type_of_desc

let type_of_expr = Typed.type_of_expr
;;

module Env : sig
  include module type of struct
    include Env
  end

  val find : loc:Location.t -> t -> Name.ident -> Ident.t * Env.desc
  val find_desc : loc:Location.t -> t -> Name.ident -> Env.desc -> Ident.t

  (** Fails if the name is bound in the environment *)
  val add_global : loc:Location.t -> t -> Name.ident -> Env.desc -> t * Ident.t

  val add_fact : loc:Location.t -> t -> Name.ident -> named_fact_desc * type_ list option -> unit
end = struct
  include Env

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
              (try List.iter2 Env.unify types types' with
               | Env.Cannot_unify (expected, actual) ->
                   error ~loc @@ TypeMismatch (expected, actual))
          | None, Some _ -> ()
          | Some _, None -> update_fact env name (desc, argument_types)
          | None, None -> ())
    | None -> update_fact env name (desc, argument_types)
  ;;
end

let check_arity ~loc ~arity ~use =
  if arity <> use then error ~loc @@ ArityMismatch { arity; use }
;;

let rec type_expr ?(allow_wildcard = false) env (e : Input.expr) : Typed.expr =
  let loc = e.loc in
  let desc =
    match e.data with
    | Wildcard ->
        if allow_wildcard
        then (
          let id = Ident.local "_" in
          Typed.Ident { id; desc = Var (Env.fresh_type ()); param = None })
        else error ~loc WildcardNotAllowed
    | Boolean b -> Typed.Boolean b
    | String s -> String s
    | Integer i -> Integer i
    | Float f -> Float f
    | Var name ->
        let id, desc = Env.find ~loc env name in
        (* Global channels cannot be used in exprs.
           Channels must be given as [chan_arg]s *)
        (match desc  with
         | Channel _ when Ident.is_global id -> error ~loc @@ GlobalChannelInExpr id
         | _ -> ()
        );
        Ident { id; desc; param = None }
    | Tuple es ->
        assert (List.length es > 0);
        Tuple (List.map (type_expr ~allow_wildcard env) es)
    | Apply (f, es) ->
        let es = List.map (type_expr ~allow_wildcard env) es in
        let use = List.length es in
        (match Env.find ~loc env f with
         | id, (ExtFun typ | ExtSyscall typ | Function typ) ->
             check_arity ~loc ~arity:(List.length typ.argument_types) ~use;
             List.iter2
               (fun expected (expr : Typed.expr) ->
                  unify ~loc:expr.loc expected (type_of_expr expr))
               typ.argument_types
               es;
             Apply (id, es)
         | id, desc ->
             error ~loc @@ NonCallableIdentifier (id, desc))
    | Param (f, e) (* [f<e>] *) ->
        (match Env.find ~loc env f with
         | id, ((Const _ | Channel _) as desc) ->
             let e = type_expr ~allow_wildcard env e in
             Ident { id; desc; param= Some e }
         | id, desc -> error ~loc @@ NonParameterizableIdentifier (id, desc))
  in
  { loc; env; desc }
;;

(* If [f] is a system call or a funciton w/ definition, an application of [f] is only
   allowed at commands [x := f (..)].
*)

let check_apps e =
  let rec aux (e : Typed.expr) =
    match e.desc with
    | Boolean _ | String _ | Integer _ | Float _ | Unit -> ()
    | Ident _ -> ()
    | Apply (id, es) ->
        let desc = Option.get @@ Env.find_opt_by_id e.env id in
        (match desc with
         | ExtFun _ -> ()
         | ExtSyscall _ | Function _ -> error ~loc:e.loc @@ NonCallableInExpression (id, desc)
         | _ -> assert false);
        List.iter aux es
    | Tuple es -> List.iter aux es
  in
  aux e

let type_expr ?(at_assignment = false) ?(allow_wildcard = false) env (e : Input.expr)
  : Typed.expr =
  let e = type_expr ~allow_wildcard env e in
  if not at_assignment then check_apps e;
  e
;;

let type_fact ?(allow_wildcard = false) env (fact : Input.fact) : Typed.fact =
  let loc = fact.loc in
  let desc : Typed.fact' =
    match fact.data with
    | ProcessFact _ -> assert false (* Unused *)
    | Fact (name, es) ->
        (* Which fact? For strucure? *)
        let nes = List.length es in
        let es = List.map (type_expr ~allow_wildcard env) es in
        let argument_types = List.map type_of_expr es in
        (match Env.find_fact_opt env name with
         | None ->
             Env.add_fact ~loc env name (Plain, Some argument_types);
             Typed.Plain (name, es)
         | Some (Plain, Some types) ->
             check_arity ~loc ~arity:(List.length types) ~use:nes;
             List.iter2 (unify ~loc) types argument_types;
             Plain (name, es)
         | Some (Plain, None) -> assert false
         | Some (desc, _) ->
             error ~loc @@ InvalidFact { name; def= desc; use= Plain }
        )
    | GlobalFact (name, es) ->
        let es = List.map (type_expr ~allow_wildcard env) es in
        Env.add_fact ~loc env name (Global, Some (List.map type_of_expr es));
        Global (name, es)
    | ChannelFact (e, name, es) ->
        let e = type_expr ~allow_wildcard env e in
        unify ~loc:e.loc TChannel (type_of_expr e);
        let es = List.map (type_expr ~allow_wildcard env) es in
        Env.add_fact ~loc env name (Channel, Some (List.map type_of_expr es));
        Channel { channel = e; name; args = es }
    | EqFact (e1, e2) ->
        let e1 = type_expr ~allow_wildcard env e1 in
        let e2 = type_expr ~allow_wildcard env e2 in
        unify ~loc (type_of_expr e1) (type_of_expr e2);
        Eq (e1, e2)
    | NeqFact (e1, e2) ->
        let e1 = type_expr ~allow_wildcard env e1 in
        let e2 = type_expr ~allow_wildcard env e2 in
        unify ~loc (type_of_expr e1) (type_of_expr e2);
        Neq (e1, e2)
    | FileFact (e1, e2) ->
        let e1 = type_expr ~allow_wildcard env e1 in
        let e2 = type_expr ~allow_wildcard env e2 in
        unify ~loc:e1.loc TValue (type_of_expr e1);
        unify ~loc:e2.loc TValue (type_of_expr e2);
        File { path = e1; contents = e2 }
  in
  { env; loc; desc }
;;

let extend_with_args env (args : Name.ident list) f =
  let env, rev_ids =
    List.fold_left
      (fun (env, rev_ids) name ->
         let id = Ident.local name in
         Env.add env id (f id), id :: rev_ids)
      (env, [])
      args
  in
  env, List.rev rev_ids
;;

let type_facts ?(allow_wildcard = false) env facts =
  List.map (type_fact ~allow_wildcard env) facts
;;

let rec infer_cmd_result_type (cmd : Typed.cmd) =
  match cmd.desc with
  | Expr expr -> type_of_expr expr
  | Sequence (cmd1, cmd2) ->
      ignore (infer_cmd_result_type cmd1);
      infer_cmd_result_type cmd2
  | Let (_, _, body) | New (_, _, body) | Get (_, _, _, body) ->
      infer_cmd_result_type body
  | Case [] -> TValue
  | Case (case :: cases) ->
      let typ = infer_cmd_result_type case.cmd in
      List.iter
        (fun (case : Typed.case) ->
           unify ~loc:case.cmd.loc typ (infer_cmd_result_type case.cmd))
        cases;
      typ
  | While (repeat_cases, until_cases) ->
      List.iter
        (fun (case : Typed.case) ->
           unify ~loc:case.cmd.loc TValue (infer_cmd_result_type case.cmd))
        (repeat_cases @ until_cases);
      TValue
  | Skip | Put _ | Assign _ | Event _ | Del _ -> TValue
;;

let type_structure_fact ~loc env name es =
  (* [str] must be a structure fact *)
  let nes = List.length es in
  match Env.find_fact_opt env name with
  | None -> error ~loc StructureFactMustBePredeclared
  | Some (Structure ftys, Some types) ->
      if nes = List.length ftys then types
      else
        error ~loc @@
        ArityMismatch { arity= List.length ftys; use= nes }
  | Some (Structure _, None) -> assert false
  | Some (desc', _) ->
      (* Not a structure *)
      error ~loc @@
      InvalidFact { name; def = desc'; use = Structure (List.map (fun _ -> Input.Value) es) }
;;

let rec type_cmd (env : Env.t) (cmd : Input.cmd) : Typed.cmd =
  let loc = cmd.loc in
  let desc =
    match cmd.data with
    | Input.Skip -> Typed.Skip
    | Sequence (c1, c2) ->
        let c1 = type_cmd env c1 in
        let c2 = type_cmd env c2 in
        Sequence (c1, c2)
    | Put facts ->
        let facts = type_facts env facts in
        Put facts
    | Let (name, e, cmd) ->
        let e = type_expr ~at_assignment:true env e in
        let id = Ident.local name in
        let env' = Env.add env id (Var (type_of_expr e)) in
        let cmd = type_cmd env' cmd in
        Let (id, e, cmd)
    | Assign (None, e) ->
        let e = type_expr ~at_assignment:true env e in
        (match e.desc with
         | Apply _ -> Assign (None, e)
         | _ ->
             (* _ := e  where e is not an application *)
             error ~loc @@ InvalidAnonymousAssignment
        )
    | Assign (Some name, e) ->
        let id, vdesc = Env.find ~loc env name in
        (match vdesc with
         | Var _ -> ()
         | desc -> error ~loc @@ InvalidVariableAtAssign (id, desc));
        let e = type_expr env ~at_assignment:true e in
        let variable_type = Option.get (type_of_value_desc vdesc) in
        unify ~loc:e.loc variable_type (type_of_expr e);
        Assign (Some id, e)
    | Case cases -> Case (type_cases env cases)
    | While (cases1, cases2) ->
        let cases1 = type_cases env cases1 in
        let cases2 = type_cases env cases2 in
        While (cases1, cases2)
    | Event facts ->
        let facts = type_facts env facts in
        Event facts
    | Expr e ->
        let e = type_expr env e in
        Expr e
    | New (name, str_es_opt, cmd) ->
        (* allocation, [new x := S(e1,..,en) in c] or [new x in c] *)
        let str_es_opt =
          Option.map
            (fun (str, es) ->
               (* [str] must be a structure fact *)
               let expected_types = type_structure_fact ~loc env str es in
               let es = List.map (type_expr env) es in
               List.iter2
                 (fun expected (expr : Typed.expr) ->
                    unify ~loc:expr.loc expected (type_of_expr expr))
                 expected_types
                 es;
               str, es)
            str_es_opt
        in
        let id = Ident.local name in
        let env' = Env.add env id (Var TValue) in
        let cmd = type_cmd env' cmd in
        New (id, str_es_opt, cmd)
    | Get (names, e, str, cmd) ->
        (* fetch, [let x1,...,xn := e.S in c] *)
        let e = type_expr env e in
        let field_types = type_structure_fact ~loc env str names in
        unify ~loc:e.loc TValue (type_of_expr e);
        let ids = List.map Ident.local names in
        let env' =
          List.fold_left2
            (fun env' id typ -> Env.add env' id (Var typ))
            env
            ids
            field_types
        in
        let cmd = type_cmd env' cmd in
        Get (ids, e, str, cmd)
    | Del (e, str) ->
        (* deletion, [delete e.S] *)
        let e = type_expr env e in
        (match Env.find_fact_opt env str with
         | Some (Structure _, _types) -> ()
         | Some (desc, _) ->
             error ~loc @@ InvalidFact { name = str; def = desc; use = Structure [] (* dummy *) }
         | None -> error ~loc @@ UnboundFact str);
        unify ~loc:e.loc TValue (type_of_expr e);
        Del (e, str)
  in
  { loc; env; desc }

and type_cases env cases : Typed.case list = List.map (type_case env) cases

and type_case env (facts, cmd) : Typed.case =
  (* facts -> cmd *)
  let vs =
    List.fold_left
      (fun vs fact -> Name.Set.union vs (Input.vars_of_fact fact))
      Name.Set.empty
      facts
  in
  let fresh = Name.Set.filter (fun v -> not (Env.mem env v)) vs in
  let fresh_ids = Name.Set.fold (fun name ids -> Ident.local name :: ids) fresh [] in
  let env' =
    List.fold_left (fun env id -> Env.add env id (Var (Env.fresh_type ()))) env fresh_ids
  in
  let facts = type_facts ~allow_wildcard:true env' facts in
  let cmd = type_cmd env' cmd in
  Typed.{ fresh = fresh_ids; facts; cmd }
;;

let type_process
      ~loc
      env
      (name : Name.ident)
      (param_opt : Name.ident option)
      args
      proc_ty
      files
      vars
      funcs
      main
  : Env.t * Typed.decl
  =
  (* [ process name<param>(ch1 : chty1, .., chn : chtyn) : proc_ty {n
          file path : filety = contents ...
          var id = e ...
          function fid(args) { c }
          main ...
        }
     ] *)
  let param_opt, args, proc_ty, files, vars, funcs, main =
    let env', param_opt =
      match param_opt with
      | None -> env, None
      | Some name ->
          let id = Ident.local name in
          Env.add env id Param, Some id
    in
    let env', rev_args =
      List.fold_left
        (fun (env, rev_args) (Input.ChanParam { id = chanid; param; typ = chanty }) ->
           let with_param = param <> None in
           let chanty = Env.find_desc ~loc env chanty (Type CChan) in
           let chanid = Ident.local chanid in
           ( Env.add env chanid (Channel (with_param, chanty))
           , Typed.{ channel=chanid; param; typ= chanty } :: rev_args ))
        (env', [])
        args
    in
    let args = List.rev rev_args in
    let proc_ty =
      match Env.find ~loc env proc_ty with
      | proc_ty, Type CProc -> proc_ty
      | id, desc ->
          error ~loc @@ InvalidVariable { ident = id; def = desc; use = Type CProc }
    in
    let files =
      List.map
        (fun (path, filety, contents) ->
           let path = type_expr env' path in
           unify ~loc:path.loc TValue (type_of_expr path);
           let filety = Env.find_desc ~loc env' filety (Type CFsys) in
           let contents = type_expr env' contents in
           unify ~loc:contents.loc TValue (type_of_expr contents);
           path, filety, contents)
        files
    in
    let env', rev_vars =
      List.fold_left
        (fun (env, rev_vars) (name, e) ->
           let e = type_expr env e in
           let id = Ident.local name in
           let env' = Env.add env id (Var (type_of_expr e)) in
           env', (id, e) :: rev_vars)
        (env', [])
        vars
    in
    let vars = List.rev rev_vars in
    let env', rev_funcs =
      List.fold_left
        (fun (env', rev_funcs) (fname, args, c) ->
           let fid = Ident.local fname in
           let typ = fresh_callable (List.length args) in
           let env_with_function = Env.add env' fid (Function typ) in
           let env'', args =
             let argument_types = ref typ.argument_types in
             extend_with_args env_with_function args @@ fun _id ->
             match !argument_types with
             | argument_type :: rest ->
                 argument_types := rest;
                 Var argument_type
             | [] -> assert false
           in
           let c = type_cmd env'' c in
           unify ~loc:c.loc typ.result_type (infer_cmd_result_type c);
           env_with_function, (fid, args, c) :: rev_funcs)
        (env', [])
        funcs
    in
    let funcs = List.rev rev_funcs in
    let main = type_cmd env' main in
    ignore (infer_cmd_result_type main);
    param_opt, args, proc_ty, files, vars, funcs, main
  in
  let env', id = Env.add_global ~loc env name Process in
  let decl : Typed.decl =
    { env
    ; loc
    ; desc =
        Process { id; param = param_opt; args; typ = proc_ty; files; vars; funcs; main }
    }
  in
  env', decl
;;

let type_lemma env (lemma : Input.lemma) : Env.t * (Ident.t * Typed.lemma) =
  let loc = lemma.loc in
  let (Lemma (name, prop)) = lemma.data in
  let desc =
    match prop.data with
    | PlainString s -> (Typed.Plain s : Typed.lemma')
    | Reachability facts ->
        let vs = Input.vars_of_facts facts in
        let fresh = Name.Set.filter (fun v -> not (Env.mem env v)) vs in
        let fresh_ids =
          Name.Set.fold (fun name ids -> Ident.local name :: ids) fresh []
        in
        let env' =
          List.fold_left
            (fun env id -> Env.add env id (Var (Env.fresh_type ())))
            env
            fresh_ids
        in
        let facts = type_facts env' facts in
        Reachability { fresh = fresh_ids; facts }
    | Correspondence (f1, f2) ->
        let vs = Name.Set.union (Input.vars_of_fact f1) (Input.vars_of_fact f2) in
        let fresh = Name.Set.filter (fun v -> not (Env.mem env v)) vs in
        let fresh_ids =
          Name.Set.fold (fun name ids -> Ident.local name :: ids) fresh []
        in
        let env' =
          List.fold_left
            (fun env id -> Env.add env id (Var (Env.fresh_type ())))
            env
            fresh_ids
        in
        let f1 = type_fact env' f1 in
        let f2 = type_fact env' f2 in
        Correspondence { fresh = fresh_ids; premise = f1; conclusion = f2 }
  in
  let lemma : Typed.lemma = { env; loc; desc } in
  (* Lemma names must be handled in different name space *)
  let id = Ident.global name in
  env, (id, lemma)
;;

let rec type_decl base_fn env (d : Input.decl) : Env.t * Typed.decl list =
  let loc = d.loc in
  match d.data with
  | DeclLoad fn ->
      (* [load "xxx.rab"] *)
      let fn = Filename.dirname base_fn ^ "/" ^ fn in
      load_decls env fn
  | DeclExtFun (name, 0) ->
      let env', id = Env.add_global ~loc env name ExtConst in
      let typ = Env.{ argument_types = []; result_type = TValue } in
      env', [{ env; loc; desc = Function { id; typ } }]
  | DeclExtFun (name, arity) ->
      let typ = fresh_callable arity in
      let env', id = Env.add_global ~loc env name (ExtFun typ) in
      env', [{ env; loc; desc = Function { id; typ } }]
  | DeclExtEq (e1, e2) ->
      let vars = Name.Set.union (Input.vars_of_expr e1) (Input.vars_of_expr e2) in
      let fresh =
        Name.Set.elements (Name.Set.filter (fun v -> not (Env.mem env v)) vars)
      in
      let env', _fresh_ids =
        extend_with_args env fresh @@ fun _id -> Var (Env.fresh_type ())
      in
      let e1 = type_expr env' e1 in
      let e2 = type_expr env' e2 in
      unify ~loc (type_of_expr e1) (type_of_expr e2);
      ( env
      , [{ env = env'
         ; loc
         ; desc =
             (* [_fresh_ids] should be included,
                but so far this information is not required in the later stages *)
             Equation (e1, e2)
         }] )
  | DeclExtSyscall (name, args, c, attack) ->
      let typ = fresh_callable (List.length args) in
      let args, cmd =
        let argument_types = ref typ.argument_types in
        let env', args =
          extend_with_args env args @@ fun _id ->
          match !argument_types with
          | argument_type :: rest ->
              argument_types := rest;
              Var argument_type
          | [] -> assert false
        in
        let c = type_cmd env' c in
        unify ~loc:c.loc typ.result_type (infer_cmd_result_type c);
        args, c
      in
      let env', id = Env.add_global ~loc env name (ExtSyscall typ) in
      env', [{ env; loc; desc = Syscall { id; args; cmd; attack } }]
  | DeclExtAttack (name, syscall, args, c) ->
      (* [attack id on syscall (a1,..,an) { c }] *)
      let syscall, syscall_type =
        match Env.find ~loc env syscall with
        | syscall, ExtSyscall typ -> syscall, typ
        | id, desc ->
            error ~loc
            @@ InvalidVariable
                 { ident = id; def = desc; use = ExtSyscall (fresh_callable (List.length args)) }
      in
      let arity = List.length syscall_type.argument_types in
      if List.length args <> arity then
        error ~loc @@ ArityMismatch { arity; use = List.length args };
      let args, cmd =
        let argument_types = ref syscall_type.argument_types in
        let env', args =
          extend_with_args env args @@ fun _id ->
          match !argument_types with
          | argument_type :: rest ->
              argument_types := rest;
              Var argument_type
          | [] -> assert false
        in
        let c = type_cmd env' c in
        unify ~loc:c.loc syscall_type.result_type (infer_cmd_result_type c);
        args, c
      in
      let env', id = Env.add_global ~loc env name Attack in
      env', [{ env; loc; desc = Attack { id; syscall; args; cmd } }]
  | DeclType (name, tclass) ->
      let env', id = Env.add_global ~loc env name (Type tclass) in
      env', [{ env; loc; desc = Type { id; typclass = tclass } }]
  | DeclAccess (proc_ty, tys, syscalls_opt) ->
      let proc_ty = Env.find_desc ~loc env proc_ty (Type CProc) in
      let tys =
        List.map
          (fun ty ->
             match Env.find ~loc env ty with
             | id, Type (CChan | CFsys) -> id
             | _ -> misc_errorf ~loc "%s must be a channel or filesys type" ty)
          tys
      in
      (match tys with
       | [] | [ _ ] -> ()
       | _ -> error ~loc (Misc "At most 1 channel or filesys type is allowed"));
      let syscalls_opt =
        Option.map
          (fun syscalls ->
             List.map
               (fun syscall ->
                  match Env.find ~loc env syscall with
                  | id, ExtSyscall _ -> id
                  | id, desc ->
                      error ~loc
                      @@ InvalidVariable { ident = id; def = desc; use = ExtSyscall (fresh_callable 0) })
               syscalls)
          syscalls_opt
      in
      ( env
      , [{ env
        ; loc
        ; desc =
            Allow { process_typ = proc_ty; target_typs = tys; syscalls = syscalls_opt }
        }] )
  | DeclAttack (proc_tys, attacks) ->
      (* [allow attack proc_ty1 .. proc_tyn [attack1, .., attackn]] *)
      let proc_tys =
        List.map (fun ty -> Env.find_desc ~loc env ty (Type CProc)) proc_tys
      in
      let attacks =
        List.map (fun attack -> Env.find_desc ~loc env attack Attack) attacks
      in
      env, [{ env; loc; desc = AllowAttack { process_typs = proc_tys; attacks } }]
  | DeclInit (name, Fresh) ->
      (* [const fresh n] *)
      let env', id = Env.add_global ~loc env name (Const false) in
      env', [{ env; loc; desc = Init { id; desc = Fresh } }]
  | DeclInit (name, Value e) ->
      (* [const n = e] *)
      let e = type_expr env e in
      unify ~loc:e.loc TValue (type_of_expr e);
      let env', id = Env.add_global ~loc env name (Const false) in
      env', [{ env; loc; desc = Init { id; desc = Value e } }]
  | DeclInit (name, Fresh_with_param) ->
      (* [const fresh n<>] *)
      let env', id = Env.add_global ~loc env name (Const true) in
      env', [{ env; loc; desc = Init { id; desc = Fresh_with_param } }]
  | DeclInit (name, Value_with_param (e, p)) ->
      (* [const n<p> = e] *)
      let p = Ident.local p in
      let env' = Env.add env p (Var TParameter) in
      let e = type_expr env' e in
      unify ~loc:e.loc TValue (type_of_expr e);
      let env', id =
        Env.add_global ~loc env name (Const true)
        (* no info of param? *)
      in
      env', [{ env; loc; desc = Init { id; desc = Value_with_param (p, e) } }]
  | DeclChan (ChanParam { id = name; param; typ = chty }) ->
      (* [channel n : ty] *)
      (* [channel n<> : ty] *)
      let chty = Env.find_desc ~loc env chty (Type CChan) in
      let env', id = Env.add_global ~loc env name (Channel (param <> None, chty)) in
      env', [{ env; loc; desc = Channel { id; param; typ = chty } }]
  | DeclProc { id; param; args; typ; files; vars; funcs; main } ->
      let env', decl = type_process ~loc env id param args typ files vars funcs main in
      env', [decl]
  | DeclSys (procs, lemmas) ->
      (* [system proc1|..|procn requires [lemma X : ...; ..; lemma Y : ...]] *)
      let type_chan_arg ~loc env : _ -> Typed.chan_arg = function
        | Input.ChanArgPlain name ->
            (* [id] *)
            (match Env.find ~loc env name with
             | id, Channel (false, chty) -> { channel = id; parameter = None; typ = chty }
             | id, _ ->
                 misc_errorf
                   ~loc
                   "%t is not a channel without a parameter"
                   (Ident.print id))
        | ChanArgParam name ->
            (* [id<>] *)
            (match Env.find ~loc env name with
             | id, Channel (true, chty) ->
                 { channel = id; parameter = Some None; typ = chty }
             | id, _ ->
                 misc_errorf ~loc "%t is not a channel with a parameter" (Ident.print id))
        | ChanArgParamInst (name, e) ->
            (* [id<e>] *)
            let e = type_expr env e in
            (match Env.find ~loc env name with
             | id, Channel (true, chty) ->
                 { channel= id; parameter= Some (Some e); typ= chty }
             | id, _ ->
                 misc_errorf ~loc "%t is not a channel with a parameter" (Ident.print id))
      in
      let type_pproc env idopt (pproc : Input.pproc) =
        let loc = pproc.loc in
        let data : Typed.proc' =
          match pproc.data, idopt with
          | Proc (pname, chan_args), None ->
              (* [pname (chargs,..,chargs)] *)
              let pid = Env.find_desc ~loc env pname Process in
              let chan_args = List.map (type_chan_arg ~loc env) chan_args in
              { id = pid; parameter = None; args = chan_args }
          | ParamProc (pname, e, chan_args), Some _p ->
              (* [pname <e> (chargs,..,chargs)] *)
              let pid = Env.find_desc ~loc env pname Process in
              let e = type_expr env e in
              (* ??? check [p] is in [e] *)
              let chan_args = List.map (type_chan_arg ~loc env) chan_args in
              { id = pid; parameter = Some e; args = chan_args }
          | Proc _, Some p ->
              misc_errorf ~loc "Process must be parameterized with the quantification %t" (Ident.print p)
          | ParamProc _, None ->
              misc_errorf ~loc "Process cannot be parameterized"
        in
        { pproc with data }
      in
      let type_proc env : _ -> Typed.proc_group_desc = function
        | Input.UnboundedProc pproc -> Unbounded (type_pproc env None pproc)
        | BoundedProc (name, pprocs) (* [!name.(pproc1|..|pprocn)] *) ->
            let id = Ident.local name in
            let env = Env.add env id Param in
            let pprocs = List.map (type_pproc env (Some id)) pprocs in
            Bounded (id, pprocs)
      in
      let procs = List.map (type_proc env) procs in
      let _env, rev_lemmas =
        List.fold_left
          (fun (env, rev_lemmas) lemma ->
             let env, lemma = type_lemma env lemma in
             env, lemma :: rev_lemmas)
          (env, [])
          lemmas
      in
      let lemmas = List.rev rev_lemmas in
      env, [{ env; loc; desc = System (procs, lemmas) }]
  | DeclStructure(n, ftys) ->
      Env.add_fact ~loc env n (Structure ftys, Some (List.map type_of_field_type ftys));
      env, [{ env; loc; desc= Structure (n, ftys)} ]

and load_decls env fn : Env.t * Typed.decl list =
  let decls, (_used_idents, _used_strings) = Lexer.read_file Parser.file fn in
  let env, rev_decls =
    List.fold_left
      (fun (env, rev_decls) decl ->
         let env, decl = type_decl fn env decl in
         env, List.rev_append decl rev_decls)
      (env, [])
      decls
  in
  env, List.rev rev_decls
;;

let load env fn =
  let mark = Env.type_variable_mark () in
  match load_decls env fn with
  | result ->
      Env.default_types_since mark;
      result
  | exception exn ->
      Env.discard_types_since mark;
      raise exn
;;
