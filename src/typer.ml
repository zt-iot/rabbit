




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
  | InvalidSimpleType of Input.rabbit_typ
  | InvalidSecurityTypeDeclaration of Name.ident
  | InvalidTypeParam of string
  (* | InvalidEnvTyParam of Input.rabbit_typ *)

exception Error of error Location.located

exception TyperException of string 

let raise_typer_exception_with_location msg loc = 
    Location.print loc Format.std_formatter;
    Format.pp_print_newline Format.std_formatter ();
    raise (TyperException msg)


let kind_of_desc = function
  | Env.Var (Top _, _) -> "toplevel"
  | Var (Loc _, _) -> "local"
  | Var (Meta _, _) -> "meta"
  | Var (MetaNew _, _) -> "metanew"
  | Var (Param, _) -> "parameter"
  | ExtFun _ -> "external function"
  | ExtSyscall _ -> "system call"
  | Const _ -> "constant"
  | Channel _ -> "channel"
  | Attack -> "attack"

  | SimpleTypeDef _ -> "simple type definition"

  | ProcTypeDef -> "process type"
  | FilesysTypeDef -> "filesys type"
  | ChanTypeDef _ -> "channel type definition"
  | SecurityTypeDef _ -> "security type"

  | Function _ -> "function"
  | Process -> "process"

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
  | InvalidSimpleType(_) -> Format.fprintf ppf "Invalid simple type: simple types can only contain polymorphic type parameters"
  | InvalidSecurityTypeDeclaration(decl_type) -> Format.fprintf ppf "%s is not a valid security type" decl_type
  | InvalidTypeParam(ty_param) -> Format.fprintf ppf "%s is a security type and therefore cannot have type parameters" ty_param
  (* | InvalidEnvTyParam(_) -> Format.fprintf ppf "This Rabbit type cannot be conveted to a Env.ty_param" *)
;;

(** [error ~loc err] raises the given runtime error. *)
let error ~loc err = 
  Format.eprintf "TyperFail: %t: %t@." (Location.print loc) (print_error err);
  Stdlib.raise (Error (Location.locate ~loc err))

let misc_errorf ~loc fmt = Format.kasprintf (fun s -> error ~loc (Misc s)) fmt





module Env : sig
  include module type of struct
    include Env
  end

  val find : loc:Location.t -> t -> Name.ident -> Ident.t * Env.desc
  val find_desc : loc:Location.t -> t -> Name.ident -> Env.desc -> Ident.t

  (** Fails if the name is bound in the environment *)
  val add_global : loc:Location.t -> t -> Name.ident -> Env.desc -> t * Ident.t

  val add_fact : loc:Location.t -> t -> Name.ident -> named_fact_desc * int option -> unit
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

  (* check if (find ~loc env name) = desc *)
  (* if so, return corresponding Ident.t *)
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

  let add_fact ~loc env name (desc, arity) =
    match find_fact_opt env name with
    | Some (desc', arity') ->
        if desc <> desc'
        then error ~loc @@ InvalidFact { name; def = desc'; use = desc }
        else (
          match arity, arity' with
          | Some a, Some a' ->
              if a = a' then () else error ~loc @@ ArityMismatch { arity = a; use = a' }
          | None, Some _ -> update_fact env name (desc, arity)
          | Some _, None -> ()
          | None, None -> ())
    | None -> update_fact env name (desc, arity)
  ;;
end

let check_arity ~loc ~arity ~use =
  if arity <> use then error ~loc @@ ArityMismatch { arity; use }
;;
    

let rec convert_rabbit_typ_to_instantiated_ty ~loc (env : Env.t) (ty : Input.rabbit_typ) : Env.instantiated_ty =
  match ty with
  | CProc | CFsys ->
      error ~loc (Misc "process and filesys cannot be used as a instantiated type")

  | CChan input_ty_params ->
      TyChan(List.map (convert_rabbit_typ_to_instantiated_ty ~loc env) input_ty_params)

  | CSimpleOrSecurity (typ_name, input_ty_params) ->


      let convert_simple_type_params def_ty_params = 
        let expected_arity = List.length def_ty_params in 
        let actual_arity = List.length input_ty_params in 
        check_arity ~loc ~arity:expected_arity ~use:actual_arity;
        List.map (convert_rabbit_typ_to_instantiated_ty ~loc env) input_ty_params
      in

      (* lookup if typ_name is a simple type definition or security type definition *)
      let _, desc = Env.find ~loc env typ_name in 
      begin match desc with 
        | Env.SimpleTypeDef def_ty_params -> 
            (* if desc is a SimpleTypDef, check that arity is matching *)
            let converted_st_params = convert_simple_type_params def_ty_params in 
            TySimple(typ_name, converted_st_params)
        | Env.SecurityTypeDef (simpletypname, instantiated_simple_typ_params) -> 
            
            (* we need to check that there are no additional input_ty_params given, because a security type cannot have any *)
            let _ = if input_ty_params = [] then () else error ~loc (InvalidTypeParam typ_name)
            in

            TySecurity(typ_name, simpletypname, instantiated_simple_typ_params)

        | Env.ChanTypeDef (instantiated_tys) -> 
          TyChan(instantiated_tys)
          
        (* we disallow security types based on product types for now *)
        | _ -> error ~loc (Misc (Format.sprintf "Invalid declaration: %s is not a simple type definition, security type definition or channel type definition" typ_name))
      end

  | CProd (t1, t2) ->
      let param1 = convert_rabbit_typ_to_instantiated_ty ~loc env t1 in 
      let param2 = convert_rabbit_typ_to_instantiated_ty ~loc env t2 in 
      TyProduct(param1, param2)

  | CPoly _ ->
      error ~loc (Misc "A polymorphic type cannot be used as an instantiated type")


let rec convert_rabbit_typ_to_env_function_param ~loc (env : Env.t) (ty : Input.rabbit_typ) : Env.function_param =
  match ty with
  (* a channel is valid as a function parameter *)
  | CChan input_ty_params ->
      FParamChannel (List.map (convert_rabbit_typ_to_env_function_param ~loc env) input_ty_params)
  | CSimpleOrSecurity (typ_name, input_ty_params) ->
      let _, desc = Env.find ~loc env typ_name in 
      begin match desc with  
        | Env.SimpleTypeDef def_ty_params -> 

            (* let _ = print_endline (Format.sprintf "Simple type name: %s" typ_name) in 
            let _ = print_endline "with def_ty_params:" in 
            let _ = List.map (fun s -> print_string s; print_string " ; ") def_ty_params in 

            let _ = print_endline "and given input_ty_params: " in 
            let _ = List.map (fun t -> print_string (Input.show_rabbit_typ t); print_string " ; ") input_ty_params in  *)


            let expected_arity = List.length def_ty_params in 
            let actual_arity = List.length input_ty_params in 
            check_arity ~loc ~arity:expected_arity ~use:actual_arity;
            let env_ty_params = List.map (convert_rabbit_typ_to_env_function_param ~loc env) input_ty_params in 
            FParamSimple(typ_name, env_ty_params)
        | Env.SecurityTypeDef (simpletypname, instantiated_simple_typ_params) -> 
            
            (* we need to check that there are no additional input_ty_params given, because a security type cannot have any *)
            let _ = if input_ty_params = [] then () else error ~loc (InvalidTypeParam typ_name)
            in

            FParamSecurity(typ_name, simpletypname, instantiated_simple_typ_params)


        | Env.ChanTypeDef (instantiated_tys) -> 
          let env_ty_params = List.map Env.instantiated_ty_to_function_param instantiated_tys in 
          
          FParamChannel(env_ty_params)
        (* we disallow security types based on product types for now *)
        | _ -> 
          Env.print_desc desc Format.std_formatter;
          error ~loc (Misc (Format.sprintf "Invalid security type declaration: above description needs to be an Env.SimpleTypeDef or Env.SecurityTypeDef"))
      end
  | CProd (t1, t2) ->
      let param1 = convert_rabbit_typ_to_env_function_param ~loc env t1 in 
      let param2 = convert_rabbit_typ_to_env_function_param ~loc env t2 in 
      FParamProduct(param1, param2)

  | CPoly ident ->
      FParamPoly ident

  | CProc | CFsys ->
      error ~loc (Misc "process and filesys cannot be used as a function parameter")




let rec desugar_expr env (e : Input.expr) : Typed.expr =
  let loc = e.loc in
  let desc, typ_opt =
    match e.data with
    | Boolean b -> Typed.Boolean b, Some (Env.TySimple("bool", []))
    | String s -> String s, Some(Env.TySimple("string", []))
    | Integer i -> Integer i, Some(Env.TySimple("int", []))
    | Float f -> Float f, Some(Env.TySimple("float", []))
    | Var name ->
        let id, desc = Env.find ~loc env name in

        let ty_opt = begin match desc with
          | Var (_, ty_opt) -> ty_opt
          | Const (_, ty_opt) -> ty_opt
          | _ -> None
        end in

        Ident { id; desc; param = None }, ty_opt
    | Tuple es ->
        assert (List.length es > 0);

        if (List.length es < 2) then
          (raise_typer_exception_with_location "A tuple expression must have at least 2 members" e.loc);


        let typed_es = List.map (desugar_expr env) es in 

        let init_tuple_typ_opt = begin match (List.hd typed_es).typ with 
          | Some (ty1) -> begin match (List.hd (List.tl typed_es)).typ with
            | Some(ty2) -> Some (Env.TyProduct(ty1, ty2))
            | _ -> None 
            end
          | _ -> None 
        end in 

        let ty_opt = List.fold_left (fun acc_tup_typ_opt (typed_expr : Typed.expr) -> begin match acc_tup_typ_opt with 
          | Some (typrod) -> begin match typed_expr.typ with 
            | Some(ty3) -> Some (Env.TyProduct(typrod, ty3))
            | None -> None
            end
          | None -> None
          end
          ) init_tuple_typ_opt (List.tl (List.tl typed_es)) in 

        Tuple (typed_es), ty_opt
    | Apply (f, es) ->
        let es = List.map (desugar_expr env) es in
        let use = List.length es in
        (match Env.find ~loc env f with
         | id, (ExtFun (DesugaredArity arity)) -> 
             check_arity ~loc ~arity ~use;
             Apply (id, es), None
         | id, (ExtFun (DesugaredTypeSig ps)) -> 
            (* arity = number of arguments that function takes *)
            let arity = List.length ps - 1 in 
            check_arity ~loc ~arity ~use; 

            let ty_opt = failwith "TODO" in 
             Apply (id, es), ty_opt
         | id, (ExtSyscall sig_desc | Function sig_desc) ->
             let arity = begin match sig_desc with
             (* arity = number of arguments that function takes *)
             | Env.DesSMFunUntyped(ids) -> List.length ids
             | Env.DesSMFunTyped(ids, ps) -> 
                assert ((List.length ids) = (List.length ps) - 1);
                (* arity = number of arguments that function takes, which is the length of parameter list minus one *)
                List.length ps - 1
             end in 
             check_arity ~loc ~arity ~use;

             let ty_opt = failwith "TODO" in 
             Apply (id, es), ty_opt
         | id, desc ->
             error ~loc @@ NonCallableIdentifier (id, desc))
    | Param (f, e) (* [f<e>] *) ->
        (match Env.find ~loc env f with
         | id, ((Const _ | Channel _) as desc) ->
             let e = desugar_expr env e in
             Ident { id; desc; param= Some e }, None
         | id, desc -> error ~loc @@ NonParameterizableIdentifier (id, desc))
  in
  { loc; env; desc; typ = typ_opt }
;;

(* If [f] is a system call or a funciton w/ definition, an application of [f] is only
   allowed at commands [x := f (..)].
   this function is called if `at_assignment=false`
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

let desugar_expr ?(at_assignment=false) env (e : Input.expr) : Typed.expr =
  let e = desugar_expr env e in
  if not at_assignment then check_apps e;
  e

let type_fact env (fact : Input.fact) : Typed.fact =
  let loc = fact.loc in
  let desc : Typed.fact' =
    match fact.data with
    | ProcessFact _ -> assert false (* XXX ??? *)
    | Fact ("In", [ e ]) -> In (desugar_expr env e)
    | Fact ("Out", [ e ]) -> Out (desugar_expr env e)
    | Fact (name, es) ->
        (* Which fact? For strucure? *)
        let nes = List.length es in
        (match Env.find_fact_opt env name with
         | None ->
             Env.add_fact ~loc env name (Plain, Some nes);
             Typed.Plain (name, List.map (desugar_expr env) es)
         | Some (Plain, Some arity) ->
             check_arity ~loc ~arity ~use:nes;
             Plain (name, List.map (desugar_expr env) es)
         | Some (Plain, None) -> assert false
         | Some (desc, _) ->
             error ~loc @@ InvalidFact { name; def= desc; use= Plain }
        )
    | GlobalFact (name, es) ->
        let nes = List.length es in
        Env.add_fact ~loc env name (Global, Some nes);
        Global (name, List.map (desugar_expr env) es)
    | ChannelFact (e, name, es) ->
        let e = desugar_expr env e in
        let es = List.map (desugar_expr env) es in
        let nes = List.length es in
        Env.add_fact ~loc env name (Channel, Some nes);
        Channel { channel = e; name; args = es }
    | EqFact (e1, e2) ->
        let e1 = desugar_expr env e1 in
        let e2 = desugar_expr env e2 in
        Eq (e1, e2)
    | NeqFact (e1, e2) ->
        let e1 = desugar_expr env e1 in
        let e2 = desugar_expr env e2 in
        Neq (e1, e2)
    | FileFact (e1, e2) ->
        let e1 = desugar_expr env e1 in
        let e2 = desugar_expr env e2 in
        File { path = e1; contents = e2 }
  in
  { env; loc; desc; typ = None }
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

let type_facts env facts = List.map (type_fact env) facts

let type_structure_fact ~loc env name es =
  (* [str] must be a structure fact *)
  let nes = List.length es in
  Env.add_fact ~loc env name (Structure, Some nes)
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
        (* print_endline (Format.sprintf "typing `var %s = ...`" name); *)
        let e = desugar_expr ~at_assignment:true env e in

        let id = Ident.local name in
        let env' = Env.add env id (Var (Loc (snd id), e.typ)) in
        let cmd = type_cmd env' cmd in
        Let (id, e, cmd)
    | Assign (None, e) ->
        let e = desugar_expr ~at_assignment:true env e in
        Assign (None, e)
    | Assign (Some name, e) ->
        let id, vdesc = Env.find ~loc env name in
        (match vdesc with
         | Var ((Top _ | Loc _ | Meta _), _) -> ()
         | desc -> error ~loc @@ InvalidVariableAtAssign (id, desc));
        let e = desugar_expr env ~at_assignment:true e in
        Assign (Some id, e)
    | Case cases -> Case (type_cases env cases)
    | While (cases1, cases2) ->
        let cases1 = type_cases env cases1 in
        let cases2 = type_cases env cases2 in
        While (cases1, cases2)
    | Event facts ->
        let facts = type_facts env facts in
        Event facts
    | Return e -> Return (desugar_expr env e)
    | New (name, input_ty_opt, str_es_opt, cmd) ->
        let desugared_ty_opt = Option.map (convert_rabbit_typ_to_instantiated_ty ~loc env) input_ty_opt in 
        (* allocation, [new x := S(e1,..,en) in c] or [new x in c] *)
        let str_es_opt =
          Option.map
            (fun (str, es) ->
               (* [str] must be a structure fact *)
               type_structure_fact ~loc env str es;
               str, List.map (desugar_expr env) es)
            str_es_opt
        in
        let id = Ident.local name in
        let env' = Env.add env id (Var (Loc (snd id), None)) in
        let cmd = type_cmd env' cmd in
        New (id, desugared_ty_opt, str_es_opt, cmd)
    | Get (names, e, str, cmd) ->
        (* fetch, [let x1,...,xn := e.S in c] *)
        let e = desugar_expr env e in
        type_structure_fact ~loc env str names;
        let ids = List.map Ident.local names in
        let env' =
          List.fold_left (fun env' id -> Env.add env' id (Var (Loc (snd id), None))) env ids
        in
        let cmd = type_cmd env' cmd in
        Get (ids, e, str, cmd)
    | Del (e, str) ->
        (* deletion, [delete e.S] *)
        let e = desugar_expr env e in
        (match Env.find_fact_opt env str with
         | Some (Structure, _arity) -> ()
         | Some (desc, _) ->
             error ~loc @@ InvalidFact { name = str; def = desc; use = Structure }
         | None -> error ~loc @@ UnboundFact str);
        Del (e, str)
  in
  { loc; env; desc; typ = None }

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
    List.fold_left (fun env id -> Env.add env id (Var (Meta (snd id), None))) env fresh_ids
  in
  let facts = type_facts env' facts in
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
      (vars : (Name.ident * Input.rabbit_typ option * Input.expr) list)
      (funcs : (Name.ident * Input.syscall_member_fun_desc * Input.cmd) list)
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
          Env.add env id (Var (Param, None)), Some id
    in

    (* add channel paramters to local environment *)
    let env', rev_args =
      List.fold_left
        (fun (env, rev_args) (Input.ChanParam { id = chanid; param; typ = chanty }) ->
           let with_param = param <> None in
          
           let chanty = begin match Env.find ~loc env chanty with 
           | id, Env.ChanTypeDef(_) -> id
           | _ -> error ~loc @@ Misc("Use a channel type definition instead")
           end in 

           let chanid = Ident.local chanid in
           ( Env.add env chanid (Channel (with_param, chanty))
           , Typed.{ channel=chanid; param; typ= chanty } :: rev_args ))
        (env', [])
        args
    in
    let args = List.rev rev_args in

    (* check if proc_ty is a valid type *)
    let proc_ty =
      match Env.find ~loc env proc_ty with
      | proc_ty, ProcTypeDef -> proc_ty
      | id, desc ->
          error ~loc @@ InvalidVariable { ident = id; def = desc; use = ProcTypeDef }
    in

    (* check if file types exist *)
    let files =
      List.map
        (fun (path, filety, contents) ->
           let path = desugar_expr env' path in
           let filety = Env.find_desc ~loc env' filety (FilesysTypeDef) in
           let contents = desugar_expr env' contents in
           path, filety, contents)
        files
    in
    (* add contents of process memory to local  environment *)
    let env', rev_vars =
      List.fold_left
        (fun (env, rev_vars) (name, ty_opt, e) ->
            let id = Ident.local name in
            let converted_ty_opt = Option.map
              (convert_rabbit_typ_to_instantiated_ty ~loc env) ty_opt in 
            let e = desugar_expr env e in
            let env' = Env.add env id (Var (Loc (snd id), None)) in
            env', (id, converted_ty_opt, e) :: rev_vars)
        (env', [])
        vars
    in
    let vars = List.rev rev_vars in

    (* add member functions of process to local environment *)
    let env', rev_funcs =
      List.fold_left
        (fun (env', rev_funcs) (fname, input_member_fun_desc, c) ->
           let args = Input.syscall_member_fun_desc_to_ident_list input_member_fun_desc in 
           let env'', args = extend_with_args env' args @@ fun id -> Var (Loc (snd id), None) in

           let converted_fun_desc = begin match input_member_fun_desc with 
            | Input.UntypedSig(_) -> Env.DesSMFunUntyped(args)
            | Input.TypedSig(_, fun_params) -> 
              let converted_fun_params = List.map 
                (convert_rabbit_typ_to_env_function_param ~loc env) fun_params in 
                Env.DesSMFunTyped(args, converted_fun_params)
           end in 

           let c = type_cmd env'' c in
           let fid = Ident.local fname in
           let env''' = Env.add env' fid (Function converted_fun_desc) in 
           env''', (fid, converted_fun_desc, c) :: rev_funcs)
        (env', [])
        funcs
    in
    let funcs = List.rev rev_funcs in
    if (name = "client_ta") then
      print_endline "running cmd code of client_ta through typer.ml";
    let main = type_cmd env' main in
    param_opt, args, proc_ty, files, vars, funcs, main
  in
  (* add process name to environment *)
  let env', id = Env.add_global ~loc env name Process in
  let decl : Typed.decl =
    { env
    ; loc
    ; desc =
        Process { id; param = param_opt; args; typ = proc_ty; files; vars; funcs; main }
    ; typ = None
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
            (fun env id -> Env.add env id (Var (Meta (snd id), None)))
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
            (fun env id -> Env.add env id (Var (Meta (snd id), None)))
            env
            fresh_ids
        in
        let f1 = type_fact env' f1 in
        let f2 = type_fact env' f2 in
        Correspondence { fresh = fresh_ids; from = f1; to_ = f2 }
  in
  let lemma : Typed.lemma = { env; loc; desc; typ = None } in
  let env', id = Env.add_global ~loc env name Process in
  env', (id, lemma)
;;

let rec type_decl base_fn env (d : Input.decl) : Env.t * Typed.decl list =
  let loc = d.loc in
  match d.data with
  | DeclSimpleTyp t -> begin match t with 
    | Input.CSimpleOrSecurity(name, ty_params) ->
        let ty_params_str = List.map (fun ty_param -> begin match ty_param with 
          | Input.CPoly(id) -> id
          | _ -> error ~loc @@ InvalidSimpleType(t)
        end
        ) ty_params in 
        let env', _ = Env.add_global ~loc env name (Env.SimpleTypeDef (ty_params_str)) in 
        
        (* let _ = print_endline (Format.sprintf "Registerd simple type %s with type parameter list: " name) in 
        let _ = List.map print_string ty_params_str in 
        let _ = print_newline in  *)

        env', [] (* no need to produce a Typed.decl for a simple type *)
    | _ -> error ~loc @@ InvalidSimpleType(t)
    end
  | DeclLoad fn ->
      (* [load "xxx.rab"] *)
      let fn = Filename.dirname base_fn ^ "/" ^ fn in
      load env fn
  | DeclEqThyFunc(name, fun_desc) -> 
    let converted_fun_desc = begin match fun_desc with 
      | Input.Arity(n) -> Env.DesugaredArity(n)
      | Input.TypeSig(typs) -> 
          Env.DesugaredTypeSig(List.map 
            (convert_rabbit_typ_to_env_function_param ~loc env) 
            typs)
      end in
    let env', _ = Env.add_global ~loc env name (ExtFun converted_fun_desc) in
    env', []
  | DeclEqThyEquation (e1, e2) ->
      let vars = Name.Set.union (Input.vars_of_expr e1) (Input.vars_of_expr e2) in
      let fresh =
        Name.Set.elements (Name.Set.filter (fun v -> not (Env.mem env v)) vars)
      in
      let env', _fresh_ids (* XXX should be in the tree *) =
        extend_with_args env fresh @@ fun id -> Var (Meta (snd id), None)
      in
      let e1 = desugar_expr env' e1 in
      let e2 = desugar_expr env' e2 in
      ( env
      , [{ env = env'; loc; desc = Equation (e1, e2) (* XXX fresh should be included *); typ = None }] )
  | DeclExtSyscall (name, syscall_desc_input, c) ->

      
      let args = Input.syscall_member_fun_desc_to_ident_list syscall_desc_input in 
      let args, cmd =
        let env', args = extend_with_args env args @@ fun id -> Var (Loc (snd id), None) in
        let c = type_cmd env' c in
        args, c
      in
      let converted_syscall_sig = begin match syscall_desc_input with 
        | Input.UntypedSig(_) -> Env.DesSMFunUntyped(args)
        | Input.TypedSig(_, fun_params_types) -> 
            let converted_fun_params_types = List.map 
              (convert_rabbit_typ_to_env_function_param ~loc env) fun_params_types in 
            Env.DesSMFunTyped(args, converted_fun_params_types)
      end in 
      let env', id = Env.add_global ~loc env name (ExtSyscall converted_syscall_sig) in
      env', [{ env; loc; desc = Typed.Syscall { id; fun_sig = converted_syscall_sig; cmd }; typ = None }]
  | DeclExtAttack (name, syscall, args, c) ->
      (* [attack id on syscall (a1,..,an) { c }] *)
      let syscall =
        match Env.find ~loc env syscall with
        | syscall, ExtSyscall _ -> syscall
        | _, _ ->
            error ~loc
            @@ Misc "Incorrect usage of `on`: use an existing syscall with the correct arity"
      in
      let args, cmd =
        let env', args = extend_with_args env args @@ fun id -> Var (Loc (snd id), None) in
        let c = type_cmd env' c in
        args, c
      in
      let env', id = Env.add_global ~loc env name Attack in
      env', [{ env; loc; desc = Attack { id; syscall; args; cmd }; typ = None }]
  | DeclType (name, typ) ->
      let converted_to_env_desc = begin match typ with 
        | Input.CProc -> Env.ProcTypeDef 
        | Input.CFsys -> Env.FilesysTypeDef
        | Input.CChan(input_ty_params) -> 
          (* every ty_param \in input_ty_param must be *)
          (* - Simple *)
          (* - Security, or *)
          (* - Product*)
          let ty_params = List.map (convert_rabbit_typ_to_instantiated_ty ~loc env) input_ty_params in
          ChanTypeDef(ty_params)
        | Input.CSimpleOrSecurity(typ_name, input_ty_params) -> 
            (* this AST node is always a security type: therefore, typ_name must be a known simple type *)
            begin match Env.find ~loc env typ_name with 
              | _, SimpleTypeDef def_ty_params -> 
                  let expected_arity = List.length def_ty_params in 
                  let actual_arity = List.length input_ty_params in 
                  check_arity ~loc ~arity:expected_arity ~use:actual_arity;
                  let env_ty_params = List.map (convert_rabbit_typ_to_instantiated_ty ~loc env) input_ty_params in 
                  SecurityTypeDef(typ_name, env_ty_params)
              | _, _ -> 
                  let error_msg = Printf.sprintf " %s is not a declared simple type" typ_name in 
                  error ~loc (Misc (error_msg))
              end
        (* disallow security types declared on products for now *)
        | _ -> error ~loc (InvalidSecurityTypeDeclaration name)

      end in
      let env', id' = Env.add_global ~loc env name converted_to_env_desc in

      (* TODO maybe get rid of this boilerplate code once it is clear 
        whether it is actually required for TAMARIN *)
      let typclass_opt = match converted_to_env_desc with
        | Env.ProcTypeDef -> Some (Input.CProc)
        | Env.FilesysTypeDef -> Some (Input.CFsys)
        | Env.ChanTypeDef _ -> Some (Input.CChan [])
        | _ -> None
      in
      let res = match typclass_opt with 
        | Some ty_class -> 
          let typed_decl_desc = Typed.Type {id = id' ; typclass = ty_class } in 
          (env', [{ Typed.desc = typed_decl_desc ; Typed.loc = loc; Typed.env = env; Typed.typ = None} ])
        | None ->
          (env', []) in 
      res
  | DeclAccess (proc_ty, tys, syscalls_opt) ->
      let proc_ty = Env.find_desc ~loc env proc_ty (ProcTypeDef) in
      let tys =
        List.map
          (fun ty ->
             match Env.find ~loc env ty with
             | id, (SecurityTypeDef _ | ChanTypeDef _ | FilesysTypeDef) -> id
             | _ -> misc_errorf ~loc "%s must be a security, channel or filesys type" ty)
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
                  | _, _ ->
                      error ~loc @@ Misc "Unknown syscall used in allow rule: use a syscall which exists"
                      )
               syscalls)
          syscalls_opt
      in
      ( env
      , [{ env
        ; loc
        ; desc =
            Allow { process_typ = proc_ty; target_typs = tys; syscalls = syscalls_opt }
        ; typ = None
        }] )
  | DeclAttack (proc_tys, attacks) ->
      (* [allow attack proc_ty1 .. proc_tyn [attack1, .., attackn]] *)
      let proc_tys =
        List.map (fun ty -> Env.find_desc ~loc env ty (ProcTypeDef)) proc_tys
      in
      let attacks =
        List.map (fun attack -> Env.find_desc ~loc env attack Attack) attacks
      in
      env, [{ env; loc; desc = AllowAttack { process_typs = proc_tys; attacks }; typ = None }]
  | DeclInit (name, rabbit_typ_opt, Fresh) ->
      let converted_ty_opt = Option.map (fun rtyp -> convert_rabbit_typ_to_instantiated_ty ~loc env rtyp) rabbit_typ_opt in 
      (* [const fresh n] *)
      let env', id = Env.add_global ~loc env name (Const (false, converted_ty_opt)) in

      (* We only return a declaration for compatibility with sem.ml *)
      env', [{ env; loc; desc = Init { id; desc = Fresh }; typ = None }]
  | DeclInit (name, _, Value e) ->
      (* [const n = e] *)
      let e = desugar_expr env e in
      let env', id = Env.add_global ~loc env name (Const (false, None)) in

      (* We only return a declaration for compatibility with sem.ml *)
      env', [{ env; loc; desc = Init { id; desc = Value e }; typ = None }]
  | DeclInit (name, rabbit_typ_opt, Fresh_with_param) ->
      (* [const fresh n<>] *)
      let converted_ty_opt = Option.map (fun rtyp -> convert_rabbit_typ_to_instantiated_ty ~loc env rtyp) rabbit_typ_opt in 
      let env', id = Env.add_global ~loc env name (Const (true, converted_ty_opt)) in
      
      (* We only return a declaration for compatibility with sem.ml *)
      env', [{ env; loc; desc = Init { id; desc = Fresh_with_param }; typ = None }]
  | DeclInit (name, _, Value_with_param (e, p)) ->
      (* [const n<p> = e] *)
      let p = Ident.local p in
      let env' = Env.add env p (Var (Param, None)) in
      let e = desugar_expr env' e in
      let env', id =
        Env.add_global ~loc env name (Const (true, None))
        (* no info of param? *)
      in

      (* We only return a declaration for compatibility with sem.ml *)
      env', [{ env; loc; desc = Init { id; desc = Value_with_param (p, e) }; typ = None }]
  | DeclChan (ChanParam { id = name; param; typ = chty }) ->
      (* [channel n : ty] *)
      (* [channel n<> : ty] *)

      
      let chty = begin match Env.find ~loc env chty with 
        | id, Env.ChanTypeDef(_) -> id
        | _ -> error ~loc @@ Misc("Use a channel type definition instead")
        end in 
      let env', id = Env.add_global ~loc env name (Channel (param <> None, chty)) in
      env', [{ env; loc; desc = Channel { id; param; typ = chty }; typ = None }]
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
            let e = desugar_expr env e in
            (match Env.find ~loc env name with
             | id, Channel (true, chty) ->
                 { channel= id; parameter= Some (Some e); typ= chty }
             | id, _ ->
                 misc_errorf ~loc "%t is not a channel with a parameter" (Ident.print id))
      in
      let type_pproc env idopt (pproc : Input.pproc) =
        let loc = pproc.loc in
        let data : Typed.pproc' =
          match pproc.data, idopt with
          | Proc (pname, chan_args), None ->
              (* [pname (chargs,..,chargs)] *)
              let pid = Env.find_desc ~loc env pname Process in
              let chan_args = List.map (type_chan_arg ~loc env) chan_args in
              { id = pid; parameter = None; args = chan_args }
          | ParamProc (pname, e, chan_args), Some _p ->
              (* [pname <e> (chargs,..,chargs)] *)
              let pid = Env.find_desc ~loc env pname Process in
              let e = desugar_expr env e in
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
      let type_proc env : _ -> Typed.proc = function
        | Input.UnboundedProc pproc -> Unbounded (type_pproc env None pproc)
        | BoundedProc (name, pprocs) (* [!name.(pproc1|..|pprocn)] *) ->
            let id = Ident.local name in
            let env = Env.add env id (Var (Param, None)) in
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
      env, [{ env; loc; desc = System (procs, lemmas); typ = None }]

and load env fn : Env.t * Typed.decl list =
  let decls, (_used_idents, _used_strings) = Lexer.read_file Parser.file fn in
  let env, rev_decls =
    List.fold_left
      (fun (acc_env, acc_decls) decl ->
         let env', new_decls = type_decl fn acc_env decl in
         
         (* first reverses new_decls, then prepends it to acc_decls *)
         env', List.rev_append new_decls acc_decls)
      (env, [])
      decls
  in
  
  let (env, decls) = env, List.rev rev_decls in 

  (* let _ = List.map (fun decl -> match decl.Typed.desc with 
    | _ ->  print_endline (Typed.show_decl decl)
  ) decls in  *)

  (env, decls)
;;
