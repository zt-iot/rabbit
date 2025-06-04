type var_desc =
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
  | ExtConst (** external function with arity = 0, ex.  function true 0 *)
  | ExtSyscall of int (** external system call with arity *)
  | Const of bool (* with param or not *)
  | Channel of bool (* with param or not *) * Name.ident (* channel type *)
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
  | Channel (b, ty) -> f ppf "Channel (param=%b) : %s" b ty
  | Attack -> f ppf "Attack"
  | Type CProc -> f ppf "ty process"
  | Type CFsys -> f ppf "ty filesys"
  | Type CChan -> f ppf "ty channel"
  | Function i -> f ppf "Function (arity=%d)" i
  | Process -> f ppf "Process"

let kind_of_desc = function
  | Var (Top _) -> "toplevel"
  | Var (Loc _) -> "local"
  | Var (Meta _) -> "meta"
  | Var (MetaNew _) -> "metanew"
  | Var Param -> "parameter"
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

(** Conversion errors *)
type error =
  | Misc of string
  | IdentifierAlreadyBound of Name.ident
  | UnknownIdentifier of Name.ident
  | ArityMismatch of { arity : int; use : int }
  | InvalidIdentifier of Name.ident * desc
  | NonCallableIdentifier of Name.ident * desc
  | NonParameterizableIdentifier of Name.ident * desc
  | InvalidFact of { ident : Name.ident; def: named_fact_desc; use: named_fact_desc }
  | InvalidVariable of { ident : Name.ident; def: desc; use: desc }
  | InvalidNullAssign
  | InvalidVariableAtAssign of Name.ident * desc
  | UnboundFact of Name.ident

exception Error of error Location.located

(** [error ~loc err] raises the given runtime error. *)
let error ~loc err = Stdlib.raise (Error (Location.locate ~loc err))

let misc_errorf ~loc fmt = Format.kasprintf (fun s -> error ~loc (Misc s)) fmt

(** Print error description. *)
let print_error err ppf =
  match err with
  | Misc s -> Format.fprintf ppf "%s" s
  | IdentifierAlreadyBound id -> Format.fprintf ppf "Identifier %s is already bound" id
  | UnknownIdentifier id -> Format.fprintf ppf "Unknown identifier %s" id
  | ArityMismatch { arity; use } -> Format.fprintf ppf "Function of arity %d takes %d arguments" arity use
  | InvalidIdentifier (id, desc) ->
      Format.fprintf ppf "%s variable %s cannot be used in an expression"
        (String.capitalize_ascii (kind_of_desc desc)) id
  | NonCallableIdentifier (id, desc) ->
      Format.fprintf ppf "%s variable %s cannot be called"
        (String.capitalize_ascii (kind_of_desc desc)) id
  | NonParameterizableIdentifier (id, desc) ->
      Format.fprintf ppf "%s variable %s cannot be parameterized"
        (String.capitalize_ascii (kind_of_desc desc)) id
  | InvalidFact { ident; def; use } ->
      Format.fprintf ppf "%s is %s fact but used as %s"
        ident
        (string_of_named_fact_desc def)
        (string_of_named_fact_desc use)
  | InvalidVariable { ident; def; use } ->
      Format.fprintf ppf "%s is %s but used as %s"
        ident
        (kind_of_desc def)
        (kind_of_desc use)
  | InvalidNullAssign ->
      Format.fprintf ppf "Right hand side of ignore assignment must be an application"
  | InvalidVariableAtAssign (id, desc) ->
      Format.fprintf ppf "%s variable %s cannot be assigned"
        (String.capitalize_ascii (kind_of_desc desc)) id
  | UnboundFact id -> Format.fprintf ppf "Unbound fact %s" id

module Env : sig
  type t

  val empty : t

  val mem : t -> Name.ident -> bool

  val must_be_fresh : loc:Location.t -> t -> Name.ident -> unit

  val find : loc:Location.t -> t -> Name.ident -> desc

  val find_desc : loc:Location.t -> t -> Name.ident -> desc -> unit

  val find_opt : t -> Name.ident -> desc option

  val add : t -> Name.ident -> desc -> t

  val in_local : t -> (t -> t * 'a) -> t * 'a

  val add_global : loc:Location.t -> t -> Name.ident -> desc -> t
  (** Fails if the name is bound in the environment *)

  val add_fact : t -> Name.ident -> named_fact_desc * int -> t

  val find_fact_opt : t -> Name.ident -> (named_fact_desc * int) option
end = struct
  type t = {
    vars : (Name.ident * desc) list;
    facts : (Name.ident * (named_fact_desc * int)) list
  }

  let empty = { vars= []; facts= [] }

  let mem env id = List.mem_assoc id env.vars

  let must_be_fresh ~loc env id =
    if mem env id then error ~loc (IdentifierAlreadyBound id)

  let find ~loc env id =
    match List.assoc_opt id env.vars with
    | None -> error ~loc (UnknownIdentifier id)
    | Some desc -> desc

  let find_desc ~loc env id desc =
    let desc' = find ~loc env id in
    if desc <> desc' then
      error ~loc @@ InvalidVariable { ident= id; def= desc'; use= desc }

  let find_opt env id = List.assoc_opt id env.vars

  let add env x desc = { env with vars = (x, desc) :: env.vars }

  let add_fact env id fact_desc =
    if List.mem_assoc id env.facts then assert false;
    { env with facts = (id, fact_desc) :: env.facts }

  let find_fact_opt env id = List.assoc_opt id env.facts

  let in_local env f =
    let env', res = f env in
    (* Extend [facts] of [env'] back to [env] *)
    { env with facts = env'.facts }, res

  let add_global ~loc env id desc =
    must_be_fresh ~loc env id;
    add env id desc
end

let check_arity ~loc ~arity ~use =
  if arity <> use then error ~loc @@ ArityMismatch { arity; use }

let rec type_expr env (e : Input.expr) =
  let loc = e.loc in
  let data =
    match e.data with
    | Var id ->
        (match Env.find ~loc env id with
         | Var (Top i) -> Syntax.Variable (id, (Top, i))
         | Var (Loc i) -> Variable (id, (Loc, i))
         | Var (Meta i) -> Variable (id, (Meta, i))
         | Var (MetaNew i) -> Variable (id, (MetaNew, i))
         | ExtConst -> ExtConst id
         | Channel (_with_param, _chty) -> Channel (id, None)
         | Const _param -> Const (id, None)
         | Var Param -> Param id
         | desc -> error ~loc @@ InvalidIdentifier (id, desc))
    | Boolean b -> Boolean b
    | String s -> String s
    | Integer i -> Integer i
    | Float f -> Float f
    | Apply (f, es) ->
        let es = List.map (type_expr env) es in
        let use = List.length es in
        (match Env.find ~loc env f with
         | ExtFun arity ->
             check_arity ~loc ~arity ~use;
             Apply (f, es)
         | ExtSyscall arity ->
             check_arity ~loc ~arity ~use;
             Apply (f, es)
         | Function arity ->
             check_arity ~loc ~arity ~use;
             Apply (f, es)
         | desc -> error ~loc @@ NonCallableIdentifier (f, desc))
    | Tuple es ->
        assert (List.length es > 0);
        Tuple (List.map (type_expr env) es)
    | Param (f, e) (* [f<e>] *) ->
        (match Env.find ~loc env f with
         | Const true -> Const (f, Some (type_expr env e))
         | Channel (true, _cty) -> Channel (f, Some (type_expr env e))
         | desc -> error ~loc @@ NonParameterizableIdentifier (f, desc))
  in
  { e with data }

let type_fact env (fact : Input.fact) =
  let loc = fact.loc in
  let env, data =
    match fact.data with
    | Fact (id, es) ->
        (* Which fact? For strucure? *)
        let nes = List.length es in
        (match Env.find_fact_opt env id with
         | None ->
             Env.add_fact env id (NoName, nes),
             Syntax.Fact (id, List.map (type_expr env) es)
         | Some (NoName, arity) ->
             check_arity ~loc ~arity ~use:nes;
             env,
             Syntax.Fact (id, List.map (type_expr env) es)
         | Some (desc, _) ->
             error ~loc @@ InvalidFact { ident=id; def= desc; use= NoName }
        )
    | GlobalFact (id, es) ->
        let nes = List.length es in
        (match Env.find_fact_opt env id with
        | None ->
            Env.add_fact env id (Global, nes),
            Syntax.GlobalFact (id, List.map (type_expr env) es)
        | Some (Global, arity) ->
            check_arity ~loc ~arity ~use:nes;
            env,
            Syntax.Fact (id, List.map (type_expr env) es)
        | Some (desc, _) ->
            error ~loc @@ InvalidFact { ident=id; def= desc; use= Global })
    | ChannelFact (e, id, es) ->
        let e = type_expr env e in
        let es = List.map (type_expr env) es in
        let nes = List.length es in
        (match Env.find_fact_opt env id with
        | None ->
            Env.add_fact env id (Channel, nes),
            Syntax.ChannelFact (e, id, es)
        | Some (Channel, arity) ->
            check_arity ~loc ~arity ~use:nes;
            env,
            Syntax.ChannelFact (e, id, es)
        | Some (desc, _) ->
            error ~loc @@ InvalidFact { ident=id; def= desc; use= Channel })
    | ProcessFact _ -> assert false (* XXX ??? *)
    | EqFact (e1, e2) ->
        let e1 = type_expr env e1 in
        let e2 = type_expr env e2 in
        env, Syntax.EqFact (e1, e2)
    | NeqFact (e1, e2) ->
        let e1 = type_expr env e1 in
        let e2 = type_expr env e2 in
        env, Syntax.NeqFact (e1, e2)
    | FileFact (e1, e2) ->
        let e1 = type_expr env e1 in
        let e2 = type_expr env e2 in
        env, Syntax.FileFact (e1, e2)
  in
  env, { fact with data }

let type_facts env facts =
  let env, rev_facts = List.fold_left (fun (env, rev_fact) fact ->
      let env, fact = type_fact env fact in
      env, fact :: rev_fact) (env, []) facts
  in
  env, List.rev rev_facts

let rec type_cmd env (cmd : Input.cmd) =
  let loc = cmd.loc in
  let env, data =
    match cmd.data with
    | Input.Skip -> env, Syntax.Skip
    | Sequence (c1, c2) ->
        let env, c1 = type_cmd env c1 in
        let env, c2 = type_cmd env c2 in
        env, Sequence (c1, c2)
    | Put facts ->
        let env, facts = type_facts env facts in
        env, Put facts
    | Let (id, e, cmd) ->
        let e = type_expr env e in
        let env, cmd =
          Env.in_local env @@ fun env ->
            let env' =
              let id' = Ident.local id in
              Env.add env id (Var (Loc (snd id')))
            in
            type_cmd env' cmd
        in
        env, Let (id, e, cmd)
    | Assign (None, e) ->
        let e = type_expr env e in
        let c =
          match e.data with
          | Apply (f, args) ->
              (match Env.find ~loc env f with
               | Function _ -> Syntax.FCall (None, f, args)
               | ExtSyscall _ -> SCall (None, f, args)
               | desc -> error ~loc @@ NonCallableIdentifier (f, desc))
          | _ -> error ~loc InvalidNullAssign
        in
        env, c
    | Assign (Some id, e) ->
        let e = type_expr env e in
        let i, top =
          match Env.find ~loc env id with
          | Var (Top i) -> (i, true)
          | Var (Loc i) -> (i, false)
          | desc -> error ~loc @@ InvalidVariableAtAssign (id, desc)
        in
        let c =
          match e.data with
          | Apply (f, args) ->
              (match Env.find ~loc env f with
               | Function _ -> Syntax.FCall (Some (id, (i, top)), f, args)
               | ExtSyscall _ -> SCall (Some (id, (i, top)), f, args)
               | _ -> Assign ((id, (i, top)), e))
          | _ -> Assign ((id, (i, top)), e)
        in
        env, c
    | Case cases ->
        let env, cases = type_cases env cases in
        env, Case cases
    | While (cases1, cases2) ->
        let env, cases1 = type_cases env cases1 in
        let env, cases2 = type_cases env cases2 in
        env, While (cases1, cases2)
    | Event facts ->
        let env, facts = type_facts env facts in
        env, Event facts
    | Return e ->
        let e = type_expr env e in
        env, Return e
    | New (id, str_es_opt, cmd) ->
        (* allocation, [new x := S(e1,..,en) in c] or [new x in c] *)
        let env, str_es_opt =
          match str_es_opt with
          | None -> env, None
          | Some (str, es) ->
              (* Treat S(e1,..,en) as a fact *)
              let env, fact = type_fact env {cmd with data= Input.Fact (str, es)} in
              let str, es =
                match fact.data with
                | Fact (str, es) -> str, es
                | _ -> assert false
              in
              env, Some (str, es)
        in
        let env, cmd =
          Env.in_local env @@ fun env ->
          let env' =
            let idx = Ident.local id in
            Env.add env id (Var (Loc (snd idx)))
          in
          type_cmd env' cmd
        in
        env, New (id, str_es_opt, cmd)
    | Get (ids, e, str, cmd) ->
        (* fetch, [let x1,...,xn := e.S in c] *)
        let e = type_expr env e in
        (match Env.find_fact_opt env str with
         | Some (NoName, arity) ->
             check_arity ~loc ~arity ~use:(List.length ids)
         | Some (desc, _) ->
             error ~loc @@ InvalidFact { ident= str; def= desc; use= NoName }
         | None -> error ~loc @@ UnboundFact str
        );
        let env, cmd =
          Env.in_local env @@ fun env ->
          let env' =
            List.fold_left (fun env' id ->
                let idx = Ident.local id in
                Env.add env' id (Var (Loc (snd idx)))) env ids
          in
          type_cmd env' cmd
        in
        env, Get (ids, e, str, cmd)
    | Del (e, str) ->
        (* deletion, [delete e.S] *)
        let e = type_expr env e in
        (match Env.find_fact_opt env str with
         | Some (NoName, _arity) -> ()
         | Some (desc, _) ->
             error ~loc @@ InvalidFact { ident= str; def= desc; use= NoName }
         | None -> error ~loc @@ UnboundFact str
        );
        env, Del (e, str)
  in
  env, { cmd with data }

and type_cases env cases =
  let env, rev_cases = List.fold_left (fun (env, rev_cases) case ->
      let env, case = type_case env case in
      env, case :: rev_cases) (env, []) cases
  in
  env, List.rev rev_cases

and type_case env (facts, cmd) =
  (* facts -> cmd *)
  let env, (fresh, facts, cmd) = Env.in_local env @@ fun env ->
    let vs = List.fold_left (fun vs fact ->
        Name.Set.union vs (Input.vars_of_fact fact)) Name.Set.empty facts
    in
    let fresh = Name.Set.filter (fun v -> not (Env.mem env v)) vs in
    let env' = Name.Set.fold (fun v env ->
        let idx = Ident.local v in
        Env.add env v (Var (Meta (snd idx)))) fresh env
    in
    let env', facts = type_facts env' facts in
    let env', cmd = type_cmd env' cmd in
    env', (fresh, facts, cmd)
  in
  env, (Name.Set.elements fresh, facts, cmd)

let extend_with_args env (args : Name.ident list) =
  (* XXX channels are not declared like [channel ch] but simply as [ch] *)
  List.fold_left (fun env id ->
      let idx = Ident.local id in
      Env.add env id (Var (Loc (snd idx)))) env args

let extend_with_args2 env (args : Name.ident list) =
  List.fold_left (fun env id ->
      let idx = Ident.local id in
      Env.add env id (Var (Loc (snd idx)))) env args

let type_process ~loc env id param_opt args typ files vars funcs main =
  (* [ process id<param>(ch1 : chty1, .., chn : chtyn) : proc_ty {
          file path : filety = contents ...
          var id = e ...
          function fid(args) { c }
          main ...
        }
     ] *)
  let env, (files, vars, funcs, main) = Env.in_local env @@ fun env ->
    let env' =
      match param_opt with
      | None -> env
      | Some param -> Env.add env param (Var Param)
    in
    let env' = List.fold_left (fun env (with_param, chanid, chanty) ->
        Env.find_desc ~loc env chanty (Type CChan);
        Env.add env chanid (Channel (with_param, chanty)))
        env' args
    in
    (match Env.find ~loc env typ with
     | Type CProc -> ()
     | desc -> error ~loc @@ InvalidVariable { ident= typ; def= desc; use= Type CProc });
    let files = List.map (fun (path, filety, contents) ->
        let path = type_expr env' path in
        Env.find_desc ~loc env' filety (Type CFsys);
        let contents = type_expr env' contents in
        path, filety, contents) files
    in
    let env', rev_vars = List.fold_left (fun (env, rev_vars) (id, e) ->
        let e = type_expr env e in
        let env' =
          let idx = Ident.local id in
          Env.add env id (Var (Loc (snd idx)))
        in
        env', (id, e) :: rev_vars) (env', []) vars
    in
    let vars = List.rev rev_vars in
    let env', rev_funcs =
      List.fold_left (fun (env', rev_funcs) (fid, args, c) ->
          let env', c =
            Env.in_local env' @@ fun env' ->
            let env'' = extend_with_args2 env' args in
            let env'' =
              let idx = Ident.local fid in
              Env.add env'' id (Var (Loc (snd idx)))
            in
            type_cmd env'' c
          in
          Env.add env' fid (Function (List.length args)),
          (id, args, c) :: rev_funcs) (env', []) funcs
    in
    let funcs = List.rev rev_funcs in
    let env', main = type_cmd env' main in
    env', (files, vars, funcs, main)
  in
  Env.add_global ~loc env id Process,
  Syntax.DeclProc { id; param= param_opt; args; typ; files; vars; funcs; main }

let type_lemma env (lemma : Input.lemma) =
  match lemma.data with
  | Lemma (id, prop) ->
      let env, data =
        match prop.data with
        | PlainString s -> env, Syntax.PlainLemma (id, s)
        | Reachability facts ->
            let vs = Input.vars_of_facts facts in
            let fresh = Name.Set.filter (fun v -> not (Env.mem env v)) vs in
            let env' = Name.Set.fold (fun v env ->
                let idx = Ident.local v in
                Env.add env v (Var (Meta (snd idx)))) fresh env
            in
            let _env', facts = type_facts env' facts in
            env, ReachabilityLemma (id, Name.Set.elements fresh, facts)
        | Correspondence (f1, f2) ->
            let vs = Name.Set.union (Input.vars_of_fact f1) (Input.vars_of_fact f2) in
            let fresh = Name.Set.filter (fun v -> not (Env.mem env v)) vs in
            let env' = Name.Set.fold (fun v env ->
                let idx = Ident.local v in
                Env.add env v (Var (Meta (snd idx)))) fresh env
            in
            let env', f1 = type_fact env' f1 in
            let _env', f2 = type_fact env' f2 in
            env, CorrespondenceLemma (id, Name.Set.elements fresh, f1, f2)
      in
      env, { prop with data }

let rec type_decl base_fn env (d : Input.decl) =
  let loc = d.loc in
  let env, data =
    match d.data with
    | DeclExtFun (id, 0) ->
        Env.add_global ~loc env id ExtConst,
        Syntax.DeclExtFun (id, 0)
    | DeclExtFun (id, arity) ->
        Env.add_global ~loc env id (ExtFun arity),
        Syntax.DeclExtFun (id, arity)
    | DeclExtEq (e1, e2) ->
        let vars = Name.Set.union (Input.vars_of_expr e1) (Input.vars_of_expr e2) in
        let fresh = Name.Set.filter (fun v -> not (Env.mem env v)) vars in
        let env' =  Name.Set.fold (fun v env ->
            let idx = Ident.local v in
            Env.add env v (Var (Loc (snd idx))))  fresh env
        in
        let e1 = type_expr env' e1 in
        let e2 = type_expr env' e2 in
        env, DeclExtEq (e1, e2) (* XXX fresh should be included *)
    | DeclExtSyscall (id, args, c) ->
        let env, c =
          Env.in_local env @@ fun env ->
          let env' = extend_with_args env args in
          type_cmd env' c
        in
        Env.add_global ~loc env id (ExtSyscall (List.length args)), DeclExtSyscall (id, args, c)
    | DeclExtAttack (id, syscall, args, c) ->
        (* [attack id on syscall (a1,..,an) { c }] *)
        (match Env.find ~loc env syscall with
         | ExtSyscall _ -> ()
         | desc -> error ~loc @@ InvalidVariable { ident=syscall; def= desc; use= ExtSyscall (-1) });
        let env, c =
          Env.in_local env @@ fun env ->
          let env' = extend_with_args env args in
          type_cmd env' c
        in
        Env.add_global ~loc env id Attack, DeclExtAttack(id, syscall, args, c)
    | DeclType (id, tclass) ->
        Env.must_be_fresh ~loc env id;
        Env.add env id (Type tclass), DeclType (id, tclass)
    | DeclAccess (proc_ty, tys, syscalls_opt) ->
        Env.find_desc ~loc env proc_ty (Type CProc);
        (List.iter (fun ty ->
             match Env.find ~loc env ty with
             | Type (CChan | CFsys) -> ()
             | _ -> misc_errorf ~loc "%s must be a channel or filesys type" ty) tys);
        (match tys with
         | [] | [_] -> ()
         | _ -> error ~loc (Misc "At most 1 channel or filesys type is allowed"));
        Option.iter (fun syscalls ->
            List.iter (fun syscall ->
                match Env.find ~loc env syscall with
                | ExtSyscall _ -> ()
                | desc -> error ~loc @@ InvalidVariable { ident= syscall; def= desc; use= ExtSyscall (-1) }) syscalls)  syscalls_opt;
        env,
        DeclAccess (proc_ty, tys, syscalls_opt)
    | DeclAttack (proc_tys, attacks) ->
        (* [allow attack proc_ty1 .. proc_tyn [attack1, .., attackn]] *)
        List.iter (fun ty -> Env.find_desc ~loc env ty (Type CProc)) proc_tys;
        List.iter (fun attack -> Env.find_desc ~loc env attack Attack) attacks;
        env,
        DeclAttack (proc_tys, attacks)
    | DeclInit (id, eopt) ->
        (* [const n = e] or [const fresh n] *)
        let eopt = Option.map (type_expr env) eopt in
        Env.add_global ~loc env id (Const false),
        DeclInit (id, eopt)
    | DeclParamInit (id, None) ->
        (* [const fresh n<>] *)
        Env.add_global ~loc env id (Const true),
        DeclParamInit (id, None)
    | DeclParamInit (id, Some (p, e)) ->
        (* [const n<p> = e] *)
        let e = type_expr (Env.add env p (Var Param)) e in
        Env.add_global ~loc env id (Const true), (* no info of param? *)
        DeclParamInit (id, Some (p, e))
    | DeclChan (id, chty) ->
        (* [channel n : ty] *)
        Env.must_be_fresh ~loc env id;
        Env.find_desc ~loc env chty (Type CChan);
        Env.add env id (Channel (false, chty)), DeclChan (id, None, chty)
    | DeclParamChan (id, chty) ->
        (* [channel n<> : ty] *)
        Env.must_be_fresh ~loc env id;
        Env.find_desc ~loc env chty (Type CChan);
        Env.add env id (Channel (true, chty)), DeclChan (id, Some (), chty)
    | DeclProc { id; args; typ; files; vars; funcs; main } ->
        type_process ~loc env id None args typ files vars funcs main
    | DeclParamProc { id; param; args; typ; files; vars; funcs; main } ->
        type_process ~loc env id (Some param) args typ files vars funcs main
    | DeclSys (procs, lemmas) ->
        (* [system proc1|..|procn requires [lemma X : ...; ..; lemma Y : ...]] *)
        let type_chan_arg ~loc env = function
          | Input.ChanArgPlain id ->
              (* [id] *)
              (match Env.find ~loc env id with
               | Channel (false, chty) -> Syntax.ChanArg { id; typ= chty; param= None }
               | _ -> misc_errorf ~loc "%s is not a channel without a parameter" id)
          | ChanArgParam id ->
              (* [id<>] *)
              (match Env.find ~loc env id with
               | Channel (true, chty) -> ChanArg { id; typ= chty; param= None }
               | _ -> misc_errorf ~loc "%s is not a channel with a parameter" id)
          | ChanArgParamInst (id, e) ->
              (* [id<e>] *)
              let e = type_expr env e in
              (match Env.find ~loc env id with
               | Channel (true, chty) -> ChanArg { id; typ= chty; param= Some (Some e) }
               | _ -> misc_errorf ~loc "%s is not a channel with a parameter" id)
        in
        let type_pproc env (pproc : Input.pproc) =
          let loc = pproc.loc in
          let data =
            match pproc.data with
              | Proc (pid, chan_args) ->
                  (* [pid (chargs,..,chargs)] *)
                  Env.find_desc ~loc env pid Process;
                  let chan_args = List.map (type_chan_arg ~loc env) chan_args in
                  Syntax.Proc (pid, None, chan_args)
              | ParamProc (pid, e, chan_args) ->
                  (* [pid <e> (chargs,..,chargs)] *)
                  let e = type_expr env e in
                  let chan_args = List.map (type_chan_arg ~loc env) chan_args in
                  Proc (pid, Some e, chan_args)
          in
          { pproc with data }
        in
        let type_proc env = function
          | Input.UnboundedProc pproc ->
              Syntax.UnboundedProc (type_pproc env pproc)
          | BoundedProc (id, pprocs) (* [!name.(pproc1|..|pprocn)] *) ->
              let env = Env.add env id (Var Param) in
              let pprocs = List.map (type_pproc env) pprocs in
              BoundedProc (id, pprocs)
        in
        let procs = List.map (type_proc env) procs in
        let env, rev_lemmas = List.fold_left (fun (env, rev_lemmas) lemma ->
            let env, lemma = type_lemma env lemma in
            env, lemma :: rev_lemmas) (env, []) lemmas
        in
        let lemmas = List.rev rev_lemmas in
        env, DeclSys (procs, lemmas)
    | DeclLoad fn ->
        (* [load "xxx.rab"] *)
        let fn = Filename.dirname base_fn ^ "/" ^ fn in
        load env fn
  in
  env, { d with data }

and load env fn =
  let decls, (_used_idents, _used_strings) = Lexer.read_file Parser.file fn in
  let env, decls =
    List.fold_left (fun (env, rev_decls) decl ->
        let env, decl = type_decl fn env decl in
        env, decl :: rev_decls) (env, []) decls
  in
  env, DeclLoad (fn, decls)
