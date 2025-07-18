open Typed

type t =
  { channels : (ident * (ident * expr option)) list
  ; parameters : (ident * expr) list
  }

let rec expr (s : t) (e : expr) : expr =
  match e.desc with
  | Boolean _ | String _ | Integer _ | Float _ | Unit -> e
  | Tuple es -> { e with desc= Tuple (List.map (expr s) es) }
  | Apply (f, es) -> { e with desc= Apply (f, List.map (expr s) es) }
  | Ident { id; desc= Channel (_, cty); param; _ } ->
      (match param, List.assoc_opt id s.channels with
       | _, None -> e (* weird *)
       | None, Some (id, None) ->
           (* ch => ch'  when  [ch => ch'] *)
           { e with desc= Ident { id; param= None; desc= Channel (false, cty) } }
       | Some param, Some (id, None) ->
           (* ch<p> => ch'<p>  when  [ch => ch'] *)
           { e with desc= Ident { id; param= Some (expr s param); desc= Channel (true, cty) } }
       | None, Some (id, Some param) ->
           (* ch => ch'<p>  when  [ch => ch'<p>] *)
           { e with desc= Ident { id; param= Some param; desc= Channel (true, cty) } }
       | Some _, Some (_id, Some _param) ->
           (* ch<p> => ??? when [ch => ch'<p>] *)
           assert false (* weird *))
  | Ident { id; desc= Param; param= None; _ } ->
      Option.value ~default:e @@ List.assoc_opt id s.parameters
  | Ident { id=_; desc= Param; param= Some _; _ } ->
      assert false
  | Ident _ -> e

let fact s (f : fact) : fact =
  let desc : fact' = match f.desc with
    | Channel { channel; name; args } ->
        let channel = expr s channel in
        let args = List.map (expr s) args in
        Channel { channel; name; args }
    | Out e -> Out (expr s e)
    | In e -> In (expr s e)
    | Plain (n, es) -> Plain (n, List.map (expr s) es)
    | Global (n, es) -> Global (n, List.map (expr s) es)
    | Eq (e1, e2) -> Eq (expr s e1, expr s e2)
    | Neq (e1, e2) -> Neq (expr s e1, expr s e2)
    | File { path; contents } -> File { path= expr s path; contents= expr s contents }
  in
  { f with desc }

let rec cmd s (c : cmd) : cmd =
  let case s (case : case) : case =
    { case with facts= List.map (fact s) case.facts; cmd= cmd s case.cmd }
  in
  let desc =
    match c.desc with
    | Skip -> Skip
    | Sequence (c1, c2) -> Sequence (cmd s c1, cmd s c2)
    | Put fs -> Put (List.map (fact s) fs)
    | Let (i, e, c) -> Let (i, expr s e, cmd s c)
    | Assign (ido, e) -> Assign (ido, expr s e)
    | Case cases -> Case (List.map (case s) cases)
    | While (cases, cases') -> While (List.map (case s) cases, List.map (case s) cases')
    | Event fs -> Event (List.map (fact s) fs)
    | Return e -> Return (expr s e)
    | New (id, neso, c) -> New (id, Option.map (fun (n, es) -> n, List.map (expr s) es) neso, cmd s c)
    | Get (ids, e, n, c) -> Get (ids, expr s e, n, cmd s c)
    | Del (e, n) -> Del (expr s e, n)
  in
  { c with desc }

type proc_group_id = Ident.t
type proc_id = Ident.t
type param_id = Ident.t

let param_id = Fun.id

type instantiated_proc =
  { id : proc_id
  ; param : param_id option
  ; args : chan_arg list
  ; typ : ident
  ; files : (expr * ident * expr) list
  ; vars : (ident * expr) list
  ; funcs : (ident * ident list * cmd) list
  ; main : cmd
  }

let instantiate_proc_aux s ~id ~param ~args ~typ ~files ~vars ~funcs ~main =
  let id = Ident.local (fst id) in
  let args =
    List.map (fun (chan_arg : chan_arg) ->
        { chan_arg with parameter = Option.map (Option.map (expr s)) chan_arg.parameter }) args
  in
  let files = List.map (fun (path, id, contents) -> expr s path, id, expr s contents) files in
  let vars = List.map (fun (id, def) -> (id, expr s def)) vars in
  let funcs = List.map (fun (fn, vars, c) -> (fn, vars, cmd s c)) funcs in
  let main = cmd s main in
  { id; param; args; typ; files; vars; funcs; main }

let instantiate_proc
    s
    ~param
    (decls : decl list)
    (pproc : pproc) (* id<parameter>(args) *) =
  let { id; parameter= param_arg; args= chan_args } = pproc.data in (* id<param_arg>(chan_args) *)
  (* instantiate [param_arg] and [chan_args] with [s] *)
  let s = { parameters= s(*XXX*); channels= [] } in
  let param_arg = Option.map (expr s) param_arg in
  let chan_args = List.map (fun (chan_arg : chan_arg) ->
      { chan_arg
        with parameter = Option.map (Option.map (expr s)) chan_arg.parameter
      }) chan_args
  in
  match
    List.find_opt (function
        | {desc= Process { id=id'; _ }; _} when id = id' -> true
        | _ -> false) decls
  with
  | Some {desc= Process { id=_
                        ; param= param_var
                        ; args= chan_params
                        ; typ
                        ; files
                        ; vars
                        ; funcs
                        ; main
                        };
          _ } ->
      (* Instantiate the process with [param_arg] and [chan_args] *)
      let s =
        let parameters =
          match param_var, param_arg with
          | None, None -> []
          | Some id, Some expr -> [id, expr]
          | _ -> assert false
        in
        let channels =
          List.map2 (fun chan_param chan_arg ->
              match chan_param, chan_arg with
              | { channel=pid; param= None; _ }, { channel=aid; parameter; typ=_ } ->
                  let param =
                    match parameter with
                    | None -> None
                    | Some (Some param) -> Some param
                    | Some None -> assert false
                  in
                  pid, (aid, param)
              | { channel=pid; param= Some (); _ }, { channel=aid; parameter; typ=_ } ->
                  let param =
                    match parameter with
                    | Some None -> None
                    | None | Some (Some _) -> assert false
                  in
                  pid, (aid, param)
            ) chan_params chan_args
        in
        { parameters; channels }
      in
      instantiate_proc_aux s ~id ~param ~args:chan_args ~typ ~files ~vars ~funcs ~main
  | None -> assert false
  | Some _ -> assert false

type instantiated_proc_group_desc =
  | Unbounded of instantiated_proc
  | Bounded of param_id * instantiated_proc list

type instantiated_proc_group =
  { id : proc_group_id
  ; desc : instantiated_proc_group_desc
  }

let instantiate_proc_group decls (proc_group : Typed.proc) =
  match proc_group with
  | Unbounded { data= { parameter= Some _; _ }; _ } -> assert false
  | Unbounded ({ data= { parameter= None; _ }; _ } as pproc) ->
      (* New process id *)
      { id= Ident.local ("PG_" ^ fst pproc.data.id)
      ; desc= Unbounded (instantiate_proc [] ~param:None decls (pproc : pproc)) }
  | Bounded (id, pprocs) ->
      let new_id = Ident.local (fst id) in
      let proc_id = Ident.prefix "PG_" new_id in
      let e = { desc= Ident { id= new_id
                            ; desc= Param
                            ; param= None }
              ; loc= Location.nowhere
              ; env= Env.add (Env.empty ()) new_id Param
              }
      in
      (* Use the instantiated parameter for the process id *)
      { id= proc_id
      ; desc= Bounded (new_id, List.map (instantiate_proc [id, e] ~param:(Some new_id) decls) pprocs) }
