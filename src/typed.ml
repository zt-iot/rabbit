type name = Name.t [@@deriving show]
type ident = Ident.t [@@deriving show]

type 'desc loc_env =
  { desc : 'desc
  ; loc : Location.t
  ; env : Env.t
  ; typ : Env.instantiated_ty option (* the type of "`desc" if it can have a type.  *)
  }

let pp_loc_env pp_desc fmt { desc; loc = _; env ; typ = _ } =
  Format.fprintf fmt "{ desc = %a; env = %a }"
    pp_desc desc
    Env.pp env

(* let show_loc_env show_desc { desc; loc = _; env } =
  Printf.sprintf "{ desc = %s; env = %s }"
    (show_desc desc)
    (Env.show env) *)


type expr = expr' loc_env [@@deriving show]

and expr' =
  | Ident of
      { id : ident
      ; desc : Env.desc
      ; param : expr option
      (** [param= Some _] iff [desc= Const true] *)
      }
  (** [id] or [id<e>].
      [id<e>] is only possible either for [id] of [Channel {param=true}] or [Const {param=true}] *)
  | Boolean of bool (** boolean, [true]/[false] *)
  | String of string (** string, ["hello"] *)
  | Integer of int (** integer, [42] *)
  | Float of string (** float, [4.12]. Store the string so we can correctly round later *)
  | Apply of ident * expr list  (** application, [f(e1,..,en)]   /  [e1 op e2] *)
  | Tuple of expr list (** tuple, [(e1,..,en)] *)
  | Unit
[@@deriving show]

let rec string_of_expr (e : expr) =
  match e.desc with
  | Ident { id; param= None; _ } -> Ident.to_string id
  | Ident { id; param= Some p; _ } -> Printf.sprintf "%s<%s>" (Ident.to_string id) (string_of_expr p)
  | Apply (f, es) -> Printf.sprintf "%s(%s)" (Ident.to_string f) (String.concat ", " @@ List.map string_of_expr es)
  | Tuple es -> Printf.sprintf "(%s)" @@ String.concat ", " @@ List.map string_of_expr es
  | String s -> Printf.sprintf "%S" s
  | Integer i -> string_of_int i
  | Float f -> f
  | Boolean b -> string_of_bool b
  | Unit -> "()"

type loop_mode =
  | In
  | Back
  | Out

type fact = fact' loc_env [@@deriving show]

and fact' =
  | Channel of
      { channel : expr
      ; name : name
      ; args : expr list
      }
  | Out of expr
  | In of expr
  | Plain of name * expr list
  | Eq of expr * expr
  | Neq of expr * expr
  | File of
      { path : expr
      ; contents : expr
      }
  | Global of string * expr list

type cmd = cmd' loc_env [@@deriving show]

and case =
  { fresh : ident list
  ; facts : fact list
  ; cmd : cmd
  } [@@deriving show]

and cmd' =
  | Skip
  | Sequence of cmd * cmd
  | Put of fact list
  | Let of ident * expr * cmd
  | Assign of ident option * expr
  | Case of case list
  | While of case list * case list
  | Event of fact list
  | Return of expr
  | New of ident * Env.instantiated_ty option * (name * expr list) option * cmd
  | Get of ident list * expr * name * cmd
  | Del of expr * name
[@@deriving show]

type chan_param = { channel : ident; param : unit option; typ : ident } [@@deriving show]

type chan_arg =
  { channel : ident
  ; parameter : expr option option
  ; typ : ident
  } [@@deriving show]

type pproc = pproc' Location.located [@@deriving show]

and pproc' =
  { id : ident
  ; parameter : expr option
  ; args : chan_arg list
  } [@@deriving show]

type proc =
  | Unbounded of pproc
  | Bounded of ident * pproc list
[@@deriving show]

type lemma = lemma' loc_env [@@deriving show]

and lemma' =
  | Plain of string
  | Reachability of
      { fresh : ident list
      ; facts : fact list
      }
  | Correspondence of
      { fresh : ident list
      ; from : fact
      ; to_ : fact
      }

type init_desc =
  | Value of expr
  | Value_with_param of ident * expr
  | Fresh
  | Fresh_with_param
[@@deriving show]




type decl = decl' loc_env [@@deriving show]

and decl' =
  | Equation of expr * expr
  | Syscall of
      { id : ident
      ; fun_sig : Env.syscall_member_fun_sig
      ; cmd : cmd
      }
  | Attack of
      { id : ident
      ; syscall : ident
      ; args : ident list
      ; cmd : cmd
      }
  (* This constructor is only kept for compatibilty with sem.ml *)
  | Type of
      { id : ident
      ; typclass : Input.rabbit_typ
      }
  | Allow of
      { process_typ : ident
      ; target_typs : ident list
      ; syscalls : ident list option
      }
  | AllowAttack of
      { process_typs : ident list
      ; attacks : ident list
      }
  | Init of
      { id : ident
      ; desc : init_desc
      }
  | ChannelDecl of
      { id : ident
      ; param : unit option
      ; typ : ident
      }
  | Process of
      { id : ident
      ; param : ident option
      ; args : chan_param list
      ; typ : ident
      ; files : (expr * ident * expr) list
      ; vars : (ident * Env.instantiated_ty option * expr) list
      ; funcs : (ident * Env.syscall_member_fun_sig * cmd) list
      ; main : cmd
      }
  | System of proc list * (Ident.t * lemma) list
  | Load of string * decl list
[@@deriving show]

module Subst = struct
  type t =
    { channels : (ident * ident) list
    ; parameters : (ident * expr) list
    }

  let rec expr (s : t) (e : expr) : expr =
    match e.desc with
    | Boolean _ | String _ | Integer _ | Float _ | Unit -> e
    | Tuple es -> { e with desc= Tuple (List.map (expr s) es) }
    | Apply (f, es) -> { e with desc= Apply (f, List.map (expr s) es) }
    | Ident ({ id; desc= ChannelDecl _; param; _ } as i) ->
        let id = Option.value ~default:id @@ List.assoc_opt id s.channels in
        let param = Option.map (expr s) param in
        { e with desc= Ident { i with id; param } }
    | Ident { id; desc= Var Param; param= None; _ } ->
        Option.value ~default:e @@ List.assoc_opt id s.parameters
    | Ident { id=_; desc= Var Param; param= Some _; _ } ->
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
      | New (id, ty_opt, neso, c) -> New (id, ty_opt, Option.map (fun (n, es) -> n, List.map (expr s) es) neso, cmd s c)
      | Get (ids, e, n, c) -> Get (ids, expr s e, n, cmd s c)
      | Del (e, n) -> Del (expr s e, n)
    in
    { c with desc }

  type instantiated_process =
    { id : ident
    ; typ : ident
    ; files : (expr * ident * expr) list
    ; vars : (ident * expr) list
    ; funcs : (ident * ident list * cmd) list
    ; main : cmd
    }

  let instantiate_process s ~id ~typ ~files ~vars ~funcs ~main =
    let id = Ident.local (fst id) in
    let files = List.map (fun (path, id, contents) -> expr s path, id, expr s contents) files in
    let vars = List.map (fun (id, def) -> (id, expr s def)) vars in
    let funcs = List.map (fun (fn, vars, c) -> (fn, vars, cmd s c)) funcs in
    let main = cmd s main in
    { id; typ; files; vars; funcs; main }

  let instantiate_pproc
      s
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
                    let _param =
                      match parameter with
                      | None -> None
                      | Some (Some pid) -> Some pid
                      | Some None -> assert false
                    in
                    pid, aid
                | { channel=pid; param= Some (); _ }, { channel=aid; parameter; typ=_ } ->
                    let _param =
                      match parameter with
                      | Some None -> ()
                      | None | Some (Some _) -> assert false
                    in
                    pid, aid
              ) chan_params chan_args
          in
          { parameters; channels }
        in
        let vars_simplified = List.map (fun (s, _, e) -> (s, e)) vars in
        let funcs_simplified = List.map (fun (f, param_desc, cmd) -> (f, Env.syscall_member_fun_desc_to_ident_list param_desc, cmd)) funcs in
        instantiate_process s ~id ~typ ~files ~vars:vars_simplified ~funcs:funcs_simplified ~main
    | None -> assert false
    | Some _ -> assert false

  let instantiate_proc decls = function
    | Unbounded { data= { parameter= Some _; _ }; _ } -> assert false
    | Unbounded ({ data= { parameter= None; _ }; _ } as pproc) ->
        [instantiate_pproc [] decls (pproc : pproc)]
    | Bounded (id, pprocs) ->
        let new_id = Ident.local (fst id) in
        let e = { desc= Ident { id= new_id
                              ; desc= Var Param
                              ; param= None }
                ; loc= Location.nowhere
                ; env= Env.add (Env.empty ()) new_id (Var Param)
                ; typ= None
                }
        in
        List.map (instantiate_pproc [id, e] decls) pprocs
end
