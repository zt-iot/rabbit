type name = Name.t
type ident = Ident.t

type 'desc loc_env =
  { desc : 'desc
  ; loc : Location.t
  ; env : Env.t
  }

type expr = expr' loc_env

and expr' =
  | Ident of
      { id : ident
      ; desc : Env.desc
      ; param : ident option
      }
  | Boolean of bool
  | String of string
  | Integer of int
  | Float of string
  | Apply of ident * expr list
  | Tuple of expr list
  | Unit

type loop_mode =
  | In
  | Back
  | Out

type fact = fact' loc_env

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

type cmd = cmd' loc_env

and case =
  { fresh : ident list
  ; facts : fact list
  ; cmd : cmd
  }

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
  | New of ident * (name * expr list) option * cmd
  | Get of ident list * expr * name * cmd
  | Del of expr * name

type chan_param = { channel : ident; param : unit option; typ : ident }

type chan_arg =
  { channel : ident
  ; parameter : ident option option
  ; typ : ident
  }

type pproc = pproc' Location.located

and pproc' =
  { id : ident
  ; parameter : unit option
  ; args : chan_arg list
  }

type proc =
  | Unbounded of pproc
  | Bounded of ident * pproc list

type lemma = lemma' loc_env

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

type decl = decl' loc_env

and decl' =
  | Function of
      { id : ident
      ; arity : int
      }
  | Equation of expr * expr
  | Syscall of
      { id : ident
      ; args : ident list
      ; cmd : cmd
      }
  | Attack of
      { id : ident
      ; syscall : ident
      ; args : ident list
      ; cmd : cmd
      }
  | Type of
      { id : ident
      ; typclass : Input.type_class
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
  | Channel of
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
      ; vars : (ident * expr) list
      ; funcs : (ident * ident list * cmd) list
      ; main : cmd
      }
  | System of proc list * (Ident.t * lemma) list
  | Load of string * decl list

module Subst = struct
  type t = (ident * ident) list

  let rec expr (s : t) (e : expr) : expr =
    match e.desc with
    | Boolean _ | String _ | Integer _ | Float _ | Unit -> e
    | Tuple es -> { e with desc= Tuple (List.map (expr s) es) }
    | Apply (f, es) -> { e with desc= Apply (f, List.map (expr s) es) }
    | Ident ({ id; desc= Channel (false, _chty); param= None } as i) ->
        (match List.assoc_opt id s with
         | None -> e
         | Some id' -> { e with desc= Ident { i with id= id' } }
        )
    | Ident ({ id; desc= Channel (true, _chty); param= Some pid } as i) ->
        (match List.assoc_opt id s with
         | None ->
             (match List.assoc_opt pid s with
              | Some pid' -> { e with desc= Ident { i with param= Some pid' } }
              | None -> e)
         | Some id' -> { e with desc= Ident { i with id = id' } }
        )
    | Ident { id=_; desc= Channel (true, _chty); param= None }
    | Ident { id=_; desc= Channel (false, _chty); param= Some _ } -> assert false
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

  let instantiate_pproc ?param (decls : decl list) (pproc : pproc) =
    let { id; parameter= param_arg; args= chan_args } = pproc.data in
    match
      List.find_opt (function
          | {desc= Process { id=id'; _ }; _} when id = id' -> true
          | _ -> false) decls
    with
    | Some {desc= Process { id=_; param= param_param; args= chan_params; typ; files; vars; funcs; main }; _} ->
        let s =
          (match param_param, param, param_arg with
           | None, None, None -> []
           | Some id, Some id', Some () ->
               [id, id']
           | _ -> assert false
          )
          @ List.map2 (fun chan_param chan_arg ->
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
        instantiate_process s ~id ~typ ~files ~vars ~funcs ~main
    | None -> assert false
    | Some _ -> assert false

  let instantiate_proc decls = function
    | Unbounded { data= { parameter= Some _; _ }; _ } -> assert false
    | Unbounded ({ data= { parameter= None; _ }; _ } as pproc) ->
        [instantiate_pproc decls (pproc : pproc)]
    | Bounded (id, pprocs) ->
        List.map (instantiate_pproc ~param:id decls) pprocs
end
