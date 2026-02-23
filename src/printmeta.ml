open Metadata

let trans_loc (loc : Location.t) =
  match loc with
  | Nowhere -> None
  | Location (begin_pos, _) ->
      let begin_line = begin_pos.Lexing.pos_lnum in
      let filename = begin_pos.Lexing.pos_fname in
      if String.length filename != 0
      then Some { filename = Some filename; begin_line = Some begin_line }
      else Some { filename = None; begin_line = Some begin_line }
;;

let fact_type (f : Spthy.fact) =
  match f with
  | Channel _ -> Some Channel
  | Global _ -> Some Global
  | Eq _ -> Some Eq
  | Neq _ -> Some Neq
  | File _ -> Some File
  | Fresh _ -> Some Fresh
  | _ -> None
;;

(* move equality and inequality facts from precondition to tags *)
let facts_of_edge (e : Sem.edge) =
  let pre_eq_neq, pre_others =
    List.partition
      (function
        | ({ desc = Eq _ | Neq _; _ } : Sem.fact) -> true
        | _ -> false)
      e.pre
  in
  pre_others, e.tag @ pre_eq_neq, e.post
;;

let fresh_of_fact (f : Sem.fact) =
  match f.desc with
  | Fresh (name, _) -> Some name
  | _ -> None
;;

let collect_vars_with_param (f : Sem.fact) =
  let rec collect_from_expr (expr : Typed.expr) =
    match expr.desc with
    | Ident { id; desc = _; param = Some _ } -> [ Ident.to_string (id :> Ident.t) ]
    | Apply (_, es) | Tuple es -> List.concat_map collect_from_expr es
    | _ -> []
  in
  match f.desc with
  | Channel { channel; name = _; args } ->
      collect_from_expr channel @ List.concat_map collect_from_expr args
  | Plain { pid = _; name = _; args } -> List.concat_map collect_from_expr args
  | Eq (e1, e2) | Neq (e1, e2) -> collect_from_expr e1 @ collect_from_expr e2
  | File { pid = _; path; contents } ->
      collect_from_expr path @ collect_from_expr contents
  | Global (_, args) -> List.concat_map collect_from_expr args
  | Structure { pid = _; name = _; address; args } ->
      collect_from_expr address @ List.concat_map collect_from_expr args
  | Access { pid = _; channel; syscall = _ } -> collect_from_expr channel
  | _ -> []
;;

let info_of_edge (edge : Sem.edge) =
  let name = Ident.to_string (edge.id :> Ident.t) in
  let fact_to_meta (f : Sem.fact) =
    let compiled = Spthy.compile_fact f in
    let f' = Spthy.fact' compiled.result in
    let loc = trans_loc f.loc in
    let ty = fact_type compiled.result in
    let fresh = fresh_of_fact f in
    let paramvars = collect_vars_with_param f in
    { name = f'.name; loc; ty; fresh; paramvars }
  in
  let pre, tag, post = facts_of_edge edge in
  let pre = List.map fact_to_meta pre in
  let label = List.map fact_to_meta tag in
  let post = List.map fact_to_meta post in
  { name; pre; label; post; attack = edge.attack }
;;

let info_of_const
      ((var, _) as id : Ident.t)
      (init_desc : Typed.init_desc)
      (loc : Location.t)
  =
  let name = Ident.to_string (Ident.prefix "Const_" id) in
  let location = trans_loc loc in
  let pre =
    match init_desc with
    | Fresh | Fresh_with_param ->
        [ { name = "Fr"
          ; loc = location
          ; ty = Some ConstFresh
          ; fresh = Some var
          ; paramvars = []
          }
        ]
    | Value _ | Value_with_param (_, _) -> []
  in
  let label =
    [ { name = "Init"; loc = location; ty = None; fresh = None; paramvars = [] }
    ; { name = "!Const"; loc = location; ty = None; fresh = None; paramvars = [] }
    ]
  in
  let post =
    [ { name = "!Const"; loc = location; ty = None; fresh = None; paramvars = [] } ]
  in
  { name; pre; label; post; attack = false }
;;

let info_of_proc_group_init (proc_group_id : Subst.proc_group_id) ((var, _) : Ident.t) loc
  =
  let name = Ident.to_string (Ident.prefix "Init_" (proc_group_id :> Ident.t)) in
  let location = trans_loc loc in
  let pre =
    [ { name = "Fr"; loc = location; ty = Some Fresh; fresh = Some var; paramvars = [] } ]
  in
  let label =
    [ { name = "Init"; loc = location; ty = None; fresh = None; paramvars = [] } ]
  in
  let post =
    [ { name = "Inited_proc_group"
      ; loc = location
      ; ty = None
      ; fresh = None
      ; paramvars = []
      }
    ]
  in
  { name; pre; label; post; attack = false }
;;

let print_rule_info (sem : Sem.t) =
  let rule_info_edges =
    List.concat_map
      (fun (proc_group_id, group_desc) ->
         match group_desc with
         | Sem.Unbounded m -> List.map info_of_edge m.edges
         | Sem.Bounded (param, ms) ->
             info_of_proc_group_init proc_group_id (param.data :> Ident.t) param.loc
             :: List.concat_map (fun m -> List.map info_of_edge m.Sem.edges) ms)
      sem.proc_groups
  in
  let rule_info_consts =
    List.map
      (fun { Location.data = id, init_desc; loc } -> info_of_const id init_desc loc)
      sem.constants
  in
  rule_info_consts @ rule_info_edges
;;

let output_metadata filename (sem : Sem.t) =
  let metadata = print_rule_info sem in
  Sexplib.Sexp.save_hum filename (sexp_of_t metadata)
;;
