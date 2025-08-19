(* XXX not used at all *)
(* let print_type_class c =
   match c with
   | Input.CProc -> "Proc"
   | Input.CFsys -> "Fsys"
   | Input.CChan -> "Chan" *)
(*
let print_attack_class a =
   match a with
   | Input.CEaves -> "eavesdrop"
   | Input.CTamper -> "tamper"
   | Input.CDrop  -> "drop"
 *)

let pprint_iv (v, i, j, k) ppf =
   Format.fprintf ppf "%s[%d,%d,%d]" v i j k


let rec pprint_expr {Location.data=c; Location.loc=_loc} (ppf : Format.formatter) =
    match c with
    | Syntax.Const s -> Format.fprintf ppf "(Const %s)" s
    | Syntax.ExtConst s -> Format.fprintf ppf "(ExtConst %s)" s
    | Syntax.Variable iv -> pprint_iv iv ppf
    | Syntax.Boolean b -> Format.fprintf ppf "(Bool %b)" b
    | Syntax.String s -> Format.fprintf ppf "(String %s)" s
    | Syntax.Integer k -> Format.fprintf ppf "(Int %d)" k
    | Syntax.Float s -> Format.fprintf ppf "(Float %s)" s
    | Syntax.Apply (o, el) ->
      Format.fprintf ppf "%s(%t)" o
        (fun ppf ->
          Format.pp_print_list
            ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
            (fun ppf e -> pprint_expr e ppf) ppf el)
    | Syntax.Tuple el ->
      Format.fprintf ppf  "(%t)"
      (fun ppf ->
          Format.pp_print_list
            ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
            (fun ppf e -> pprint_expr e ppf) ppf el)
    | Syntax.Channel (s, _) -> Format.fprintf ppf "Ch %s" s
    | Syntax.FrVariable s -> Format.fprintf ppf "Fr %s" s

let pprint_event {Location.data=c; Location.loc=loc} ppf =
  match c with
  | Syntax.Event (eid, ivl) -> Format.fprintf ppf "%s(%t)" eid
    (fun ppf ->
      Format.pp_print_list
        ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
        (fun ppf e -> Format.fprintf ppf "%t" (pprint_expr e)) ppf ivl)

let rec pprint_stmt {Location.data=c; Location.loc=loc} ppf =
  match c with
  | Syntax.OpStmt a -> Format.fprintf ppf "@[<hov>%t@]@ " (pprint_atomic_stmt a)
  | Syntax.EventStmt (a, el) ->
    Format.fprintf ppf "%t[@[<hov>%t@]]@ " (pprint_atomic_stmt a)
      (fun ppf ->
          Format.pp_print_list
            ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
            (fun ppf e -> pprint_event e ppf) ppf el)

and pprint_atomic_stmt {Location.data=c; Location.loc=loc} ppf =
    match c with
    | Syntax.Skip -> Format.fprintf ppf "Skip"
    | Syntax.Let (iv, e) -> Format.fprintf ppf "let %t := %t" (pprint_iv iv) (pprint_expr e)
    | Syntax.Call (iv, f, args) -> Format.fprintf ppf "call %t := %s(@[<hov>%t@])" (pprint_iv iv) f
       (fun ppf ->
          Format.pp_print_list
            ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
            (fun ppf e -> pprint_expr e ppf) ppf args)
    | Syntax.Syscall (iv, ins, args) -> Format.fprintf ppf "syscall %t := %s(@[<hov>%t@])" (pprint_iv iv) (ins)
       (fun ppf ->
          Format.pp_print_list
            ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
            (fun ppf e -> pprint_expr e ppf) ppf args)
    | Syntax.If (e, c1, c2) -> Format.fprintf ppf "if %t @ then@ @[<hov>%t@]@ else@ @[<hov>%t@]@ " (pprint_expr e)
       (fun ppf ->
          Format.pp_print_list
            ~pp_sep:(fun ppf () -> Format.fprintf ppf ";@ ")
            (fun ppf e -> pprint_stmt e ppf) ppf c1)
      (fun ppf ->
          Format.pp_print_list
            ~pp_sep:(fun ppf () -> Format.fprintf ppf ";@ ")
            (fun ppf e -> pprint_stmt e ppf) ppf c2)

    | Syntax.For (iv, i, j, c) ->
      Format.fprintf ppf "for %t in range(%d,%d) do@ @[<hov>%t@]@ " (pprint_iv iv) i j
       (fun ppf ->
          Format.pp_print_list
            ~pp_sep:(fun ppf () -> Format.fprintf ppf ";@ ")
            (fun ppf e -> pprint_stmt e ppf) ppf c)

and pprint_stmts cs ppf =
   Format.pp_print_list
      ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
      (fun ppf e -> pprint_stmt e ppf) ppf cs

(* type access_class = CRead |  CWrite | CSend | CRecv
type attack_class = CEaves |  CTamper | CDrop
type chan_class = CDatagram | CStream
 *)
let pprint_context ctx ppf =

   let pprint_ext_const x ppf =
      Format.fprintf ppf "extern consts: @[<hov>%t@]"
         (fun ppf ->
          Format.pp_print_list
            ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
            (fun ppf c -> Format.fprintf ppf "%s" c) ppf x) in

   let pprint_ext_func x ppf =
      Format.fprintf ppf "extern funcs: @[<hov>%t@]"
         (fun ppf ->
          Format.pp_print_list
            ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
            (fun ppf (f, k) -> Format.fprintf ppf "%s.%d" f k ) ppf x) in

   let pprint_ty x ppf =
      Format.fprintf ppf "type vars: @[<hov>%t@]"
         (fun ppf ->
          Format.pp_print_list
            ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
            (fun ppf (f, k) -> Format.fprintf ppf "%s : %s" f (print_type_class k) ) ppf x) in

   let pprint_const x ppf =
      Format.fprintf ppf "consts: @[<hov>%t@]"
         (fun ppf ->
          Format.pp_print_list
            ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
            (fun ppf c -> Format.fprintf ppf "%s" c) ppf x) in

   let pprint_fsys x ppf =
      Format.fprintf ppf "file systems: @[<hov>%t@]"
         (fun ppf ->
          Format.pp_print_list
            ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
            (fun ppf (a, b, c) -> Format.fprintf ppf "{name:%s@ path:%s@ type:%s}" a b c) ppf x) in

   let pprint_chan x ppf =
      Format.fprintf ppf "channels: @[<hov>%t@]"
         (fun ppf ->
          Format.pp_print_list
            ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
            (fun ppf (a, c) -> Format.fprintf ppf "name:%s@ type:%s@ " a c) ppf x) in

   let pprint_proc x ppf =
      Format.fprintf ppf "processes: @[<hov>%t@]"
         (fun ppf ->
          Format.pp_print_list
            ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
            (fun ppf (x, args, ty, vars, funs) -> Format.fprintf ppf
               "@[<v>@[<h>name:%s@ chans:%t@ type:%s@]@ vars:@[<hov>%t@]@ funcs:@[<hov>%t@]@]" x
               (fun ppf ->
                Format.pp_print_list
                  ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
                  (fun ppf c -> Format.fprintf ppf "%s" c) ppf args)
               ty  (fun ppf ->
                   Format.pp_print_list
                  ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
                  (fun ppf c -> Format.fprintf ppf "%s" c) ppf vars)
               (fun ppf ->
                Format.pp_print_list
                  ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
                  (fun ppf (f, k) -> Format.fprintf ppf "%s:%d" f k) ppf funs)) ppf x) in

   let pprint_event x ppf =
      Format.fprintf ppf "events: @[<hov>%t@]"
         (fun ppf ->
          Format.pp_print_list
            ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
            (fun ppf (a, c) -> Format.fprintf ppf "%s:%d" a c) ppf x) in

   Format.fprintf ppf "@.   @[<v>@ %t@ %t@ %t@ %t@ %t@ %t@ %t@ %t@]"
   (pprint_ext_const ctx.Context.ctx_ext_const)
   (pprint_ext_func ctx.Context.ctx_ext_func)
   (pprint_ty ctx.Context.ctx_ty)
   (pprint_const ctx.Context.ctx_const)
   (pprint_fsys ctx.Context.ctx_fsys)
   (pprint_chan ctx.Context.ctx_ch)
   (pprint_proc (List.map Context.to_pair_ctx_proctmpl ctx.Context.ctx_proctmpl))
   (pprint_event ctx.Context.ctx_event)


let pprint_definition def ppf =

   let pprint_ext_eq x ppf =
      Format.fprintf ppf "extern eqns: @[<v>%t@]"
      (fun ppf ->
       Format.pp_print_list
         ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
         (fun ppf (idl, e1, e2) -> Format.fprintf ppf "@[<h>[%s]|%t=%t@]" (String.concat " " idl) (pprint_expr e1) (pprint_expr e2)) ppf x) in

   let pprint_const x ppf =
      Format.fprintf ppf "extern consts: @[<v>%t@]"
      (fun ppf ->
       Format.pp_print_list
         ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
         (fun ppf (id, e) -> Format.fprintf ppf "%s=%t" id (pprint_expr e)) ppf x) in

   let pprint_fsys x ppf =
      Format.fprintf ppf "file system: @[<v>%t@]"
      (fun ppf ->
       Format.pp_print_list
         ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
         (fun ppf (id, path, e) -> Format.fprintf ppf "%s:%s=%t" id path (pprint_expr e)) ppf x) in

   let pprint_proc x ppf =
      Format.fprintf ppf "%t"
      (fun ppf ->
       Format.pp_print_list
         ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
         (fun ppf (pid, el, fl, m) -> Format.fprintf ppf "process %s:@   @[<v>%t@ %t@ %t@ @]" pid
            (fun ppf ->
             Format.pp_print_list
               ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
            (fun ppf (id, e) -> Format.fprintf ppf "%s=%t" id (pprint_expr e)) ppf el)
            (fun ppf ->
             Format.pp_print_list
               ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
            (fun ppf (f, args, c, vid) -> Format.fprintf ppf "@[<v>%s(%s)=@   @[<v>%t@ return %t@]@]" f (String.concat " " args) (pprint_stmts c) (pprint_iv vid)) ppf fl)
            (pprint_stmts m)
            ) ppf x) in
   Format.fprintf ppf "@.   @[<v>@ %t@ %t@ %t@ %t@]"
   (pprint_ext_eq def.Context.def_ext_eq)
   (pprint_const def.Context.def_const)
   (pprint_fsys def.Context.def_fsys)
   (pprint_proc (List.map Context.to_pair_def_proctmpl def.Context.def_proctmpl))


let pprint_access_policy pol ppf =

   let pprint_pol_access x ppf =
      Format.fprintf ppf "accesses: @[<hov>%t@]"
      (fun ppf->
         Format.pp_print_list
         ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
         (fun ppf (s, t, a) -> Format.fprintf ppf "@[<hov>%s->%t:%s@]" s

            (fun ppf ->
          Format.pp_print_list
            ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
            (fun ppf t' -> Format.fprintf ppf "%s" t') ppf t)
             (a)) ppf x) in

   let pprint_pol_attack x ppf =
      Format.fprintf ppf "attacks: @[<v>%t@]"
      (fun ppf->
         Format.pp_print_list
         ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
         (fun ppf (t, a) -> Format.fprintf ppf "@[<hov>%s:%s@]" t (a)) ppf x) in

   Format.fprintf ppf "@.   @[<v>@ %t@ %t@]"
   (pprint_pol_access pol.Context.pol_access)
   (pprint_pol_attack pol.Context.pol_attack)

let pprint_system procs ppf =
      Format.pp_print_list
         ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
         (fun ppf (vl, fl, m, fsys) -> Format.fprintf ppf "file system: %s:@ %t@ %t@ %t@ " fsys
            (fun ppf ->
             Format.pp_print_list
               ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
            (fun ppf (id, e) -> Format.fprintf ppf "%s=%t" id (pprint_expr e)) ppf vl)

            (fun ppf ->
             Format.pp_print_list
               ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
            (fun ppf (f, args, c, vid) -> Format.fprintf ppf "@[<v>%s(%s)=@   @[<v>%t@ return %t@ @]@]" f (String.concat " " args) (pprint_stmts c) (pprint_iv vid)) ppf fl)

            (pprint_stmts m)

            ) ppf procs
