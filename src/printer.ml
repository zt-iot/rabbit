let print_type_class c = 
   match c with 
   | Input.CProc -> "Proc"
   | Input.CFsys -> "Fsys" 
   | Input.CChan -> "Chan"

let print_chan_class c = 
   match c with 
   | Input.CDatagram -> "datagram"
   | Input.CStream -> "stream"

let print_access_class a = 
   match a with
   | Input.CRead -> "read"
   | Input.CWrite -> "write"
   | Input.CSend -> "send"
   | Input.CRecv -> "recv"

let print_attack_class a = 
   match a with
   | Input.CEaves -> "Eaves" 
   | Input.CTamper -> "Tamper"
   | Input.CDrop  -> "Drop"

let pprint_iv (v, i, j) ppf =
   Format.fprintf ppf "%s[%d,%d]" v i j
  

let string_of_ins i =   
  match i with 
  | Syntax.IRead -> "read" 
  | Syntax.IWrite -> "write" 
  | Syntax.IInvoke -> "invoke" 
  | Syntax.IRecv -> "recv" 
  | Syntax.ISend -> "send" 
  | Syntax.IOpen -> "open" 
  | Syntax.IClose -> "close" 
  | Syntax.ICloseConn -> "close_conn" 
  | Syntax.IConnect -> "connect" 
  | Syntax.IAccept -> "accept"

let pprint_ins i ppf = 
   Format.fprintf ppf "%s" (string_of_ins i)

let rec pprint_expr {Location.data=c; Location.loc=loc} ppf = 
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
    | Syntax.Channel s -> Format.fprintf ppf "Ch %s" s
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
    | Syntax.Instruction (iv, ins, args) -> Format.fprintf ppf "ins %t := %t(@[<hov>%t@])" (pprint_iv iv) (pprint_ins ins)
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

   let pprint_ext_const x ppx =
      Format.fprintf ppf "extern consts: @[<hov>%t@]"   
         (fun ppf -> 
          Format.pp_print_list 
            ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ") 
            (fun ppf c -> Format.fprintf ppf "%s" c) ppf x) in

   let pprint_ext_func x ppx =
      Format.fprintf ppf "extern funcs: @[<hov>%t@]"   
         (fun ppf -> 
          Format.pp_print_list 
            ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ") 
            (fun ppf (f, k) -> Format.fprintf ppf "%s.%d" f k ) ppf x) in

   let pprint_ty x ppx =
      Format.fprintf ppf "type vars: @[<hov>%t@]"   
         (fun ppf -> 
          Format.pp_print_list 
            ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ") 
            (fun ppf (f, k) -> Format.fprintf ppf "%s : %s" f (print_type_class k) ) ppf x) in

   let pprint_const x ppx =
      Format.fprintf ppf "consts: @[<hov>%t@]"   
         (fun ppf -> 
          Format.pp_print_list 
            ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ") 
            (fun ppf c -> Format.fprintf ppf "%s" c) ppf x) in

   let pprint_fsys x ppx =
      Format.fprintf ppf "file systems: @[<hov>%t@]"   
         (fun ppf -> 
          Format.pp_print_list 
            ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ") 
            (fun ppf (a, b, c) -> Format.fprintf ppf "{name:%s@ path:%s@ type:%s}" a b c) ppf x) in

   let pprint_chan x ppx =
      Format.fprintf ppf "channels: @[<hov>%t@]"   
         (fun ppf -> 
          Format.pp_print_list 
            ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ") 
            (fun ppf (a, b, c) -> Format.fprintf ppf "name:%s@ method:%s@ type:%s@ " a (print_chan_class b) c) ppf x) in

   let pprint_proc x ppx =
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

   let pprint_event x ppx =
      Format.fprintf ppf "events: @[<hov>%t@]"   
         (fun ppf -> 
          Format.pp_print_list 
            ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ") 
            (fun ppf (a, c) -> Format.fprintf ppf "%s:%d" a c) ppf x) in

   Format.fprintf ppf "@.   @[<v>@ %t@ %t@ %t@ %t@ %t@ %t@ %t@ %t@]"
   (pprint_ext_const ctx.Loader.ctx_ext_const) 
   (pprint_ext_func ctx.Loader.ctx_ext_func) 
   (pprint_ty ctx.Loader.ctx_ty) 
   (pprint_const ctx.Loader.ctx_const) 
   (pprint_fsys ctx.Loader.ctx_fsys) 
   (pprint_chan ctx.Loader.ctx_chan)    
   (pprint_proc ctx.Loader.ctx_proc) 
   (pprint_event ctx.Loader.ctx_event) 


let pprint_definition def ppf =

   let pprint_ext_eq x ppx =
      Format.fprintf ppf "extern eqns: @[<v>%t@]"   
      (fun ppf -> 
       Format.pp_print_list 
         ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ") 
         (fun ppf (idl, e1, e2) -> Format.fprintf ppf "@[<h>[%s]|%t=%t@]" (String.concat " " idl) (pprint_expr e1) (pprint_expr e2)) ppf x) in

   let pprint_const x ppx =
      Format.fprintf ppf "extern consts: @[<v>%t@]"   
      (fun ppf -> 
       Format.pp_print_list 
         ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ") 
         (fun ppf (id, e) -> Format.fprintf ppf "%s=%t" id (pprint_expr e)) ppf x) in

   let pprint_fsys x ppx =
      Format.fprintf ppf "file system: @[<v>%t@]"   
      (fun ppf -> 
       Format.pp_print_list 
         ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ") 
         (fun ppf (id, path, e) -> Format.fprintf ppf "%s:%s=%t" id path (pprint_expr e)) ppf x) in

   let pprint_proc x ppx =
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
   (pprint_ext_eq def.Loader.def_ext_eq) 
   (pprint_const def.Loader.def_const) 
   (pprint_fsys def.Loader.def_fsys) 
   (pprint_proc def.Loader.def_proc)  


let pprint_access_policy pol ppf =

   let pprint_pol_access x ppx =
      Format.fprintf ppf "accesses: @[<hov>%t@]"
      (fun ppf->   
         Format.pp_print_list 
         ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ") 
         (fun ppf (s, t, a) -> Format.fprintf ppf "@[<hov>%s->%s:%s@]" s t (print_access_class a)) ppf x) in


   let pprint_pol_attack x ppx =
      Format.fprintf ppf "attacks: @[<v>%t@]"   
      (fun ppf->   
         Format.pp_print_list 
         ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ") 
         (fun ppf (t, a) -> Format.fprintf ppf "@[<hov>%s:%s@]" t (print_attack_class a)) ppf x) in

   Format.fprintf ppf "@.   @[<v>@ %t@ %t@]"
   (pprint_pol_access pol.Loader.pol_access) 
   (pprint_pol_attack pol.Loader.pol_attack)

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
