type substitute_error =
  | AccessError of Input.access_class
  | ClassError of Input.chan_class

exception Error of substitute_error Location.located

(** [error ~loc err] raises the given runtime error. *)
let error ~loc err = Stdlib.raise (Error (Location.locate ~loc err))

(** Print error description. *)
let print_error err ppf =
  match err with
  | AccessError a -> Format.fprintf ppf "Channel access %s not granted" (Syntax.string_of_access_class a)
  | ClassError a -> Format.fprintf ppf "Channel class %s is expected" (Syntax.string_of_chan_class a)

let rec expr_chan_sub e f t accesses chan_class = 
  let loc = e.Location.loc in
  match e.Location.data with
  | Syntax.Const _  -> e
  | Syntax.ExtConst s  -> e
  | Syntax.Variable iv  -> e
  | Syntax.Boolean b  -> e
  | Syntax.String s  -> e
  | Syntax.Integer k  -> e
  | Syntax.Float s -> e
  | Syntax.Apply (o, el) -> Location.locate ~loc:loc (Syntax.Apply (o, List.map (fun e -> expr_chan_sub e f t accesses chan_class) el))
  | Syntax.Tuple el -> Location.locate ~loc:loc (Syntax.Tuple (List.map (fun e -> expr_chan_sub e f t accesses chan_class) el))
  | Syntax.Channel (s, l1, l2) -> 
    if s = f then 
    begin
      (List.fold_left (fun _ x -> if List.exists (fun y -> x = y) accesses then () else error ~loc (AccessError x)) () l1) ;
      (List.fold_left (fun _ x -> if List.exists (fun y -> x = y) [chan_class] then () else error ~loc (ClassError x)) () l2) ;
      Location.locate ~loc:loc (Syntax.Channel (s, l1, [chan_class])) 
    end else e 


let rec stmt_chan_sub c f t accesses chan_class =
  let loc = c.Location.loc in
  match c.Location.data with
  | Syntax.OpStmt a -> Location.locate ~loc:loc (Syntax.OpStmt (atomic_stmt_chan_sub a f t accesses chan_class))
  | Syntax.EventStmt (a, el) -> Location.locate ~loc:loc (Syntax.EventStmt ((atomic_stmt_chan_sub a f t accesses chan_class), el))
  
and atomic_stmt_chan_sub c f t accesses chan_class = 
    let loc = c.Location.loc in
    match c.Location.data with
    | Syntax.Skip -> c
    | Syntax.Let (iv, e) -> Location.locate ~loc:loc (Syntax.Let (iv, expr_chan_sub e f t accesses chan_class))
    | Syntax.Call (iv, f, args) -> Location.locate ~loc:loc (Syntax.Call (iv, f, List.map (fun e -> expr_chan_sub e f t accesses chan_class) args))
    | Syntax.Instruction (iv, ins, args) -> Location.locate ~loc:loc (Syntax.Instruction (iv, ins, List.map (fun e -> expr_chan_sub e f t accesses chan_class) args))
    | Syntax.If (e, c1, c2) -> 
      Location.locate ~loc:loc 
        (Syntax.If (expr_chan_sub e f t accesses chan_class, 
                    List.map (fun e -> stmt_chan_sub e f t accesses chan_class) c1,
                     List.map (fun e -> stmt_chan_sub e f t accesses chan_class) c2))
    | Syntax.For (iv, i, j, c) -> 
      Location.locate ~loc:loc 
        (Syntax.For (iv, i, j, List.map (fun e -> stmt_chan_sub e f t accesses chan_class) c))

let rec expr_const_sub e def = 
  let loc = e.Location.loc in
  match e.Location.data with
  | Syntax.Const s  -> snd (Context.def_get_const def s)
  | Syntax.ExtConst s  -> e
  | Syntax.Variable iv  -> e
  | Syntax.Boolean b  -> e
  | Syntax.String s  -> e
  | Syntax.Integer k  -> e
  | Syntax.Float s -> e
  | Syntax.Apply (o, el) -> Location.locate ~loc:loc (Syntax.Apply (o, List.map (fun e -> expr_const_sub e def) el))
  | Syntax.Tuple el -> Location.locate ~loc:loc (Syntax.Tuple (List.map (fun e -> expr_const_sub e def) el))
  | Syntax.Channel (s, l1, l2) -> e

let rec stmt_const_sub c def =
  let loc = c.Location.loc in
  match c.Location.data with
  | Syntax.OpStmt a -> Location.locate ~loc:loc (Syntax.OpStmt (atomic_stmt_const_sub a def))
  | Syntax.EventStmt (a, el) -> Location.locate ~loc:loc (Syntax.EventStmt ((atomic_stmt_const_sub a def), el))
  
and atomic_stmt_const_sub c def = 
    let loc = c.Location.loc in
    match c.Location.data with
    | Syntax.Skip -> c
    | Syntax.Let (iv, e) -> Location.locate ~loc:loc (Syntax.Let (iv, expr_const_sub e def))
    | Syntax.Call (iv, f, args) -> Location.locate ~loc:loc (Syntax.Call (iv, f, List.map (fun e -> expr_const_sub e def) args))
    | Syntax.Instruction (iv, ins, args) -> Location.locate ~loc:loc (Syntax.Instruction (iv, ins, List.map (fun e -> expr_const_sub e def) args))
    | Syntax.If (e, c1, c2) -> 
      Location.locate ~loc:loc 
        (Syntax.If (expr_const_sub e def, 
                    List.map (fun e -> stmt_const_sub e def) c1,
                     List.map (fun e -> stmt_const_sub e def) c2))
    | Syntax.For (iv, i, j, c) -> 
      Location.locate ~loc:loc 
        (Syntax.For (iv, i, j, List.map (fun e -> stmt_const_sub e def) c))

