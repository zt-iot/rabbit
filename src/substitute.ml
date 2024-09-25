type substitute_error =
  | AccessError of string
  | PremissionError of string

exception Error of substitute_error Location.located

(** [error ~loc err] raises the given runtime error. *)
let error ~loc err = Stdlib.raise (Error (Location.locate ~loc err))

(** Print error description. *)
let print_error err ppf =
  match err with
  | AccessError a -> Format.fprintf ppf "Channel access %s not granted" (a)
  | PremissionError a -> Format.fprintf ppf "Channel access %s not granted" (a)

let rec expr_chan_sub e f t accesses = 
  let loc = e.Location.loc in
  match e.Location.data with
  | Syntax.Const _  -> e
  | Syntax.ExtConst s  -> e
  | Syntax.Variable iv  -> e
  | Syntax.Boolean b  -> e
  | Syntax.String s  -> e
  | Syntax.Integer k  -> e
  | Syntax.Float s -> e
  | Syntax.Apply (o, el) -> Location.locate ~loc:loc (Syntax.Apply (o, List.map (fun e -> expr_chan_sub e f t accesses) el))
  | Syntax.Tuple el -> Location.locate ~loc:loc (Syntax.Tuple (List.map (fun e -> expr_chan_sub e f t accesses) el))
  | Syntax.Channel (s, o) -> 
    if s = f then 
    begin
      (* if List.exists (fun y -> o = y) accesses then () else error ~loc (AccessError o) ; *)
      Location.locate ~loc:loc (Syntax.Channel (t, o)) 
    end else e 

  | _ -> e


let rec stmt_chan_sub c f t accesses =
  let loc = c.Location.loc in
  match c.Location.data with
  | Syntax.OpStmt a -> Location.locate ~loc:loc (Syntax.OpStmt (atomic_stmt_chan_sub a f t accesses))
  | Syntax.EventStmt (a, el) -> Location.locate ~loc:loc (Syntax.EventStmt ((atomic_stmt_chan_sub a f t accesses), el))
  
and atomic_stmt_chan_sub c f t accesses = 
    let loc = c.Location.loc in
    match c.Location.data with
    | Syntax.Skip -> c
    | Syntax.Let (iv, e) -> Location.locate ~loc:loc (Syntax.Let (iv, expr_chan_sub e f t accesses))
    | Syntax.Call (iv, fn, args) -> Location.locate ~loc:loc (Syntax.Call (iv, fn, List.map (fun e -> expr_chan_sub e f t accesses) args))
    | Syntax.Syscall (iv, ins, args) -> Location.locate ~loc:loc (Syntax.Syscall (iv, ins, List.map (fun (e, ty) -> expr_chan_sub e f t accesses, ty) args))
    | Syntax.If (e1, e2, c1, c2) -> 
      Location.locate ~loc:loc 
        (Syntax.If (expr_chan_sub e1 f t accesses, expr_chan_sub e2 f t accesses, 
                    List.map (fun e -> stmt_chan_sub e f t accesses) c1,
                     List.map (fun e -> stmt_chan_sub e f t accesses) c2))
    | Syntax.For (iv, i, j, c) -> 
      Location.locate ~loc:loc 
        (Syntax.For (iv, i, j, List.map (fun e -> stmt_chan_sub e f t accesses) c))
