let rec expr_chan_sub e f t = 
  let loc = e.Location.loc in
  match e.Location.data with
  | Syntax.Const s  -> e
  | Syntax.ExtConst s  -> e
  | Syntax.Variable iv  -> e
  | Syntax.Boolean b  -> e
  | Syntax.String s  -> e
  | Syntax.Integer k  -> e
  | Syntax.Float s -> e
  | Syntax.Apply (o, el) -> Location.locate ~loc:loc (Syntax.Apply (o, List.map (fun e -> expr_chan_sub e f t) el))
  | Syntax.Tuple el -> Location.locate ~loc:loc (Syntax.Tuple (List.map (fun e -> expr_chan_sub e f t) el))
  | Syntax.Channel s -> if s = f then Location.locate ~loc:loc (Syntax.Channel t) else e



let rec stmt_chan_sub c f t =
  let loc = c.Location.loc in
  match c.Location.data with
  | Syntax.OpStmt a -> Location.locate ~loc:loc (Syntax.OpStmt (atomic_stmt_chan_sub a f t))
  | Syntax.EventStmt (a, el) -> Location.locate ~loc:loc (Syntax.EventStmt ((atomic_stmt_chan_sub a f t), el))
  
and atomic_stmt_chan_sub c f t = 
    let loc = c.Location.loc in
    match c.Location.data with
    | Syntax.Skip -> c
    | Syntax.Let (iv, e) -> Location.locate ~loc:loc (Syntax.Let (iv, expr_chan_sub e f t))
    | Syntax.Call (iv, f, args) -> Location.locate ~loc:loc (Syntax.Call (iv, f, List.map (fun e -> expr_chan_sub e f t) args))
    | Syntax.Instruction (iv, ins, args) -> Location.locate ~loc:loc (Syntax.Instruction (iv, ins, List.map (fun e -> expr_chan_sub e f t) args))
    | Syntax.If (e, c1, c2) -> 
      Location.locate ~loc:loc 
        (Syntax.If (expr_chan_sub e f t, 
                    List.map (fun e -> stmt_chan_sub e f t) c1,
                     List.map (fun e -> stmt_chan_sub e f t) c2))
    | Syntax.For (iv, i, j, c) -> 
      Location.locate ~loc:loc 
        (Syntax.For (iv, i, j, List.map (fun e -> stmt_chan_sub e f t) c))

