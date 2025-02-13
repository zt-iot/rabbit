type substitute_error =
  | AccessError of string
  | PremissionError of string
  | UnintendedError of string

exception Error of substitute_error Location.located

(** [error ~loc err] raises the given runtime error. *)
let error ~loc err = Stdlib.raise (Error (Location.locate ~loc err))

(** Print error description. *)
let print_error err ppf =
  match err with
  | AccessError a -> Format.fprintf ppf "Channel access %s not granted" (a)
  | PremissionError a -> Format.fprintf ppf "Channel access %s not granted" (a)
  | UnintendedError a -> Format.fprintf ppf "Unintended Error (%s)" (a)

let rec expr_chan_sub e f t accesses = 
  let loc = e.Location.loc in
  match e.Location.data with
  | Syntax.Const _  -> e
  | Syntax.ExtConst s  -> e
  | Syntax.LocVariable (v, i)  -> e
  | Syntax.MetaVariable (v, i)  -> e
  | Syntax.MetaNewVariable (v, i)  -> e
  | Syntax.TopVariable (v, i)  -> e
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

let fact_chan_sub f fr t accesses =
  let loc = f.Location.loc in
  let f = 
   match f.Location.data with
   | Syntax.Fact (v, el) -> Syntax.Fact (v, (List.map (fun e -> expr_chan_sub e fr t accesses) el))
   | Syntax.GlobalFact (v, el) -> Syntax.GlobalFact (v, (List.map (fun e -> expr_chan_sub e fr t accesses) el))
   | Syntax.PathFact (l, id, el) -> Syntax.PathFact (expr_chan_sub l fr t accesses, id, (List.map (fun e -> expr_chan_sub e fr t accesses) el))
   | Syntax.ChannelFact (l, id, el) ->
      Syntax.ChannelFact (expr_chan_sub l fr t accesses, id, (List.map (fun e -> expr_chan_sub e fr t accesses) el))
   | Syntax.ResFact (v, el) -> Syntax.ResFact (v, (List.map (fun e -> expr_chan_sub e fr t accesses) el))

  | _ -> error ~loc (UnintendedError "")
 in Location.locate ~loc:loc f


let facts_chan_sub fl f t accesses = 
  List.map (fun ft -> fact_chan_sub ft f t accesses) fl

let rec cmd_chan_sub c f t accesses = 
  let loc = c.Location.loc in
  let c = 
    match c.Location.data with
    | Syntax.Sequence (c1, c2) -> Syntax.Sequence (cmd_chan_sub c1 f t accesses, cmd_chan_sub c2 f t accesses) 
    (* | Syntax.Wait (vl, fl, c) -> Syntax.Wait (vl, facts_chan_sub fl f t accesses, cmd_chan_sub c f t accesses) *)
    | Syntax.Let (v, e, c) -> Syntax.Let (v, expr_chan_sub e f t accesses, cmd_chan_sub c f t accesses)
    | Syntax.Assign (v, e) -> Syntax.Assign (v, expr_chan_sub e f t accesses)
    | Syntax.FCall (v, fn, el) -> Syntax.FCall (v, fn, List.map (fun e -> expr_chan_sub e f t accesses) el) 
    | Syntax.SCall (v, s, el) -> Syntax.SCall (v, s, List.map (fun e -> expr_chan_sub e f t accesses) el) 
    | Syntax.Case (cl) -> Syntax.Case 
      (List.map (fun (vl, fl, c) -> (vl, facts_chan_sub fl f t accesses, cmd_chan_sub c f t accesses)) cl)
    | Syntax.While (cl1, cl2) -> 
      Syntax.While (
        (List.map (fun (vl, fl, c) -> (vl, facts_chan_sub fl f t accesses, cmd_chan_sub c f t accesses)) cl1),
        (List.map (fun (vl, fl, c) -> (vl, facts_chan_sub fl f t accesses, cmd_chan_sub c f t accesses)) cl2))
    | Syntax.Event (fl) -> Syntax.Event (facts_chan_sub fl f t accesses)
    | Syntax.Skip -> Syntax.Skip
    | Syntax.Put (fl) -> Syntax.Put (facts_chan_sub fl f t accesses)
    | Syntax.Return e -> Syntax.Return (expr_chan_sub e f t accesses)
    in
  Location.locate ~loc:loc c
