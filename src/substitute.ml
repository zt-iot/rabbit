type error = ..
(* XXX unused
  | AccessError of string
  | PremissionError of string
*)

exception Error of error Location.located

(** [error ~loc err] raises the given runtime error. *)
let error ~loc err = Stdlib.raise (Error (Location.locate ~loc err))

(** Print error description. *)
let print_error err _ppf =
  match err with
  | _ -> assert false
(*
  | AccessError a -> Format.fprintf ppf "Channel access %s not granted" (a)
  | PremissionError a -> Format.fprintf ppf "Channel access %s not granted" (a)
*)

let rec expr_chan_sub e f t  =
  let loc = e.Location.loc in
  match e.Location.data with
  | Syntax.Channel (s, None) when s = f -> t
  | Syntax.Channel (_, None) -> e
  | Syntax.Channel (s, Some e) ->
      (* It seems [expr_param_chan_sub] handles the case [s = f] *)
      Location.locate ~loc:loc (Syntax.Channel (s, Some (expr_chan_sub e f t)))
  | Syntax.Apply (o, el) -> Location.locate ~loc:loc (Syntax.Apply (o, List.map (fun e -> expr_chan_sub e f t ) el))
  | Syntax.Tuple el -> Location.locate ~loc:loc (Syntax.Tuple (List.map (fun e -> expr_chan_sub e f t ) el))
  | Syntax.ParamConst (fid, e) -> Location.locate ~loc:loc (Syntax.ParamConst (fid, expr_chan_sub e f t) )
  | Syntax.Const _  -> e
  | Syntax.ExtConst _  -> e
  | Syntax.LocVariable _  -> e
  | Syntax.MetaVariable _ -> e
  | Syntax.MetaNewVariable _ -> e
  | Syntax.TopVariable _ -> e
  | Syntax.Boolean _ -> e
  | Syntax.String _ -> e
  | Syntax.Integer _ -> e
  | Syntax.Float _ -> e
  | _ -> e

let fact_chan_sub f fr t  =
  let loc = f.Location.loc in
  let f =
   match f.Location.data with
   | Syntax.Fact (v, el) -> Syntax.Fact (v, (List.map (fun e -> expr_chan_sub e fr t ) el))
   | Syntax.GlobalFact (v, el) -> Syntax.GlobalFact (v, (List.map (fun e -> expr_chan_sub e fr t ) el))
   (* | Syntax.PathFact (l, id, el) -> Syntax.PathFact (expr_chan_sub l fr t , id, (List.map (fun e -> expr_chan_sub e fr t ) el)) *)
   | Syntax.ChannelFact (l, id, el) ->
      Syntax.ChannelFact (expr_chan_sub l fr t , id, (List.map (fun e -> expr_chan_sub e fr t ) el))
   | Syntax.EqFact (e1, e2) -> Syntax.EqFact (expr_chan_sub e1 fr t, expr_chan_sub e2 fr t)
   | Syntax.NeqFact (e1, e2) -> Syntax.NeqFact (expr_chan_sub e1 fr t, expr_chan_sub e2 fr t)
   | Syntax.FileFact (e1, e2) -> Syntax.FileFact (expr_chan_sub e1 fr t, expr_chan_sub e2 fr t)
   | _ -> assert false
 in Location.locate ~loc:loc f


let facts_chan_sub fl f t  =
  List.map (fun ft -> fact_chan_sub ft f t ) fl

let rec cmd_chan_sub c f t  =
  let loc = c.Location.loc in
  let c =
    match c.Location.data with
    | Syntax.Sequence (c1, c2) -> Syntax.Sequence (cmd_chan_sub c1 f t , cmd_chan_sub c2 f t )
    (* | Syntax.Wait (vl, fl, c) -> Syntax.Wait (vl, facts_chan_sub fl f t , cmd_chan_sub c f t ) *)
    | Syntax.Let (v, e, c) -> Syntax.Let (v, expr_chan_sub e f t , cmd_chan_sub c f t )
    | Syntax.Assign (v, e) -> Syntax.Assign (v, expr_chan_sub e f t )
    | Syntax.FCall (v, fn, el) -> Syntax.FCall (v, fn, List.map (fun e -> expr_chan_sub e f t ) el)
    | Syntax.SCall (v, s, el) -> Syntax.SCall (v, s, List.map (fun e -> expr_chan_sub e f t ) el)
    | Syntax.Case (cl) -> Syntax.Case
      (List.map (fun (vl, fl, c) -> (vl, facts_chan_sub fl f t , cmd_chan_sub c f t )) cl)
    | Syntax.While (cl1, cl2) ->
      Syntax.While (
        (List.map (fun (vl, fl, c) -> (vl, facts_chan_sub fl f t , cmd_chan_sub c f t )) cl1),
        (List.map (fun (vl, fl, c) -> (vl, facts_chan_sub fl f t , cmd_chan_sub c f t )) cl2))
    | Syntax.Event (fl) -> Syntax.Event (facts_chan_sub fl f t )
    | Syntax.Skip -> Syntax.Skip
    | Syntax.Put (fl) -> Syntax.Put (facts_chan_sub fl f t )
    | Syntax.Return e -> Syntax.Return (expr_chan_sub e f t )
    | Syntax.New (v, fid_el_opt, c) ->
        Syntax.New (v, Option.map (fun (fid, el) ->
            fid, List.map (fun e -> expr_chan_sub e f t ) el) fid_el_opt, cmd_chan_sub c f t )
    | Syntax.Get (vl, id, fid, c) -> Syntax.Get (vl, expr_chan_sub id f t , fid, cmd_chan_sub c f t )
    | Syntax.Del (id, fid) -> Syntax.Del (expr_chan_sub id f t , fid)
  in
  Location.locate ~loc:loc c

let rec expr_param_chan_sub e f t =
   let loc = e.Location.loc in
   match e.Location.data with
   | Syntax.Channel (fid, Some e) when fid = f ->
       Location.locate ~loc:loc (Syntax.Channel (t, Some (expr_param_chan_sub e f t)))
   | Syntax.Channel (fid, Some e) ->
       Location.locate ~loc:loc (Syntax.Channel (fid, Some (expr_param_chan_sub e f t)))
   | Channel (_, None) -> e (* [expr_chan_sub] handles this *)
   | Syntax.Apply (o, el) -> Location.locate ~loc:loc (Syntax.Apply (o, List.map (fun e -> expr_param_chan_sub e f t ) el))
   | Syntax.Tuple el -> Location.locate ~loc:loc (Syntax.Tuple (List.map (fun e -> expr_param_chan_sub e f t ) el))
   | Syntax.ParamConst (fid, e) -> Location.locate ~loc:loc (Syntax.ParamConst (fid, expr_param_chan_sub e f t) )
   | Syntax.Const _ -> e
   | Syntax.ExtConst _ -> e
   | Syntax.LocVariable _ -> e
   | Syntax.MetaVariable _ -> e
   | Syntax.MetaNewVariable _ -> e
   | Syntax.TopVariable _ -> e
   | Syntax.Boolean _ -> e
   | Syntax.String _ -> e
   | Syntax.Integer _ -> e
   | Syntax.Float _s -> e
   | _ -> e

 let fact_param_chan_sub f fr t  =
   let loc = f.Location.loc in
   let f =
    match f.Location.data with
    | Syntax.Fact (v, el) -> Syntax.Fact (v, (List.map (fun e -> expr_param_chan_sub e fr t ) el))
    | Syntax.GlobalFact (v, el) -> Syntax.GlobalFact (v, (List.map (fun e -> expr_param_chan_sub e fr t ) el))
    (* | Syntax.PathFact (l, id, el) -> Syntax.PathFact (expr_param_chan_sub l fr t , id, (List.map (fun e -> expr_param_chan_sub e fr t ) el)) *)
    | Syntax.ChannelFact (l, id, el) ->
       Syntax.ChannelFact (expr_param_chan_sub l fr t , id, (List.map (fun e -> expr_param_chan_sub e fr t ) el))
    | Syntax.EqFact (e1, e2) -> Syntax.EqFact (expr_param_chan_sub e1 fr t, expr_param_chan_sub e2 fr t )
    | Syntax.NeqFact (e1, e2) -> Syntax.NeqFact (expr_param_chan_sub e1 fr t, expr_param_chan_sub e2 fr t )
    | Syntax.FileFact (e1, e2) -> Syntax.FileFact (expr_param_chan_sub e1 fr t, expr_param_chan_sub e2 fr t )
    | _ -> assert false
  in Location.locate ~loc:loc f


 let facts_param_chan_sub fl f t  =
   List.map (fun ft -> fact_param_chan_sub ft f t ) fl

 let rec cmd_param_chan_sub c f t  =
   let loc = c.Location.loc in
   let c =
     match c.Location.data with
     | Syntax.Sequence (c1, c2) -> Syntax.Sequence (cmd_param_chan_sub c1 f t , cmd_param_chan_sub c2 f t )
     (* | Syntax.Wait (vl, fl, c) -> Syntax.Wait (vl, facts_chan_sub fl f t , cmd_chan_sub c f t ) *)
     | Syntax.Let (v, e, c) -> Syntax.Let (v, expr_param_chan_sub e f t , cmd_param_chan_sub c f t )
     | Syntax.Assign (v, e) -> Syntax.Assign (v, expr_param_chan_sub e f t )
     | Syntax.FCall (v, fn, el) -> Syntax.FCall (v, fn, List.map (fun e -> expr_param_chan_sub e f t ) el)
     | Syntax.SCall (v, s, el) -> Syntax.SCall (v, s, List.map (fun e -> expr_param_chan_sub e f t ) el)
     | Syntax.Case (cl) -> Syntax.Case
       (List.map (fun (vl, fl, c) -> (vl, facts_param_chan_sub fl f t , cmd_param_chan_sub c f t )) cl)
     | Syntax.While (cl1, cl2) ->
       Syntax.While (
         (List.map (fun (vl, fl, c) -> (vl, facts_param_chan_sub fl f t , cmd_param_chan_sub c f t )) cl1),
         (List.map (fun (vl, fl, c) -> (vl, facts_param_chan_sub fl f t , cmd_param_chan_sub c f t )) cl2))
     | Syntax.Event (fl) -> Syntax.Event (facts_param_chan_sub fl f t )
     | Syntax.Skip -> Syntax.Skip
     | Syntax.Put (fl) -> Syntax.Put (facts_param_chan_sub fl f t )
     | Syntax.Return e -> Syntax.Return (expr_param_chan_sub e f t )
     | Syntax.New (v, fid_el_opt, c) ->
         Syntax.New (v,
                     Option.map (fun (fid, el) ->
                         fid, List.map (fun e -> expr_param_chan_sub e f t ) el) fid_el_opt,
                     cmd_param_chan_sub c f t )
     | Syntax.Get (vl, id, fid, c) -> Syntax.Get (vl, expr_param_chan_sub id f t , fid, cmd_param_chan_sub c f t )
     | Syntax.Del (id, fid) -> Syntax.Del (expr_param_chan_sub id f t , fid)
   in
   Location.locate ~loc:loc c


let rec expr_param e t =
  let loc = e.Location.loc in
  match e.Location.data with
  | Syntax.Param _ -> t
  | Syntax.Channel (fid, Some e) ->
      Location.locate ~loc:loc (Syntax.Channel (fid, Some (expr_param e t)))
  | Syntax.ParamConst (fid, e) -> Location.locate ~loc:loc (Syntax.ParamConst (fid, expr_param e t) )
  | Syntax.Apply (o, el) -> Location.locate ~loc:loc (Syntax.Apply (o, List.map (fun e -> expr_param e t) el))
  | Syntax.Tuple el -> Location.locate ~loc:loc (Syntax.Tuple (List.map (fun e -> expr_param e t) el))
  | _ -> e

let fact_param f t  =
  let loc = f.Location.loc in
  let f =
    match f.Location.data with
    | Syntax.Fact (v, el) -> Syntax.Fact (v, (List.map (fun e -> expr_param e t ) el))
    | Syntax.GlobalFact (v, el) -> Syntax.GlobalFact (v, (List.map (fun e -> expr_param e t ) el))
    (* | Syntax.PathFact (l, id, el) -> Syntax.PathFact (expr_param_chan_sub l fr t , id, (List.map (fun e -> expr_param_chan_sub e fr t ) el)) *)
    | Syntax.ChannelFact (l, id, el) ->
        Syntax.ChannelFact (expr_param l t , id, (List.map (fun e -> expr_param e t ) el))
    | Syntax.EqFact (e1, e2) -> Syntax.EqFact (expr_param e1 t, expr_param e2 t)
    | Syntax.NeqFact (e1, e2) -> Syntax.NeqFact (expr_param e1 t, expr_param e2 t)
    | Syntax.FileFact (e1, e2) -> Syntax.FileFact (expr_param e1 t, expr_param e2 t)

    | _ -> assert false
  in Location.locate ~loc:loc f


let facts_param fl t  =
  List.map (fun ft -> fact_param ft t ) fl

let rec cmd_param c t  =
  let loc = c.Location.loc in
  let c =
    match c.Location.data with
    | Syntax.Sequence (c1, c2) -> Syntax.Sequence (cmd_param c1 t , cmd_param c2 t )
    (* | Syntax.Wait (vl, fl, c) -> Syntax.Wait (vl, facts_chan_sub fl f t , cmd_chan_sub c f t ) *)
    | Syntax.Let (v, e, c) -> Syntax.Let (v, expr_param e t , cmd_param c t)
    | Syntax.Assign (v, e) -> Syntax.Assign (v, expr_param e t )
    | Syntax.FCall (v, fn, el) -> Syntax.FCall (v, fn, List.map (fun e -> expr_param e t ) el)
    | Syntax.SCall (v, s, el) -> Syntax.SCall (v, s, List.map (fun e -> expr_param e t ) el)
    | Syntax.Case (cl) -> Syntax.Case
      (List.map (fun (vl, fl, c) -> (vl, facts_param fl t , cmd_param c t )) cl)
    | Syntax.While (cl1, cl2) ->
      Syntax.While (
        (List.map (fun (vl, fl, c) -> (vl, facts_param fl t , cmd_param c t )) cl1),
        (List.map (fun (vl, fl, c) -> (vl, facts_param fl t , cmd_param c t )) cl2))
    | Syntax.Event (fl) -> Syntax.Event (facts_param fl t )
    | Syntax.Skip -> Syntax.Skip
    | Syntax.Put (fl) -> Syntax.Put (facts_param fl t )
    | Syntax.Return e -> Syntax.Return (expr_param e t )
    | Syntax.New (v, fid_el_opt, c) ->
        Syntax.New (v, Option.map (fun (fid, el) -> fid, List.map (fun e -> expr_param e t ) el) fid_el_opt, cmd_param c t )
    | Syntax.Get (vl, id, fid, c) -> Syntax.Get (vl, expr_param id t , fid, cmd_param c t )
    | Syntax.Del (id, fid) -> Syntax.Del (expr_param id t , fid)
  in
  Location.locate ~loc:loc c
