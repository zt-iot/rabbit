open Types
open Pitypes

(* Move the let declaration as deep as possible *)

exception Not_used
exception Unchanged

let rec cleanup_named_process occurs = function
    Nil -> Nil
  | NamedProcess(s, tl, p) ->
      NamedProcess(s, (if List.exists occurs tl then [] else tl), cleanup_named_process occurs p)
  | Par(p1,p2) -> Par(cleanup_named_process occurs p1, cleanup_named_process occurs p2)
  | Restr(n,(args,env),p,occ) -> Restr(n, (args, env), cleanup_named_process occurs p,occ)
  | Repl(p,occ) -> Repl(cleanup_named_process occurs p, occ)
  | Let(pat, t, p, q, occ) -> Let(pat, t, cleanup_named_process occurs p, cleanup_named_process occurs q, occ) 
  | Input(t, pat, p, occ) -> Input(t, pat, cleanup_named_process occurs p, occ)
  | Output(tc,t,p, occ) -> Output(tc, t, cleanup_named_process occurs p, occ)
  | Test(t,p,q,occ) -> Test(t, cleanup_named_process occurs p, cleanup_named_process occurs q,occ)
  | Event(t, (args, env), p, occ) -> Event(t, (args, env), cleanup_named_process occurs p, occ)
  | Insert(t, p, occ) -> Insert(t, cleanup_named_process occurs p, occ)
  | Get(pat, t, p, q, occ) -> Get(pat, t, cleanup_named_process occurs p, cleanup_named_process occurs q, occ)
  | Phase(n,p,occ) -> Phase(n, cleanup_named_process occurs p,occ)
  | LetFilter(bl, f, p, q, occ) -> LetFilter(bl, f, cleanup_named_process occurs p, cleanup_named_process occurs q, occ)
  | Barrier(n,str_op,p,occ) -> Barrier(n,str_op,cleanup_named_process occurs p,occ)
  | AnnBarrier _ ->
     Parsing_helper.internal_error "Barriers should not appear here (15)"

(* [push is_new put_ins occurs needed_by_new occurs_new_args p] adds an instruction 
   (assignment or new) to the process [p], pushing it as far as possible inside [p].
   The function [put_ins] adds the considered instruction, so that the returned
   process is equivalent to [put_ins p], but with the added instruction moved inside
   [p] if possible.

   - [is_new] is true when the added instruction is a "new", 
   false when it is a "let".
   - [occurs t] returns true when the term [t] contains the name 
   or variable defined by the added instruction.
   - [needed_by_new n] returns true when the name [n] needs to have 
   the variable defined by the added instruction as argument 
   (should be always false when the added instruction is a "new").
   - [occurs_new_args args] returns true when the variable defined 
   by the added instruction is mentioned in the arguments [args] 
   (should be always false when the added instruction is a "new").

   Raises [Unchanged] if the returned process would be [put_ins p]. *)
let push is_new put_ins occurs needed_by_new occurs_new_args proc =

  let rec occurs_pat = function
    | PatVar _ -> false
    | PatTuple(_,args) -> List.exists occurs_pat args
    | PatEqual t -> occurs t
  in

  let rec push_top proc = match proc with
    | Nil -> raise Not_used
    | Par(p1,p2) -> push_split p1 p2 (fun p1' p2' -> Par(p1',p2'))
    | Repl(p,occ) ->
	if is_new 
	then raise Unchanged
	else Repl(push p,occ)
    | Restr(n,args,p,occ) ->
        if needed_by_new n || occurs_new_args args
        then raise Unchanged
        else Restr(n,args,push p,occ)
    | Test(t,p1,p2,occ) ->
        if occurs t
        then raise Unchanged
        else push_split p1 p2 (fun p1' p2' -> Test(t,p1',p2',occ))
    | Input(c,pat,p,occ) ->
        if occurs c || occurs_pat pat
        then raise Unchanged
        else Input(c,pat,push p,occ)
    | Output(c,t,p,occ) ->
        if occurs c || occurs t
        then raise Unchanged
        else Output(c,t,push p,occ)
    | Let(pat,t,p1,p2,occ) ->
        if occurs t || occurs_pat pat
        then raise Unchanged
        else push_split p1 p2 (fun p1' p2' -> Let(pat,t,p1',p2',occ))
    | LetFilter(vars,(Pred(_,l) as fact),p1,p2,occ) ->
        if List.exists occurs l
        then raise Unchanged
        else push_split p1 p2 (fun p1' p2' -> LetFilter(vars,fact,p1',p2',occ))
    | Event(ev,args,p,occ) ->
        if occurs ev || occurs_new_args args
        then raise Unchanged
        else Event(ev,args,push p,occ)
    | Insert(t,p,occ) ->
        if occurs t
        then raise Unchanged
        else Insert(t,push p,occ)
    | Get(pat,t,p1,p2,occ) ->
        if occurs t || occurs_pat pat
        then raise Unchanged
        else push_split p1 p2 (fun p1' p2' -> Get(pat,t,p1',p2',occ))
    | Phase(n,p,occ) -> Phase(n,push p,occ)
    | Barrier(n,str_op,p,occ) -> Barrier(n,str_op,push p,occ)
    | NamedProcess(str,args,p) ->
	if List.exists occurs args then
          NamedProcess(str,[],push p)
	else
	  NamedProcess(str,args,push p)
    | AnnBarrier _ -> Parsing_helper.internal_error "[move_let.ml >> push_let] Unexpected process."

  and push p =
    try
      push_top p
    with Unchanged ->
      put_ins p
	  
  and push_split p1 p2 layer =
    let p1_op = try Some (push p1) with Not_used -> None in
    let p2_op = try Some (push p2) with Not_used -> None in

    match p1_op,p2_op with
      | None, None -> raise Not_used
      | Some p1', None -> layer p1' (cleanup_named_process occurs p2)
      | None, Some p2' -> layer (cleanup_named_process occurs p1) p2'
      | _ -> raise Unchanged

  in

  try 
    push_top proc
  with Not_used ->
    cleanup_named_process occurs proc

      
let move_process need_vars_in_names lets_never_fail proc =

  let moved_let = ref false in
  let moved_new = ref false in
  
  let rec move = function
    | Nil -> Nil
    | Par(p1,p2) -> Par(move p1, move p2)
    | Repl(p,occ) -> Repl(move p,occ)
    | Restr(n,args,p,occ) ->
	if !Param.move_new then
	  let p' = move p in
	  let put_new p = Restr(n,args,p,occ) in
	  try
	    let p'' = push true put_new (Terms.occurs_f n) (fun _ -> false) (fun _ -> false) p' in
	    moved_new := true;
	    p''
	  with Unchanged ->
	    put_new p'
	else
	  Restr(n,args,move p, occ)
    | Test(t,p1,p2,occ) -> Test(t,move p1,move p2,occ)
    | Input(c,pat,p,occ) -> Input(c,pat,move p,occ)
    | Output(c,t,p,occ) -> Output(c,t,move p,occ)
    | LetFilter(vars,fact,pthen,pelse,occ) -> LetFilter(vars,fact,move pthen,move pelse,occ)
    | Event(ev,args,p,occ) -> Event(ev,args,move p,occ)
    | Insert(t,p,occ) -> Insert(t,move p,occ)
    | Get(pat,t,pthen,pelse,occ) -> Get(pat,t,move pthen,move pelse,occ)
    | Phase(n,p,occ) -> Phase(n,move p,occ)
    | Barrier(n,str_op,p,occ) -> Barrier(n,str_op,move p,occ)
    | Let(PatVar v,t,pthen,Nil,occ) when !Param.move_let && (lets_never_fail || Terms.term_never_fail t) ->
	begin
          let pthen' = move pthen in
	  let put_let p = Let(PatVar v,t,p,Nil,occ) in
	  let needed_by_new n =
	    List.exists (fun (n',s,_) -> n == n' && v.vname.orig_name = s) need_vars_in_names
	  in
  	  let occurs_new_args (vars_op,_) =
	    match vars_op with
	    | None -> false
	    | Some vars -> List.memq v vars
	  in
          try
            let pthen'' = push false put_let (Terms.occurs_var v) needed_by_new occurs_new_args pthen' in
	    moved_let := true;
	    pthen''
          with Unchanged ->
	    put_let pthen'
	end
    | Let(pat,t,pthen,pelse,occ) -> Let(pat,t,move pthen,move pelse,occ)
    | NamedProcess(str,args,p) -> NamedProcess(str,args,move p)
    | AnnBarrier _ ->  Parsing_helper.internal_error "[move_let.ml >> move_let_process] Unexpected process."
  in

  let proc' = move proc in

  let moved =
    match !moved_new, !moved_let with
    | false, false -> raise Unchanged
    | false, true -> MLet
    | true, false -> MNew
    | true, true -> MBoth
  in
  (moved, proc')
  
let move lets_never_fail pi_state =
  if not (!Param.move_new || !Param.move_let) then pi_state else
  
  let need_vars_in_names =
    match pi_state.pi_need_vars_in_names with
    | Computed l -> l
    | _ -> Parsing_helper.internal_error "[move_let.ml >> move_let] need_vars_in_names should have been computed."
  in

  let move_desc p_desc =
    let (moved, p') = move_process need_vars_in_names lets_never_fail p_desc.proc in
    { p_desc with
      proc = p';
      display_num = None;
      construction = Move(moved, p_desc) }
  in

  try
    let process_query' =
      match pi_state.pi_process_query with
      | Equivalence _ -> Parsing_helper.internal_error "[move_let.ml >> move_let] Query should have been encoded."
      | SingleProcess(p, ql) -> SingleProcess(move_desc p, ql)
      | SingleProcessSingleQuery(p,q) -> SingleProcessSingleQuery(move_desc p, q)
    in
    { pi_state with pi_process_query = process_query' }
  with Unchanged ->
    pi_state
	
